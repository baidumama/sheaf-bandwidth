"""
B-3-pre: Hodge separating risk test
=========================================

Test whether the Hodge spectrum (low-eigenmodes of the 0-Laplacian on a
Delaunay triangulation of MRI-style k-space trajectories) is "separating"
in the sampling-theorem sense, i.e. whether the sampling matrix
A[V_s, K] = [v_k(i_n)]  has full column rank with reasonable
conditioning under realistic subsampling configurations.

Pipeline:
  1) Generate trajectory point clouds in [-k_max, k_max]^3
        (a) 3D stack-of-spirals (MRI realistic)
        (b) 3D radial spokes (MRI realistic)
        (c) Random uniform in ball (baseline)
        (d) Cartesian undersampled grid (baseline)
        (e) Sparkling-like blue noise (Lloyd-relaxed in ball, MRI advanced)
  2) Build a 3D Delaunay simplicial complex K(V).
  3) Build the weighted 0-Laplacian L_0 = D - W with edge weight
        w_{ij} = 1 / |k_i - k_j|^2 (B-2 v0.1 §3.4 default).
  4) Compute K=50 smallest eigenpairs (mu_k, v_k) via scipy.sparse eigsh.
  5) For several V_s subsets, evaluate the sampling matrix A:
        - numerical column rank
        - condition number
        - smallest singular value sigma_K and ratio sigma_K/sigma_0
        - full singular spectrum
  6) Save figures (3D point cloud, eigenvalue curve, eigenvector samples,
     sigma decay).

Outputs:
  ./figures/B3pre_*.png
  ./B3pre_results.json
"""

from __future__ import annotations

import json
import os
import sys
import time
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from mpl_toolkits.mplot3d import Axes3D  # noqa: F401  (registers 3D projection)
from scipy.sparse import csr_matrix, lil_matrix
from scipy.sparse.linalg import eigsh
from scipy.spatial import Delaunay


# -----------------------------------------------------------------------------
# Globals / paths
# -----------------------------------------------------------------------------

SEED = 20260506
K_MAX = 1.0          # normalized k-space radius
N_TARGET = 300       # rough target |V|
K_EIG = 50           # number of low eigenmodes
RNG = np.random.default_rng(SEED)

ROOT = Path(__file__).resolve().parent
FIGS = ROOT / "figures"
FIGS.mkdir(parents=True, exist_ok=True)

EIG_TOL = 1e-9   # treat eigenvalues smaller than this as zero (constant mode)


# -----------------------------------------------------------------------------
# Trajectory generators
# -----------------------------------------------------------------------------

def _crop_to_ball(pts: np.ndarray, r: float) -> np.ndarray:
    """Keep only points strictly inside the ball of radius r."""
    norms = np.linalg.norm(pts, axis=1)
    return pts[norms <= r * 0.999]


def traj_stack_of_spirals(n_target: int = N_TARGET, k_max: float = K_MAX,
                          n_stacks: int = 9, n_turns: float = 4.0) -> np.ndarray:
    """3D stack-of-spirals: in-plane Archimedean spiral, stacked in kz."""
    n_per_stack = max(1, n_target // n_stacks)
    kz_levels = np.linspace(-k_max * 0.9, k_max * 0.9, n_stacks)
    pts = []
    for kz in kz_levels:
        # in-plane radius depends on kz (stay inside ball)
        r_max = np.sqrt(max(k_max ** 2 - kz ** 2, 1e-6))
        t = np.linspace(0.0, 1.0, n_per_stack)
        r = r_max * t
        theta = 2 * np.pi * n_turns * t
        kx = r * np.cos(theta)
        ky = r * np.sin(theta)
        stack = np.column_stack([kx, ky, np.full_like(kx, kz)])
        pts.append(stack)
    pts = np.vstack(pts)
    pts = _crop_to_ball(pts, k_max)
    return pts


def traj_radial(n_target: int = N_TARGET, k_max: float = K_MAX,
                n_spokes: int = 30, n_per_spoke: int | None = None) -> np.ndarray:
    """3D radial spokes through the origin."""
    if n_per_spoke is None:
        n_per_spoke = max(2, n_target // n_spokes)
    # spread spokes via golden-section quasi-uniform on the sphere
    phi_g = (1 + np.sqrt(5)) / 2
    pts = []
    for i in range(n_spokes):
        # Fibonacci spiral on sphere
        z = 1 - 2 * (i + 0.5) / n_spokes
        r_xy = np.sqrt(max(0.0, 1 - z * z))
        theta = 2 * np.pi * i / phi_g
        d = np.array([r_xy * np.cos(theta), r_xy * np.sin(theta), z])
        d /= np.linalg.norm(d)
        # sample symmetrically along [-k_max, k_max] times d
        ts = np.linspace(-k_max * 0.99, k_max * 0.99, n_per_spoke)
        spoke = ts[:, None] * d[None, :]
        pts.append(spoke)
    pts = np.vstack(pts)
    # de-dup near origin (every spoke would sample 0)
    norms = np.linalg.norm(pts, axis=1)
    keep_mask = norms > 1e-3
    keep = pts[keep_mask]
    keep = np.vstack([keep, np.zeros((1, 3))])  # one origin sample
    return _crop_to_ball(keep, k_max)


def traj_random_uniform(n_target: int = N_TARGET, k_max: float = K_MAX) -> np.ndarray:
    """Uniform random points inside the ball (baseline)."""
    rng = np.random.default_rng(SEED + 1)
    pts = []
    while len(pts) < n_target:
        batch = rng.uniform(-k_max, k_max, size=(n_target, 3))
        norms = np.linalg.norm(batch, axis=1)
        ok = batch[norms <= k_max * 0.999]
        pts.extend(ok.tolist())
    pts = np.array(pts[:n_target])
    return pts


def traj_cartesian(n_target: int = N_TARGET, k_max: float = K_MAX,
                   undersample: int = 1) -> np.ndarray:
    """Cartesian grid inside the ball (baseline)."""
    side = int(np.ceil(n_target ** (1 / 3))) + 2
    axis = np.linspace(-k_max * 0.95, k_max * 0.95, side)
    grid = np.array(np.meshgrid(axis, axis, axis, indexing="ij"))
    pts = grid.reshape(3, -1).T
    pts = _crop_to_ball(pts, k_max)
    if undersample > 1:
        pts = pts[::undersample]
    return pts


def traj_sparkling(n_target: int = N_TARGET, k_max: float = K_MAX,
                   n_iter: int = 12) -> np.ndarray:
    """Sparkling-like blue noise via Lloyd relaxation in the ball.

    Approximates the 'Voronoi-pushed' property of SPARKLING without the
    full physical/MR constraints (slew rate, gradient strength).  This is
    sufficient as a 'realistic blue noise' baseline for the separating test.
    """
    rng = np.random.default_rng(SEED + 2)
    # initial random samples
    pts = traj_random_uniform(n_target, k_max).copy()
    for _ in range(n_iter):
        # Voronoi tessellation (use Delaunay for neighbour structure)
        try:
            tri = Delaunay(pts, qhull_options="QJ")
        except Exception:
            return pts
        # for each point, gather neighbours and move toward mean of neighbour mid-points
        idx_ptr, indices = tri.vertex_neighbor_vertices
        new_pts = pts.copy()
        for i in range(len(pts)):
            nbrs = indices[idx_ptr[i]:idx_ptr[i + 1]]
            if len(nbrs) == 0:
                continue
            # repel slightly: target = mean of neighbours, then push outward 5%
            mean_nbr = pts[nbrs].mean(axis=0)
            direction = pts[i] - mean_nbr
            new_pts[i] = pts[i] + 0.15 * direction + 0.02 * rng.standard_normal(3)
            # project back to ball
            r = np.linalg.norm(new_pts[i])
            if r > k_max * 0.99:
                new_pts[i] *= k_max * 0.99 / r
        pts = new_pts
    return pts


TRAJ_GENERATORS = {
    "spiral":     traj_stack_of_spirals,
    "radial":     traj_radial,
    "random":     traj_random_uniform,
    "cartesian":  traj_cartesian,
    "sparkling":  traj_sparkling,
}


# -----------------------------------------------------------------------------
# 0-Laplacian construction
# -----------------------------------------------------------------------------

def build_edges_from_delaunay(V: np.ndarray) -> np.ndarray:
    """Return unique undirected edges (Mx2 int array) of the 3D Delaunay
    tetrahedralization of V."""
    tri = Delaunay(V, qhull_options="QJ")  # joggle for robustness
    tetras = tri.simplices  # (N_T, 4)
    # each tetra has 6 edges
    e1 = tetras[:, [0, 0, 0, 1, 1, 2]]
    e2 = tetras[:, [1, 2, 3, 2, 3, 3]]
    edges = np.stack([e1, e2], axis=-1).reshape(-1, 2)
    edges = np.sort(edges, axis=1)  # canonicalize
    edges = np.unique(edges, axis=0)
    return edges


def build_laplacian(V: np.ndarray, edges: np.ndarray) -> csr_matrix:
    """L_0 = D - W with w_{ij} = 1 / |k_i - k_j|^2.  Sparse."""
    N = V.shape[0]
    diffs = V[edges[:, 0]] - V[edges[:, 1]]
    dist2 = np.sum(diffs ** 2, axis=1)
    # guard against accidental near-zero distance
    dist2 = np.maximum(dist2, 1e-12)
    w = 1.0 / dist2
    rows = np.concatenate([edges[:, 0], edges[:, 1]])
    cols = np.concatenate([edges[:, 1], edges[:, 0]])
    data = np.concatenate([w, w])
    W = csr_matrix((data, (rows, cols)), shape=(N, N))
    deg = np.asarray(W.sum(axis=1)).ravel()
    D = csr_matrix((deg, (np.arange(N), np.arange(N))), shape=(N, N))
    L = D - W
    # symmetrize numerically
    L = (L + L.T) * 0.5
    return L.tocsr()


def low_spectrum(L: csr_matrix, k: int = K_EIG) -> tuple[np.ndarray, np.ndarray]:
    """Return (mu, V_eig) of the k smallest eigenpairs of L.  Sorted ascending."""
    N = L.shape[0]
    k = min(k, N - 2)
    # shift-invert near 0 to get smallest eigenvalues; sigma=1e-6 to avoid singularity
    try:
        mu, U = eigsh(L, k=k, sigma=1e-6, which="LM")
    except Exception:
        # fallback: ARPACK SM (slower / less stable)
        mu, U = eigsh(L, k=k, which="SM")
    order = np.argsort(mu)
    return mu[order], U[:, order]


# -----------------------------------------------------------------------------
# Subsampling configurations
# -----------------------------------------------------------------------------

def make_subsample_configs(V: np.ndarray, K: int, k_max: float) -> dict:
    """Return a dict { name: indices into V } of test configurations."""
    N = V.shape[0]
    rng = np.random.default_rng(SEED + 3)
    configs: dict[str, np.ndarray] = {}

    # 1) full sample
    configs["full"] = np.arange(N)

    # 2) inner-k center crop  (|k| <= k_max/2)
    norms = np.linalg.norm(V, axis=1)
    inner = np.where(norms <= k_max * 0.5)[0]
    if len(inner) >= K:  # only meaningful if at least K samples inside
        configs["inner_half"] = inner

    # 3) random subsampling at three rates
    for rate, label in [(0.5, "rand_50pct"),
                        (0.25, "rand_25pct"),
                        (0.125, "rand_12.5pct")]:
        m = int(max(K + 5, np.round(rate * N)))
        m = min(m, N)
        idx = rng.choice(N, size=m, replace=False)
        configs[label] = np.sort(idx)

    # 4) "tight" config: |V_s| ~= K (the hardest possible)
    m_tight = min(K + 2, N)
    idx_tight = rng.choice(N, size=m_tight, replace=False)
    configs["tight_K_plus_2"] = np.sort(idx_tight)

    # 5) every-other-spoke / stride 2
    configs["stride2"] = np.arange(0, N, 2)

    return configs


# -----------------------------------------------------------------------------
# Sampling matrix metrics
# -----------------------------------------------------------------------------

def sampling_metrics(U: np.ndarray, V_s_idx: np.ndarray, K: int) -> dict:
    """Compute rank/cond/sigma metrics of A = U[V_s, :K]."""
    A = U[V_s_idx][:, :K]   # (|V_s|, K)
    metrics = {
        "n_samples": int(A.shape[0]),
        "K": int(K),
    }
    # SVD
    s = np.linalg.svd(A, compute_uv=False)
    metrics["sigma_max"] = float(s[0]) if len(s) else 0.0
    metrics["sigma_min"] = float(s[-1]) if len(s) else 0.0
    if metrics["sigma_max"] > 0 and len(s):
        metrics["sigma_ratio"] = float(s[-1] / s[0])
    else:
        metrics["sigma_ratio"] = 0.0
    # rank with tolerance from numpy default  max(M,N)*eps*sigma_max
    metrics["rank"] = int(np.linalg.matrix_rank(A))
    metrics["full_rank"] = bool(metrics["rank"] == K)
    # cond
    if metrics["sigma_min"] > 0:
        metrics["cond"] = float(metrics["sigma_max"] / metrics["sigma_min"])
    else:
        metrics["cond"] = float("inf")
    metrics["sv"] = s.tolist()  # full spectrum (small, K-length)
    return metrics


# -----------------------------------------------------------------------------
# Plotting
# -----------------------------------------------------------------------------

def plot_point_cloud(V: np.ndarray, name: str, out: Path) -> None:
    fig = plt.figure(figsize=(5, 5))
    ax = fig.add_subplot(111, projection="3d")
    ax.scatter(V[:, 0], V[:, 1], V[:, 2], s=4, alpha=0.7)
    ax.set_title(f"{name}  (N={V.shape[0]})")
    ax.set_xlabel("kx"); ax.set_ylabel("ky"); ax.set_zlabel("kz")
    fig.tight_layout()
    fig.savefig(out, dpi=120)
    plt.close(fig)


def plot_eig_curve(mu: np.ndarray, name: str, out: Path) -> None:
    fig, ax = plt.subplots(figsize=(6, 4))
    ax.semilogy(np.arange(len(mu)), np.maximum(mu, 1e-12), "o-")
    ax.set_xlabel("k (eigen index)")
    ax.set_ylabel(r"$\mu_k$  (log scale)")
    ax.set_title(f"{name}: low spectrum of L_0")
    ax.grid(True, alpha=0.3)
    fig.tight_layout()
    fig.savefig(out, dpi=120)
    plt.close(fig)


def plot_eigvecs(V: np.ndarray, U: np.ndarray, name: str, out: Path,
                 picks=(1, 5, 10, 20)) -> None:
    fig = plt.figure(figsize=(12, 3))
    for j, k in enumerate(picks):
        ax = fig.add_subplot(1, len(picks), j + 1, projection="3d")
        col = U[:, k]
        scat = ax.scatter(V[:, 0], V[:, 1], V[:, 2], c=col, cmap="coolwarm", s=6)
        ax.set_title(f"{name}: v_{k}")
        ax.set_xticks([]); ax.set_yticks([]); ax.set_zticks([])
        fig.colorbar(scat, ax=ax, shrink=0.6)
    fig.tight_layout()
    fig.savefig(out, dpi=120)
    plt.close(fig)


def plot_singular_decay(metrics_per_config: dict, name: str, out: Path,
                        K: int) -> None:
    fig, ax = plt.subplots(figsize=(6.5, 4))
    for label, m in metrics_per_config.items():
        sv = np.array(m["sv"])
        sv_norm = sv / (sv[0] if sv[0] > 0 else 1.0)
        ax.semilogy(np.arange(len(sv)), np.maximum(sv_norm, 1e-16),
                    "o-", label=label, markersize=3)
    ax.set_xlabel("singular value index")
    ax.set_ylabel(r"$\sigma_i / \sigma_0$")
    ax.set_title(f"{name}: sampling matrix singular spectrum (K={K})")
    ax.legend(fontsize=8)
    ax.grid(True, alpha=0.3)
    fig.tight_layout()
    fig.savefig(out, dpi=120)
    plt.close(fig)


# -----------------------------------------------------------------------------
# Main driver
# -----------------------------------------------------------------------------

def run_one_traj(name: str, V: np.ndarray, K: int = K_EIG) -> dict:
    """Run the full pipeline on one trajectory and return a results dict."""
    t0 = time.time()
    out = {"trajectory": name, "N": int(V.shape[0])}

    if V.shape[0] < K + 5:
        out["error"] = f"too few points (N={V.shape[0]} < K+5={K+5})"
        return out

    # de-duplicate exact duplicates that some generators might produce
    V_unique, _ = np.unique(np.round(V, 8), axis=0, return_index=True)
    if V_unique.shape[0] != V.shape[0]:
        # use the de-duplicated set
        V = V_unique
        out["N"] = int(V.shape[0])

    # 1. Delaunay edges
    try:
        edges = build_edges_from_delaunay(V)
    except Exception as e:
        out["error"] = f"Delaunay failed: {e}"
        return out
    out["n_edges"] = int(edges.shape[0])

    # 2. Laplacian
    L = build_laplacian(V, edges)

    # 3. Low spectrum
    mu, U = low_spectrum(L, k=K)
    out["mu"] = mu.tolist()
    # number of zero eigenvalues -> number of connected components
    out["n_zero_eigs"] = int(np.sum(mu < EIG_TOL))

    # 4. Subsample configs
    configs = make_subsample_configs(V, K=K, k_max=K_MAX)
    cfg_metrics = {}
    for cname, idx in configs.items():
        cfg_metrics[cname] = sampling_metrics(U, idx, K)
    out["configs"] = cfg_metrics

    # 5. plots
    plot_point_cloud(V, name, FIGS / f"B3pre_pc_{name}.png")
    plot_eig_curve(mu, name, FIGS / f"B3pre_eig_{name}.png")
    plot_eigvecs(V, U, name, FIGS / f"B3pre_eigvecs_{name}.png")
    plot_singular_decay(cfg_metrics, name,
                        FIGS / f"B3pre_sv_{name}.png", K=K)

    out["elapsed_sec"] = round(time.time() - t0, 2)
    return out


def main() -> None:
    print("=" * 60)
    print(f"B-3-pre: Hodge separating test  (seed={SEED}, N~{N_TARGET}, K={K_EIG})")
    print("=" * 60)

    all_results = {}
    for name, gen in TRAJ_GENERATORS.items():
        print(f"\n---- {name} ----")
        try:
            V = gen()
            print(f"  generated N={V.shape[0]} points")
            res = run_one_traj(name, V, K=K_EIG)
        except Exception as e:
            res = {"trajectory": name, "error": str(e)}
            print(f"  ERROR: {e}")
        all_results[name] = res
        if "error" not in res:
            for cname, m in res["configs"].items():
                print(f"    {cname:18s}  M={m['n_samples']:4d}  rank={m['rank']:3d}/{K_EIG}  "
                      f"cond={m['cond']:.3e}  sigma_K/sigma_0={m['sigma_ratio']:.3e}")

    out_path = ROOT / "B3pre_results.json"
    with out_path.open("w") as f:
        json.dump(all_results, f, indent=2)
    print(f"\nSaved results to {out_path}")
    print(f"Figures in {FIGS}")


if __name__ == "__main__":
    main()
