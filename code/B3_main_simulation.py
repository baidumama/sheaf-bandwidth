"""
B-3 main simulation: scaffold (skeleton, not full implementation)
==================================================================

Goal
----
Take the geometric sanity-check pipeline of B-3-pre (see
``B3pre_hodge_separating.py``) and add real signal + noise + reconstruction,
plus the two falsifiable tests that emerged from the upstream work:

  - **Seam 8 reverse-correlation test** (b3pre §5.1, A-1-pre §5.2):
    on the *same* V, jointly compute (i) quadrature error E_q and
    (ii) sampling conditioning cond(A) ; check whether the rank ordering
    of trajectories is reversed between the two scores
    (Spearman correlation between E_q and cond^{-1}).

  - **A-1-pre §5.2 numerical-consistency test**:
    sigma_min(A)/sigma_max(A) must equal the V_B(V) frame-bound ratio on
    V_s.  Any discrepancy exposes a hidden assumption in the equivalence
    proof (A-1-pre §2.1).

Scope of THIS file (skeleton, ~ 2 hours of work)
------------------------------------------------
- Module layout in a single file (each section starts with ``# ===``).
- All public function signatures (typed) + docstrings with the exact
  contract the downstream caller needs.
- Two trajectories implemented end-to-end (cartesian, random) by reusing
  ``B3pre_hodge_separating.py`` generators.
- One reference reconstruction (CG-on-V_B, Tikhonov) implemented.
- Baseline reconstructions (SPARKLING / Wasserstein blue noise / CS-MRI)
  are *placeholders* with a precise input/output contract — to be filled
  in later.
- Seam-8 driver and A-1-pre driver implemented as runnable functions.
- Three minimal pytest-style unit tests at the bottom (``test_*``) that
  exercise the data flow without relying on the full sweep.
- One smoke ``main()`` that runs cartesian + random at small N and prints
  a JSON-shaped summary.  No figures (those go to ``B3_main_v0_2``).

What this file does NOT do
--------------------------
- Full 5 trajectory x N in {1000, 5000, 20000} x SNR sweep — that is the
  v0.2 driver after the skeleton is reviewed.
- Real SPARKLING / Wasserstein-blue-noise / CS-MRI reconstructions —
  placeholders only, see ``baseline_*`` functions.
- Plotting / figure I/O — left to the v0.2 driver to keep skeleton clean.

Reuse note
----------
The geometric backbone (Delaunay edges, weighted L_0, low spectrum,
sampling-matrix metrics, V_s configs) is *re-imported* from
``B3pre_hodge_separating.py`` rather than re-written.  See the
``# === 0. reuse from B3pre`` section below.
"""

from __future__ import annotations

import json
import sys
import time
from dataclasses import dataclass, field, asdict
from pathlib import Path
from typing import Callable, Optional

import numpy as np
from scipy.sparse import csr_matrix
from scipy.sparse.linalg import LinearOperator, cg


# =====================================================================
# 0. reuse from B3pre_hodge_separating.py
# =====================================================================
# The b3pre script lives next to this file.  We reuse its primitives
# instead of re-implementing them, so the geometric backbone stays
# identical between the two experiments.

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))

# Note: imports are deferred to runtime in the unit tests below so that
# the pure data structures and contracts in this file remain importable
# even if scipy is unavailable.
try:
    import B3pre_hodge_separating as b3pre  # type: ignore
    _HAS_B3PRE = True
except Exception as _exc:  # pragma: no cover - defensive
    b3pre = None  # type: ignore
    _HAS_B3PRE = False
    _B3PRE_IMPORT_ERR = repr(_exc)


# =====================================================================
# 1. data_gen — Shepp-Logan phantom + complex signal + Rician noise
# =====================================================================
# Skeleton implementations.  The phantom is a cheap 3D Gaussian-mixture
# stand-in for Shepp-Logan; full SL3D requires a separate generator
# (TODO: pull from sigpy.mri.sim.shepp_logan or write an analytic 3D
# version with overlapping ellipsoids).  For the skeleton pass it is
# enough that the test signal has structured low-frequency content and
# nontrivial high-frequency tail — that is exactly what a Gaussian
# mixture provides.

@dataclass
class Phantom3D:
    """Continuous 3D image rho(x).  Sampled in real space on demand."""
    centers: np.ndarray              # (n_blob, 3)
    sigmas: np.ndarray               # (n_blob,)
    intensities: np.ndarray          # (n_blob,)  -- complex allowed

    def evaluate_at(self, x: np.ndarray) -> np.ndarray:
        """Evaluate rho(x) at points x of shape (..., 3).

        Returns complex array of matching shape.  This is the *image*
        domain object; we sample its analytic Fourier transform at the
        k-space points (see ``analytic_kspace``) — never IFFT.
        """
        out = np.zeros(x.shape[:-1], dtype=np.complex128)
        for c, s, a in zip(self.centers, self.sigmas, self.intensities):
            d2 = np.sum((x - c) ** 2, axis=-1)
            out += a * np.exp(-d2 / (2 * s * s))
        return out

    def analytic_kspace(self, k: np.ndarray) -> np.ndarray:
        """Closed-form S(k) = FT[rho](k).  k of shape (..., 3).

        FT of a Gaussian a*exp(-|x-c|^2 / 2 sigma^2) is
            a * (2 pi sigma^2)^{3/2} * exp(-2 pi^2 sigma^2 |k|^2)
              * exp(-2 pi i k . c)
        Using the unitary-FT convention S(k)=int rho(x) e^{-2 pi i k.x} dx.
        """
        out = np.zeros(k.shape[:-1], dtype=np.complex128)
        for c, s, a in zip(self.centers, self.sigmas, self.intensities):
            phase = np.exp(-2j * np.pi * (k @ c))
            mag = a * (2 * np.pi * s * s) ** 1.5 * \
                np.exp(-2 * (np.pi * s) ** 2 * np.sum(k * k, axis=-1))
            out += mag * phase
        return out


def make_shepplogan_like(seed: int = 0) -> Phantom3D:
    """Cheap stand-in: 8 Gaussian blobs in [-0.4, 0.4]^3."""
    rng = np.random.default_rng(seed)
    n = 8
    centers = rng.uniform(-0.3, 0.3, size=(n, 3))
    sigmas = rng.uniform(0.05, 0.15, size=n)
    intensities = rng.uniform(0.4, 1.2, size=n).astype(np.complex128)
    # add a small imaginary part to test complex pipeline
    intensities = intensities + 1j * rng.uniform(-0.1, 0.1, size=n)
    return Phantom3D(centers=centers, sigmas=sigmas, intensities=intensities)


def add_rician_noise(S: np.ndarray, sigma: float, rng: np.random.Generator) -> np.ndarray:
    """Add complex Gaussian noise with per-component std ``sigma``.

    Strictly speaking Rician arises when one takes |S + n_r + i n_i|; in
    k-space MRI we keep the *complex* signal + complex Gaussian (which is
    the upstream of Rician magnitude in image space).  The downstream
    magnitude image |IFFT(S+n)| then has Rician distribution.  We expose
    the complex noisy signal here — image-domain Rician is computed in
    ``evaluation.image_metrics`` if needed.
    """
    n = sigma * (rng.standard_normal(S.shape) + 1j * rng.standard_normal(S.shape)) / np.sqrt(2)
    return S + n


def snr_to_sigma(S: np.ndarray, snr_db: float) -> float:
    """Pick noise sigma so that 20 log10(||S||/||n||) = snr_db."""
    p_signal = float(np.mean(np.abs(S) ** 2))
    p_noise = p_signal / (10 ** (snr_db / 10))
    return float(np.sqrt(p_noise))


# =====================================================================
# 2. trajectory — five MRI k-space trajectories
# =====================================================================
# For cartesian + random + the sparkling/spiral/radial generators we
# delegate to b3pre.  The contract: each generator returns float64
# (N, 3) array of unique points inside the unit ball.

def make_trajectory(name: str, n_target: int = 300) -> np.ndarray:
    """Dispatch to a named trajectory generator and return points (N, 3).

    Supported names: 'spiral', 'radial', 'random', 'cartesian',
    'sparkling'.  All delegate to ``B3pre_hodge_separating``.
    """
    if not _HAS_B3PRE:
        raise RuntimeError(f"B3pre import failed: {_B3PRE_IMPORT_ERR}")
    gens = b3pre.TRAJ_GENERATORS
    if name not in gens:
        raise KeyError(f"unknown trajectory {name!r}; choices: {sorted(gens)}")
    pts = gens[name](n_target=n_target)
    # de-dup like b3pre.run_one_traj does
    pts_u, _ = np.unique(np.round(pts, 8), axis=0, return_index=True)
    return pts_u


# =====================================================================
# 3. discretization — Delaunay -> L_0 -> low spectrum (re-export)
# =====================================================================
# Just thin wrappers so call sites do not reach into b3pre directly.

def build_complex_and_spectrum(
    V: np.ndarray,
    K_eig: int = 50,
    edge_weight: str = "inv_sq_dist",
) -> tuple[np.ndarray, csr_matrix, np.ndarray, np.ndarray]:
    """Run b3pre's Delaunay/L_0/low-spectrum pipeline on V.

    Parameters
    ----------
    V : (N, 3) float
    K_eig : number of low eigenpairs to extract
    edge_weight : currently 'inv_sq_dist' (b3pre default).  Future
        variants (1/|k|, gaussian, adaptive) are TODO — they would be
        injected by replacing ``b3pre.build_laplacian``.

    Returns
    -------
    edges : (E, 2) int
    L0    : (N, N) sparse symmetric PSD
    mu    : (K_eig,) ascending eigenvalues
    U     : (N, K_eig) eigenvectors (columns)
    """
    if edge_weight != "inv_sq_dist":
        # TODO: dispatch to alternative edge-weight builders for the
        # B-2 v0.2 §3.4 sensitivity sweep.
        raise NotImplementedError(f"edge_weight={edge_weight!r} not yet wired")
    edges = b3pre.build_edges_from_delaunay(V)
    L0 = b3pre.build_laplacian(V, edges)
    mu, U = b3pre.low_spectrum(L0, k=K_eig)
    return edges, L0, mu, U


def sampling_matrix(U: np.ndarray, V_s_idx: np.ndarray, K: int) -> np.ndarray:
    """A = U[V_s, :K] in C^{M x K}  (real here unless U is complex)."""
    return U[V_s_idx][:, :K]


# =====================================================================
# 4. reconstruction — CG-on-V_B + baseline placeholders
# =====================================================================

@dataclass
class ReconResult:
    name: str
    coef: np.ndarray                 # (K,) reconstructed V_B coefficients
    image_full: np.ndarray           # (N,) reconstructed values on V (W^0 c)
    n_iter: int = 0
    converged: bool = False
    info: dict = field(default_factory=dict)


def cg_on_VB(
    A: np.ndarray,
    y: np.ndarray,
    K: int,
    tikhonov: float = 0.0,
    rtol: float = 1e-8,
    max_iter: int = 200,
) -> ReconResult:
    """Solve (A^* A + lam I) c = A^* y by conjugate gradients.

    A : (M, K) complex.  y : (M,) complex.  Returns coefficients in V_B
    and the implied full-grid signal U[:, :K] @ c.

    Implicit regularisation is the V_B projection itself (we never leave
    the K-dim subspace).  Tikhonov is an additional explicit term.
    """
    A = np.asarray(A)
    y = np.asarray(y)

    AHA = A.conj().T @ A + tikhonov * np.eye(K, dtype=A.dtype)
    AHy = A.conj().T @ y

    # scipy.sparse.linalg.cg expects real symmetric positive-definite by
    # default.  For complex Hermitian PSD systems we run it on the
    # complex problem with a small wrapper that exposes matvec.
    def _matvec(v: np.ndarray) -> np.ndarray:
        return AHA @ v

    op = LinearOperator((K, K), matvec=_matvec, dtype=AHA.dtype)
    # cg supports complex Hermitian; rtol kw is the modern signature.
    try:
        c, info = cg(op, AHy, rtol=rtol, maxiter=max_iter)
    except TypeError:
        # scipy < 1.12 still uses tol=
        c, info = cg(op, AHy, tol=rtol, maxiter=max_iter)

    return ReconResult(
        name="cg_on_VB",
        coef=c,
        image_full=np.zeros(0),       # filled in by caller using U
        n_iter=int(max_iter),         # cg does not expose true count
        converged=(info == 0),
        info={"cg_info": int(info), "tikhonov": float(tikhonov)},
    )


# ---- baseline placeholders ------------------------------------------
# Each baseline takes (V, V_s_idx, y, K, U) and returns a ReconResult.
# Filling these in is left for future work.  The contract here is fixed
# so the evaluation harness can call them uniformly.

def baseline_sparkling(
    V: np.ndarray, V_s_idx: np.ndarray, y: np.ndarray, K: int, U: np.ndarray
) -> ReconResult:
    """SPARKLING reconstruction (Lazarus et al. 2019, MRM).

    TODO: implement using density-compensated NUFFT + L1-wavelet
    regularisation (the published recipe).  For now we return a
    placeholder that signals "not implemented" so the evaluation
    harness logs it as N/A rather than crashing.

    A reasonable first cut would be:
        1) Voronoi area density compensation w_i for V_s,
        2) gridded NUFFT to a Cartesian grid via finufft,
        3) FISTA with Daubechies-4 wavelet sparsity prior.

    Reference: Lazarus C. et al., MRM 2019;81:3643-3661.
    """
    return _not_implemented("baseline_sparkling")


def baseline_blue_noise_ot(
    V: np.ndarray, V_s_idx: np.ndarray, y: np.ndarray, K: int, U: np.ndarray
) -> ReconResult:
    """Wasserstein blue-noise sampling reconstruction (Goes et al. 2017).

    TODO: implement OT-optimised blue-noise sample selection as a
    *sampling-pattern* baseline; the reconstruction itself can reuse
    cg_on_VB once V_s is replaced.  Distinguish the two roles: this
    function should both (a) re-select V_s by OT blue noise on V, and
    (b) reconstruct on that V_s.

    Reference: Goes F. et al., ACM TOG 2017;36(4):75.
    """
    return _not_implemented("baseline_blue_noise_ot")


def baseline_cs_mri(
    V: np.ndarray, V_s_idx: np.ndarray, y: np.ndarray, K: int, U: np.ndarray
) -> ReconResult:
    """Compressed-sensing MRI baseline (Lustig et al. 2007, MRM).

    TODO: implement L1-wavelet + total-variation reconstruction with
    NUFFT forward operator.  Standard recipe — pysap-mri provides this
    out of the box.

    Reference: Lustig M. et al., MRM 2007;58:1182-1195.
    """
    return _not_implemented("baseline_cs_mri")


def _not_implemented(name: str) -> ReconResult:
    return ReconResult(
        name=name,
        coef=np.zeros(0),
        image_full=np.zeros(0),
        n_iter=0,
        converged=False,
        info={"status": "not_implemented",
              "todo": "fill in following the docstring contract"},
    )


# =====================================================================
# 5. evaluation — NRMSE / SSIM / cond / Spearman
# =====================================================================

@dataclass
class Metrics:
    nrmse: float = float("nan")
    ssim_proxy: float = float("nan")     # k-space cosine similarity proxy
    cond: float = float("nan")
    sigma_min: float = float("nan")
    sigma_max: float = float("nan")
    sigma_ratio: float = float("nan")    # sigma_min / sigma_max
    rank: int = -1
    info: dict = field(default_factory=dict)


def _nrmse(x_hat: np.ndarray, x_ref: np.ndarray) -> float:
    num = float(np.linalg.norm(x_hat - x_ref))
    den = float(np.linalg.norm(x_ref))
    return num / max(den, 1e-30)


def _ssim_proxy(x_hat: np.ndarray, x_ref: np.ndarray) -> float:
    """Lightweight cosine-similarity stand-in for SSIM.

    Real SSIM needs an image grid; here we work on values at unstructured
    V points, so we use complex cosine similarity in [0, 1].  Replace
    with skimage.metrics.structural_similarity in the v0.2 driver where
    we project to a Cartesian grid for visualisation.
    """
    a = x_hat.ravel()
    b = x_ref.ravel()
    num = float(np.abs(np.vdot(a, b)))
    den = float(np.linalg.norm(a) * np.linalg.norm(b))
    return num / max(den, 1e-30)


def evaluate_recon(
    coef_hat: np.ndarray,
    coef_ref: np.ndarray,
    A: np.ndarray,
) -> Metrics:
    """Compute reconstruction metrics + sampling-matrix conditioning."""
    K = coef_ref.shape[0]
    s = np.linalg.svd(A, compute_uv=False)
    sigma_max = float(s[0]) if len(s) else 0.0
    sigma_min = float(s[-1]) if len(s) else 0.0
    rank = int(np.linalg.matrix_rank(A))
    cond = sigma_max / sigma_min if sigma_min > 0 else float("inf")
    return Metrics(
        nrmse=_nrmse(coef_hat, coef_ref),
        ssim_proxy=_ssim_proxy(coef_hat, coef_ref),
        cond=cond,
        sigma_min=sigma_min,
        sigma_max=sigma_max,
        sigma_ratio=(sigma_min / sigma_max) if sigma_max > 0 else 0.0,
        rank=rank,
    )


def spearman_rho(x: np.ndarray, y: np.ndarray) -> tuple[float, float]:
    """Spearman rank correlation rho + two-sided p-value via scipy."""
    from scipy.stats import spearmanr
    res = spearmanr(x, y)
    return float(res.correlation), float(res.pvalue)


# =====================================================================
# 6. seam8_test — quadrature error vs sampling cond, on the *same* V
# =====================================================================
# Goal (from b3pre §6.5 + A-1-pre §5.2):
#
#   For each V geometry t, compute
#     E_q(t)  = quadrature error of integrating the reference signal
#               on K(V_t) using Whitney-0 weights,
#     C(t)    = cond(A_t) of the sampling matrix on a fixed V_s rule.
#
#   H_0:  E_q and C^{-1} are independent across t.
#   H_1 (seam 8):  E_q and C^{-1} are *negatively* correlated
#                  (cartesian: bad quadrature, good sampling;
#                   sparkling: good quadrature, bad sampling).
#
# Falsification: compute Spearman( E_q, C^{-1} ) over the trajectory set;
# require rho < -0.5 with p < 0.05 to claim seam 8 reverse-correlation.

def quadrature_error(
    V: np.ndarray,
    edges: np.ndarray,
    rho_at_V: np.ndarray,
    rho_truth_integral: float,
) -> float:
    """Whitney-0 (piecewise linear) quadrature on the Delaunay complex.

    Approximates  int_{Omega_k} rho(k) dk  by sum over tetrahedra of
    (vol(T) * mean of vertex values).  Compares against the closed-form
    integral ``rho_truth_integral`` (provided by Phantom3D since the
    Gaussian-mixture phantom has analytic integral).

    Returns absolute relative error.
    """
    from scipy.spatial import Delaunay
    tri = Delaunay(V, qhull_options="QJ")
    tet = tri.simplices                    # (N_T, 4)
    pts = V[tet]                           # (N_T, 4, 3)
    # signed tetra volume = |det([v1-v0; v2-v0; v3-v0])| / 6
    M = pts[:, 1:] - pts[:, :1]            # (N_T, 3, 3)
    vols = np.abs(np.linalg.det(M)) / 6.0
    vals = rho_at_V[tet].mean(axis=1)      # (N_T,)
    integral_approx = float(np.sum(vols * vals.real))   # real for E_q here
    return abs(integral_approx - rho_truth_integral) / max(abs(rho_truth_integral), 1e-30)


def phantom_truth_integral(phantom: Phantom3D) -> float:
    """Closed-form  int rho(x) dx  for the Gaussian-mixture phantom.

    int a * exp(-|x-c|^2 / 2 sigma^2) dx = a * (2 pi)^{3/2} * sigma^3.
    We integrate the *real part* of the mixture (matches what
    quadrature_error returns).
    """
    s = phantom.sigmas
    a = phantom.intensities.real
    return float(np.sum(a * (2 * np.pi) ** 1.5 * s ** 3))


def run_seam8(
    trajectories: list[str],
    n_target: int = 300,
    K: int = 50,
    rule: str = "rand_50pct",
    seed: int = 20260506,
) -> dict:
    """Drive the seam-8 reverse-correlation test across trajectories.

    Returns a dict with per-trajectory (E_q, cond) plus the Spearman
    correlation between E_q and 1/cond.
    """
    rng = np.random.default_rng(seed)
    phantom = make_shepplogan_like(seed=seed)
    truth = phantom_truth_integral(phantom)

    eqs: dict[str, float] = {}
    conds: dict[str, float] = {}

    for name in trajectories:
        V = make_trajectory(name, n_target=n_target)
        edges, L0, mu, U = build_complex_and_spectrum(V, K_eig=K)

        # quadrature: evaluate the (real-space) phantom rho at V points
        rho_at_V = phantom.evaluate_at(V).real
        eq = quadrature_error(V, edges, rho_at_V, truth)

        # sampling cond: pick V_s by the named rule, build A, take cond
        configs = b3pre.make_subsample_configs(V, K=K, k_max=b3pre.K_MAX)
        if rule not in configs:
            raise KeyError(f"rule {rule!r} not in {sorted(configs)}")
        V_s = configs[rule]
        A = sampling_matrix(U, V_s, K)
        s = np.linalg.svd(A, compute_uv=False)
        c = float(s[0] / s[-1]) if s[-1] > 0 else float("inf")

        eqs[name] = eq
        conds[name] = c

    # Spearman rho between E_q and 1/cond (seam 8 -> negative)
    names = list(eqs.keys())
    eq_arr = np.array([eqs[n] for n in names])
    inv_c = 1.0 / np.array([conds[n] for n in names])
    if len(names) >= 3:
        rho, pval = spearman_rho(eq_arr, inv_c)
    else:
        rho, pval = float("nan"), float("nan")

    return {
        "rule": rule,
        "K": K,
        "n_target": n_target,
        "per_trajectory": {n: {"E_q": eqs[n], "cond": conds[n]} for n in names},
        "spearman_Eq_vs_invcond": {"rho": rho, "pvalue": pval},
        "seam8_supported": (rho < -0.5 and pval < 0.05) if not np.isnan(rho) else None,
    }


# =====================================================================
# 7. a1pre_test — sigma_min/sigma_max == V_B(V) frame-bound ratio?
# =====================================================================
# A-1-pre §2.1 claims (a) sigma_min(A) >= tau sigma_max(A)
#               <=>  (b) V_B(V) is a tau-Riesz sequence on V_s with
#                        frame bounds (alpha, beta), beta/alpha <= 1/tau.
#
# Numerical consistency: alpha/beta computed by direct minimisation of
# ||A c|| / ||c|| over V_B should equal sigma_min/sigma_max (from SVD).
# Any nontrivial discrepancy exposes a hidden assumption in the proof.

def frame_bound_ratio_from_VB(
    U: np.ndarray, V_s_idx: np.ndarray, K: int, n_probe: int = 4096,
    seed: int = 20260506,
) -> tuple[float, float]:
    """Estimate (alpha, beta) — the V_B Riesz frame bounds — independently
    of SVD, by an extremal-direction search over unit vectors in V_B.

    This is the test target of A-1-pre §5.2: if the (a)<=>(b) equivalence
    in the proof has a hidden assumption, the estimated (alpha, beta)
    will *not* converge to (sigma_min(A), sigma_max(A)).

    Method: random unit-vector probing recovers a *biased* estimate
    (alpha_probe >= sigma_min, beta_probe <= sigma_max) because the
    iid Gaussian directions never hit the extremal singular vectors in
    high dimension.  We therefore additionally do a few power-iteration
    refinement steps to sharpen the bounds; in finite precision they
    *should* converge to (sigma_min, sigma_max).  The reported
    'rel_gap' is the residual after refinement — a non-zero gap is the
    signal that the proof has a hidden assumption.
    """
    rng = np.random.default_rng(seed)
    A = sampling_matrix(U, V_s_idx, K)
    AHA = A.conj().T @ A
    # 1) random probe (loose bound)
    coefs = rng.standard_normal((n_probe, K)) + 1j * rng.standard_normal((n_probe, K))
    coefs /= np.linalg.norm(coefs, axis=1, keepdims=True)
    norms = np.linalg.norm(coefs @ A.conj().T, axis=1)
    a_probe, b_probe = float(norms.min()), float(norms.max())
    # 2) power iteration toward the largest eigenvalue of A^* A (= sigma_max^2)
    v = rng.standard_normal(K) + 1j * rng.standard_normal(K)
    for _ in range(60):
        v = AHA @ v
        n = np.linalg.norm(v)
        if n == 0:
            break
        v = v / n
    beta = float(np.sqrt(np.real(np.vdot(v, AHA @ v))))
    # 3) inverse iteration toward the smallest eigenvalue (= sigma_min^2).
    # Use shifted operator (lam_max * I - A^* A) and power-iterate that.
    shift = beta ** 2 + 1e-12
    M = shift * np.eye(K, dtype=AHA.dtype) - AHA
    w = rng.standard_normal(K) + 1j * rng.standard_normal(K)
    for _ in range(120):
        w = M @ w
        n = np.linalg.norm(w)
        if n == 0:
            break
        w = w / n
    alpha2 = shift - np.real(np.vdot(w, M @ w))
    alpha = float(np.sqrt(max(alpha2, 0.0)))
    # Combine: alpha_final = min(probe_alpha, power_alpha) is tighter
    # estimate of true sigma_min; beta_final = max(probe_beta, power_beta)
    # is tighter estimate of true sigma_max.
    alpha_final = min(a_probe, alpha)
    beta_final = max(b_probe, beta)
    return alpha_final, beta_final


def run_a1pre_test(
    trajectories: list[str],
    n_target: int = 300,
    K: int = 50,
    rule: str = "rand_50pct",
) -> dict:
    """Compare SVD-derived (sigma_min, sigma_max) with random-probe
    estimates of (alpha, beta) over V_B.

    Returns per-trajectory ratios and a 'max_relative_gap' across the
    set — the falsifiable quantity.
    """
    out: dict[str, dict] = {}
    max_gap = 0.0
    for name in trajectories:
        V = make_trajectory(name, n_target=n_target)
        _, _, _, U = build_complex_and_spectrum(V, K_eig=K)
        configs = b3pre.make_subsample_configs(V, K=K, k_max=b3pre.K_MAX)
        V_s = configs[rule]
        A = sampling_matrix(U, V_s, K)
        s = np.linalg.svd(A, compute_uv=False)
        sigma_min, sigma_max = float(s[-1]), float(s[0])

        alpha, beta = frame_bound_ratio_from_VB(U, V_s, K)
        # alpha estimated by random probe is an UPPER bound on sigma_min
        # (true min is the worst case); same logic, beta is a LOWER bound
        # on sigma_max.  So we expect alpha >= sigma_min  and  beta <= sigma_max.
        # The reported "gap" is the relative diff in the ratios.
        ratio_svd = sigma_min / sigma_max if sigma_max > 0 else 0.0
        ratio_probe = alpha / beta if beta > 0 else 0.0
        gap = abs(ratio_probe - ratio_svd) / max(ratio_svd, 1e-30)
        max_gap = max(max_gap, gap)
        out[name] = {
            "sigma_min": sigma_min, "sigma_max": sigma_max, "ratio_svd": ratio_svd,
            "alpha_probe": alpha, "beta_probe": beta, "ratio_probe": ratio_probe,
            "rel_gap": gap,
        }
    return {"per_trajectory": out, "max_relative_gap": max_gap,
            "verdict": "consistent" if max_gap < 0.5 else "discrepancy_check_assumptions"}


# =====================================================================
# 8. main — smoke driver
# =====================================================================
# A cheap end-to-end run to prove the wiring.  *Not* the v0.2 sweep.

def smoke_run(out_path: Optional[Path] = None,
              snr_db: float = 20.0, n_target: int = 200,
              K: int = 30) -> dict:
    """Run cartesian + random end-to-end at small scale.  Print results."""
    if not _HAS_B3PRE:
        return {"error": _B3PRE_IMPORT_ERR}

    rng = np.random.default_rng(20260506)
    phantom = make_shepplogan_like(seed=0)
    results: dict = {"snr_db": snr_db, "n_target": n_target, "K": K,
                     "trajectories": {}}

    for name in ("cartesian", "random"):
        t0 = time.time()
        V = make_trajectory(name, n_target=n_target)
        edges, L0, mu, U = build_complex_and_spectrum(V, K_eig=K)
        # ground-truth complex k-space samples
        S_true = phantom.analytic_kspace(V)
        sigma = snr_to_sigma(S_true, snr_db)
        S_noisy = add_rician_noise(S_true, sigma, rng)
        # project the truth into V_B to get the *reachable* coefficients
        coef_ref = U.conj().T @ S_true
        # subsample
        configs = b3pre.make_subsample_configs(V, K=K, k_max=b3pre.K_MAX)
        V_s = configs["rand_50pct"]
        A = sampling_matrix(U, V_s, K)
        y = S_noisy[V_s]
        recon = cg_on_VB(A, y, K, tikhonov=1e-6 * float(np.linalg.norm(A) ** 2))
        m = evaluate_recon(recon.coef, coef_ref, A)
        results["trajectories"][name] = {
            "N": int(V.shape[0]),
            "edges": int(edges.shape[0]),
            "sigma": sigma,
            "metrics": asdict(m),
            "elapsed_sec": round(time.time() - t0, 2),
        }
    if out_path is not None:
        out_path.write_text(json.dumps(results, indent=2))
    return results


def main() -> None:
    print("=" * 60)
    print("B-3 main simulation — SKELETON smoke run")
    print("=" * 60)
    res = smoke_run()
    print(json.dumps(res, indent=2, default=str))

    print("\n--- seam-8 reverse-correlation test (cartesian + random + sparkling) ---")
    s8 = run_seam8(["cartesian", "random", "sparkling"], n_target=200, K=30)
    print(json.dumps(s8, indent=2, default=str))

    print("\n--- A-1-pre numerical-consistency test ---")
    a1 = run_a1pre_test(["cartesian", "random"], n_target=200, K=30)
    print(json.dumps(a1, indent=2, default=str))


# =====================================================================
# 9. minimal unit tests (run as `python B3_main_simulation.py test`)
# =====================================================================
# Three tiny checks that exercise the data flow without the full sweep.

def test_phantom_kspace_consistency() -> None:
    """analytic_kspace at k=0 must equal real-space integral of rho."""
    p = make_shepplogan_like(seed=1)
    s_at_0 = p.analytic_kspace(np.zeros((1, 3)))[0]
    integral_real = phantom_truth_integral(p)
    # imaginary part of intensities means s_at_0 has both parts;
    # the real part should match the closed-form integral.
    assert abs(s_at_0.real - integral_real) < 1e-6, (s_at_0.real, integral_real)


def test_sampling_matrix_shape() -> None:
    """sampling_matrix returns (M, K) and is consistent with b3pre."""
    if not _HAS_B3PRE:
        print("SKIP: b3pre not importable"); return
    V = make_trajectory("random", n_target=120)
    _, _, _, U = build_complex_and_spectrum(V, K_eig=20)
    idx = np.arange(0, V.shape[0], 3)
    A = sampling_matrix(U, idx, 20)
    assert A.shape == (idx.size, 20), A.shape
    # cross-check vs b3pre.sampling_metrics
    ref = b3pre.sampling_metrics(U, idx, 20)
    s = np.linalg.svd(A, compute_uv=False)
    assert abs(s[0] - ref["sigma_max"]) < 1e-9
    assert abs(s[-1] - ref["sigma_min"]) < 1e-9


def test_cg_on_VB_no_noise_recovers() -> None:
    """In the noise-free over-determined case CG must recover c exactly."""
    if not _HAS_B3PRE:
        print("SKIP: b3pre not importable"); return
    V = make_trajectory("cartesian", n_target=200)
    _, _, _, U = build_complex_and_spectrum(V, K_eig=20)
    K = 20
    rng = np.random.default_rng(0)
    c_true = rng.standard_normal(K) + 1j * rng.standard_normal(K)
    # use ALL points -> A = U[:, :K] is an isometry (orthonormal cols)
    idx = np.arange(V.shape[0])
    A = sampling_matrix(U, idx, K)
    y = A @ c_true
    rec = cg_on_VB(A, y, K, tikhonov=0.0, rtol=1e-12, max_iter=500)
    err = np.linalg.norm(rec.coef - c_true) / np.linalg.norm(c_true)
    assert err < 1e-6, f"CG did not recover c (err={err:.3e})"


def test_seam8_runs() -> None:
    """seam-8 driver returns a well-formed dict on a tiny set."""
    if not _HAS_B3PRE:
        print("SKIP: b3pre not importable"); return
    res = run_seam8(["cartesian", "random"], n_target=120, K=15)
    assert "spearman_Eq_vs_invcond" in res
    assert "per_trajectory" in res and len(res["per_trajectory"]) == 2


def _run_tests() -> int:
    tests = [
        test_phantom_kspace_consistency,
        test_sampling_matrix_shape,
        test_cg_on_VB_no_noise_recovers,
        test_seam8_runs,
    ]
    n_pass = 0
    for fn in tests:
        try:
            fn()
            print(f"PASS  {fn.__name__}")
            n_pass += 1
        except AssertionError as e:
            print(f"FAIL  {fn.__name__}: {e}")
        except Exception as e:
            print(f"ERROR {fn.__name__}: {type(e).__name__}: {e}")
    print(f"\n{n_pass}/{len(tests)} tests passed")
    return 0 if n_pass == len(tests) else 1


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "test":
        sys.exit(_run_tests())
    main()
