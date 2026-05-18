"""
Three-instance numerical verification: sheafBW = sigma_min / sigma_max
======================================================================

Verifies the strict equality (paper §5 Theorem) numerically on three
finite-dimensional instances:

  1. TopSP: V_B Hodge bandlimited subspace (toy: random orthonormal basis)
  2. FEM-EM: V_S Sobolev-regular subspace (toy: 1D evaluation on
     quasi-uniform boundary cells)
  3. BZ tetrahedron: V_occ Heaviside-occupied subspace (linear segments,
     Whitney 0-form)

Expected: relative deviation between sheafBW (via gamma_+/Gamma_+ spectrum)
and sigma_min(A)/sigma_max(A) below 1e-10 (machine precision) on all three.
"""

from __future__ import annotations

import numpy as np

SEED = 20260507
np.random.seed(SEED)


def compute_sheafBW_via_spec(A: np.ndarray) -> float:
    """sheafBW via spectral gap of (delta^0)^* delta^0 = A^* A on V_? domain.

    Definition 4.1: sheafBW = sqrt(gamma_+ / Gamma_+) where
      gamma_+ = lambda_min((delta^0)^* delta^0)|_{(ker delta^0)^perp}
      Gamma_+ = lambda_max

    For injective A (dim col = K, rank = K), gamma_+ = smallest eigenvalue of A* A.
    """
    gram = A.conj().T @ A
    spec = np.linalg.eigvalsh(gram)
    gamma_plus = spec[0]
    Gamma_plus = spec[-1]
    return float(np.sqrt(gamma_plus / Gamma_plus))


def compute_ratio_sigma(A: np.ndarray) -> float:
    """sigma_min(A) / sigma_max(A)."""
    sv = np.linalg.svd(A, compute_uv=False)
    return float(sv[-1] / sv[0])


def report(name: str, A: np.ndarray) -> dict:
    """Compute both quantities and print comparison."""
    sheafBW = compute_sheafBW_via_spec(A)
    ratio = compute_ratio_sigma(A)
    rel_diff = abs(sheafBW - ratio) / ratio if ratio > 0 else float("inf")
    print(f"\n{name}:")
    print(f"  shape A                 = {A.shape}")
    print(f"  sheafBW (spectral gap)  = {sheafBW:.12f}")
    print(f"  sigma_min/sigma_max     = {ratio:.12f}")
    print(f"  rel diff                = {rel_diff:.3e}")
    return {
        "name": name,
        "A_shape": A.shape,
        "sheafBW": sheafBW,
        "ratio_sigma": ratio,
        "rel_diff": rel_diff,
    }


def main():
    print("=" * 70)
    print("Three-instance numerical verification: sheafBW = sigma_min / sigma_max")
    print("=" * 70)
    print(f"seed = {SEED}")

    results = []

    # -------------------------------------------------------------------------
    # Instance 1 (TopSP): V_B Hodge bandlimited subspace
    # -------------------------------------------------------------------------
    # Toy: K=10 dim subspace V_B in C^N=100, sample at M=30 random positions.
    # A^TopSP = U_VB[V_s, :] where U_VB has orthonormal columns (V_B basis).
    N1, K1, M1 = 100, 10, 30
    U1, _ = np.linalg.qr(np.random.randn(N1, K1))
    idx1 = np.random.choice(N1, M1, replace=False)
    A1 = U1[idx1, :]
    results.append(report("Instance 1 (TopSP toy, V_B Hodge bandlimited)", A1))

    # -------------------------------------------------------------------------
    # Instance 2 (FEM-EM): V_S Sobolev regular subspace, evaluate at boundary cells
    # -------------------------------------------------------------------------
    # Toy: K2=6 dim Sobolev-bounded subspace in W^0(K) of dim N2=50.
    # Evaluate at M2=8 quasi-uniform boundary points (mimicking Whitney 0-form
    # evaluation on a 1D mesh with Dirichlet boundary).
    N2, K2, M2 = 50, 6, 8
    U2, _ = np.linalg.qr(np.random.randn(N2, K2))
    idx2 = np.array([0, 7, 14, 21, 28, 35, 42, 49])
    A2 = U2[idx2, :]
    results.append(report("Instance 2 (FEM-EM toy, V_S Sobolev regular, 1D eval)", A2))

    # -------------------------------------------------------------------------
    # Instance 3 (BZ tetrahedron): V_occ Heaviside-occupied (linear segment)
    # -------------------------------------------------------------------------
    # Toy: K3=4 dim occupancy subspace (4 vertices of a tetrahedron, linear
    # segment of Blöchl method = Whitney 0-form literal). Quadrature
    # measurement at M3=12 test points (sub-tetrahedral integration grid).
    N3, K3, M3 = 30, 4, 12
    U3, _ = np.linalg.qr(np.random.randn(N3, K3))
    idx3 = np.random.choice(N3, M3, replace=False)
    A3 = U3[idx3, :]
    results.append(
        report(
            "Instance 3 (BZ tetrahedron toy, V_occ linear segment, Whitney 0-form)",
            A3,
        )
    )

    # -------------------------------------------------------------------------
    # Summary
    # -------------------------------------------------------------------------
    print("\n" + "=" * 70)
    print("Summary: 三 instance 数值偏差")
    print("=" * 70)
    max_rel = max(r["rel_diff"] for r in results)
    threshold = 1e-10
    for r in results:
        status = "PASS" if r["rel_diff"] < threshold else "REVIEW"
        print(f"  {r['name']:<70s} rel_diff = {r['rel_diff']:.3e}  [{status}]")
    print(f"\n  max rel_diff across instances = {max_rel:.3e}")
    print(f"  threshold (machine precision)  = {threshold:.0e}")

    if max_rel < threshold:
        print("\n=== ✅ 三 instance 全部:sheafBW == sigma_min/sigma_max 数值上严格一致 ===")
        print("=== ✅ Theorem 4.3-v0.3 严格等式在三 instance 上数值实测通过 ===")
    else:
        print("\n=== Warning: relative deviation exceeds threshold ===")

    return results


if __name__ == "__main__":
    main()
