# Sheaf Bandwidth: A Categorical Bridge

This repository contains the paper and Lean 4 formalization for:

**Sheaf Bandwidth: A Categorical Bridge Between Topological Signal Processing and Finite Element Exterior Calculus**

The paper introduces `sheafBW`, a categorically intrinsic spectral-gap-normalized bandwidth invariant on cellular sheaves of Hilbert spaces. It is proven equivalent to the SVD-style condition number `σ_min(A) / σ_max(A)` under a constructed double 0-cell complex (`thm:strict-equality`), unitary-invariant on the cellular-sheaf side (`prop:sheafBW-unitary`), and applied to three previously disjoint domains: topological signal processing on MRI sampling; finite element electromagnetics; and Brillouin zone tetrahedron quadrature. Robinson's [2014, §6] open problem on sheaf bandwidth is narrowed to two specific clauses (OP1: non-trivial dagger structure; OP2: constructive Pareto-optimality for the empirical sampling–integration trade-off).

The finite-dimensional operator and cellular-sheaf core of the paper (1D / k=0) is fully mechanized in Lean 4 (mathlib4 `v4.30.0-rc2`): `lake build` passes the entire library with 8326 jobs / 0 sorry / 0 admitted / 0 warnings. The category-theoretic packaging of §5.7, the physical instances of §6, and the empirical Pareto proposition are explicitly left informal with disclaimer footnotes (see "Scope and explicit limitations" below).

## Quick start

### Read the paper

```bash
open paper/v0.1/main.pdf
```

### Verify the Lean proofs

```bash
cd lean
lake update      # fetches mathlib4 (one-time, downloads ~7 GB of cache)
lake build       # incremental; first build ~30 min
# Expected: 8326 jobs PASS / 0 sorry / 0 admit / 0 warning
```

The paper ↔ Lean correspondence table is in [`lean/CROSSREF.md`](lean/CROSSREF.md).

### Reproduce the numerical experiments (paper §7)

```bash
cd code
python3 -m venv .venv && source .venv/bin/activate
pip install -r requirements.txt
python3 A_route_ch3_numerical.py
```

Random seed is fixed (`20260507`) for reproducibility; the verification checks the algebraic identity `sheafBW(Samps) = σ_min(A) / σ_max(A)` to machine precision (`reldiff < 5 × 10⁻¹⁶`).

## Structure

| Directory | Contents |
|---|---|
| `lean/` | Lean 4 formalization (12 source files in `lean/MRI/Cellular/`, 2169 LOC; full paper ↔ Lean mapping in `lean/CROSSREF.md`) |
| `paper/v0.1/` | Paper LaTeX source + compiled PDF (29 pages) |
| `code/` | §7 numerical reproducibility scripts (Python) |

## Verification

| Track | Status |
|---|---|
| Lean formalization | `lake build` passes / 8326 jobs / 0 sorry / 0 admit / 0 warning |
| Paper build | `pdflatex` double-pass / 29 pages / 0 undefined ref |
| Numerical reproducibility | `reldiff ≤ 1.64 × 10⁻¹⁴` across three toy instances (§7) |

### Scope and explicit limitations

The paper formalizes the **finite-dimensional operator / sheaf core** restricted to the 1D / k = 0 model. The following are explicitly **not** formalized and are left informal with disclaimer footnotes at their declarations:

- Category-theoretic packaging of `\CellSh^{\fin}_{\Hilb,\mathrm{u}}(X)` (paper `def:unitary-subcat`, `prop:unitary-groupoid`)
- Physical correspondence maps for the three application instances (paper `def:sampling-map`, `def:integration-map`)
- The empirical sampling–integration Pareto trade-off (paper `empirical:8b`) — supported by two quantitative evidence channels plus a directional heuristic, not promoted to theorem status
- The geometric "scalar multiple of isometry" clause of `thm:strict-equality`

The categorical invariant `sheafBW` is numerically isomorphic to the frame-bound ratio of frame theory; the contribution is the **categorical lift** plus the closed Hilbert complex structure on the cellular-sheaf side, plus the **mechanized formalization** in Lean 4, restricted to the 1D / k = 0 model. General-k FEEC bridging is not claimed.

## Citing

Citation entry will be added when an arXiv preprint or journal publication becomes available.

## Author

Independent Researcher.

## License

[License placeholder — TBD]
