# MRI — Sheaf Bandwidth in Lean 4

Lean 4 (mathlib4 `v4.30.0-rc2`) formalization of the paper
**"Sheaf Bandwidth: A Categorical Bridge Between Topological Signal
Processing and Finite Element Exterior Calculus"** (informal source:
[`../paper/v0.1/main.pdf`](../paper/v0.1/main.pdf), 28 pages).

## Status

`lake build` PASS · **8326 jobs** · **0 sorry · 0 admit · 0 warning**

## What is formalized

Three main finite-dimensional operator/sheaf-core results from the paper are
formalized end-to-end and machine-verified by the Lean kernel:

| paper                                                  | Lean entry point                                              |
|--------------------------------------------------------|---------------------------------------------------------------|
| §3 `thm:triangle-equiv` — Triangle Equivalence         | [`Cellular/TriangleEquivalence.lean`](MRI/Cellular/TriangleEquivalence.lean) → `triangle_equivalence` |
| §5 `thm:strict-equality` — strict equality on `Samps`  | [`Cellular/SamplingSpectral.lean`](MRI/Cellular/SamplingSpectral.lean) → `strict_equality_full_rank` |
| §5 `prop:sheafBW-unitary` — sheafBW unitary invariance | [`Cellular/Unitary.lean`](MRI/Cellular/Unitary.lean) → `sheafBW_eq`                                    |

Together with the supporting definitions, lemmas, and corollaries inside the
declared formalization scope. **Full paper ↔ Lean correspondence table:**
[`CROSSREF.md`](CROSSREF.md).

## What is *not* formalized

The following are declared informal and **not** promoted to Lean theorems:

- paper §5.7 `def:unitary-subcat` + `prop:unitary-groupoid` —
  category-theoretic packaging. The core sheaf-bandwidth invariance is
  already captured by `prop:sheafBW-unitary` (formalized).
- paper §6 three physical instances (TopSP / FEM / Brillouin zone) +
  `def:sampling-map` + `def:integration-map` — physical correspondences
  (B-spline FE, quadrature, Bloch–Floquet), not mathematical theorems.
- paper §6 Empirical Proposition 8b — empirical (declared as such in
  `CROSSREF.md` §C).

See [`CROSSREF.md`](CROSSREF.md) §C for the explicit informal-only list.

## Build

Requires `elan` (Lean version manager). Toolchain is pinned in
[`lean-toolchain`](lean-toolchain) (`leanprover/lean4:v4.30.0-rc2`).

```bash
# from this directory (lean/)
lake exe cache get        # download mathlib oleans (recommended; saves ~20 min)
lake build
```

Expected output: `Build completed successfully (8326 jobs).`

## Project layout

```
lean/
├── MRI.lean              -- top-level import map (annotated by paper section)
├── CROSSREF.md           -- paper ↔ Lean correspondence table
├── lakefile.toml         -- mathlib v4.30.0-rc2 dependency
├── lean-toolchain        -- leanprover/lean4:v4.30.0-rc2
    └── MRI/
        └── Cellular/         -- 12 files, ~2000 LOC
        ├── README.md            -- module overview
        ├── Complex.lean         -- Complex1D base structure
        ├── Sheaf.lean           -- CellularSheaf (paper def:finite-dim-sheaf)
        ├── Sections.lean        -- discrepancy + globalSections
        ├── Inner.lean           -- Cochain0/1 via PiLp 2 (paper def:cochain-space)
        ├── Coboundary.lean      -- coboundary + coboundaryHilbert
        ├── Sampling.lean        -- Xsamp + Samps + canonical isometry
        ├── Spectral.lean        -- gammaPlus + GammaPlus + sheafBW
        ├── SamplingSpectral.lean -- thm:strict-equality + full-rank/boundary forms
        ├── Variational.lean     -- triangle-equiv (a)⇔(b) Riesz form
        ├── TriangleEquivalence.lean -- thm:triangle-equiv (TFAE) + H0 repairs
        ├── HilbertComplex.lean  -- thm:closed-hilbert-complex + lem:L0-spectrum
        └── Unitary.lean         -- prop:sheafBW-unitary
```

## Reading the formalization

- **From a paper statement** → open [`CROSSREF.md`](CROSSREF.md),
  find the `\label{...}` row, jump to the Lean theorem name.
- **From a Lean theorem** → look at its docstring; key results carry a
  `paper-ref: <label>` line pointing back to the paper.
- **Project overview** → read [`MRI.lean`](MRI.lean) — top-level import map
  with per-module annotations grouped by paper section.

## mathlib upstream candidates

Four general-purpose lemmas were discovered during this formalization
and are candidates for upstream contribution to mathlib4:

- `LinearMap.singularValues_comp_linearIsometryEquiv` (pre-compose,
  `Cellular/SamplingSpectral.lean` §1)
- `LinearMap.singularValues_linearIsometryEquiv_comp` (post-compose,
  `Cellular/SamplingSpectral.lean` §1)
- `LinearMap.IsSymmetric.eigenvalues_{zero,last}_eq_{iSup,iInf}_rayleigh`
  (`Cellular/Variational.lean` §1+§3)
- `LinearMap.injective_iff_singularValues_last_pos`
  (`Cellular/Variational.lean` §9)

## License

[TBD]
