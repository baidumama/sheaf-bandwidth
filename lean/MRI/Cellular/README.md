# MRI.Cellular — Cellular sheaf formalization

> Lean 4 + mathlib4 formalization of cellular sheaf data structures together with
> the main results of paper §3 (Triangle Equivalence) and §5 (strict equality +
> sheafBW unitary invariance).
>
> `lake build` PASS / 8326 jobs / 0 error / 0 warning / 0 sorry / 0 admit.

Entry point: `lean/MRI.lean` (imports the 11 modules below).

## File structure

| 文件 | 角色 | informal cross-ref |
|---|---|---|
| `Complex.lean` | `Complex1D` structure(0/1-cell complex):Cells₀ / Cells₁ + face₀ / face₁ | §5 def:Xsamp |
| `Sheaf.lean` | `CellularSheaf C stalk₀ stalk₁` structure(**generic per-cell stalks**:每个 0-cell / 1-cell 独立配 ℂ-Hilbert)+ restrict₀ / restrict₁(dependent type) | §5 def:finite-dim-sheaf + def:sampling-sheaf |
| `Sections.lean` | `discrepancy : (∀ v, stalk₀ v) →ₗ[ℂ] (∀ e, stalk₁ e)` LinearMap + `globalSections` (= `LinearMap.ker discrepancy`) | §3 (F1) + §5 def:cochain-space |
| `Inner.lean` | `Cochain0 / Cochain1` ℓ² Hilbert structure(via `PiLp 2`,Fintype + finite-dim heterogeneous stalks) | §3 (F1) + §5 def:cochain-space |
| `Coboundary.lean` | `coboundary` operator(= discrepancy alias) + first lemma `globalSections = ker coboundary`(by `rfl`) + `coboundaryHilbert`(Hilbert-layer wrap via `WithLp.linearEquiv 2`) | §5 def:coboundary + §3 (F2) prop:delta-equals-A |
| `Sampling.lean` | `XsampVert` inductive + `Xsamp : ℕ → Complex1D` + `Samps E eval` sampling sheaf;canonical isometry(`canonicalLinearEquiv` operator-layer / `canonicalLinearIsometryEquiv` Hilbert-layer) + sampling operator(plain Π + `samplingOpEuclidean`) + **`coboundary_eq_sampling_op`**(prop:delta-equals-A operator-level) + **`coboundaryHilbert_eq_samplingOpEuclidean`**(prop:delta-equals-A Hilbert-level) | §5 def:Xsamp + def:sampling-sheaf + **lem:canonical-isometry + prop:delta-equals-A** |
| `Spectral.lean` | paper §5 def:spectral-gap + def:sheafBW general form:`GammaPlus`(`σ_max(δ⁰)²`)/ `gammaPlus`(`σ_min positive sv²`)/ `sheafBW`(`√(γ_+ / Γ_+)` + corner case) + 3 non-negativity lemmas | §5 def:spectral-gap (line 154-169) + def:sheafBW (line 38-50) |
| `SamplingSpectral.lean` | generic `LinearMap.singularValues_comp_linearIsometryEquiv` helper(unitary invariance) + spectrum reduction on `Samps`:`singularValues_coboundaryHilbert_eq_samplingOpEuclidean` + `gammaPlus / GammaPlus_Samps_eq_*` + `sheafBW_Samps_eq_singularValues_div` + **`strict_equality`(Theorem 5.3 single statement)** + `H0_vanishing_iff`(corollary) | §5 line 481-537:**Theorem 5.3 strict equality + cor:H0-vanishing** |
| `Variational.lean` | Generic LinearMap singular value variational characterization + (a)⇔(b) generic form:`IsSymmetric.eigenvalues_{zero,last}_eq_{iSup,iInf}_rayleigh`(mathlib PR candidates) + `sq_singularValues_{zero,last}_eq_{iSup,iInf}_norm_sq`(paper eq:sigma-max/min-var) + rayleighQuotient bridge + spherical form + `injective_iff_singularValues_last_pos`(mathlib PR candidate) + `triangle_equiv_a_iff_b`(paper §3 (a)⇔(b) generic LinearMap form) | §3 line 99-198 (a)⇔(b) Riesz form |
| `TriangleEquivalence.lean` | paper §3 specialized + TFAE main statement:`injective_samplingOp_iff_injective_samplingOpEuclidean`(WithLp bridge) + `triangle_equiv_a_iff_c`(paper §3 (a)⇔(c) Robinson sheaf form) + **`triangle_equivalence`**(paper §3 thm:triangle-equiv TFAE three-way equivalence main statement) | **§3 thm:triangle-equiv main statement** |
| `HilbertComplex.lean` | paper §5 Theorem 5.11 closed Hilbert complex 条件 (d):`coboundaryHilbert_range_isClosed`(fin-dim trivial) + paper §5 lem:L0-spectrum 三结论:`sheafLaplacian0` def + `isSymmetric` + `isPositive` + `ker_eq`(mathlib `{isSymmetric,isPositive,ker}_adjoint_comp_self` apply) | §5 Theorem 5.11 (d) + lem:L0-spectrum |
| `Unitary.lean` | paper §5 Proposition 5.4 prop:sheafBW-unitary:`UnitarySheafMorphism` structure(family of stalk-wise `≃ₗᵢ[ℂ]` + sheaf-morphism compatibility) + `cochainUnitary0/1`(via `piLpCongrRight`) + `discrepancy_commute`(plain Π) + `coboundaryHilbert_commute` + `commute_linearMap` + `finrank_range_coboundaryHilbert_eq` + `singularValues_coboundaryHilbert_eq` + **`sheafBW_eq`**(paper §5 Prop 5.4 main statement) | **§5 prop:sheafBW-unitary main statement** |

## Design decisions

| 选择 | 理由 |
|---|---|
| **stalks 标量域 ℂ** | MRI signal complex-valued; paper §2/§3 uniformly use ℂ |
| **Complex1D 仅 0/1 维** | paper §3 双-Z₂ 模型只用 0-cell + 1-cell;通用 CellComplex 是 over-engineer |
| **Generic per-cell stalks** | paper §5 def:sampling-sheaf heterogeneous stalks (σ_B = V_B / σ_∞ = 0 / τ_i = ℂ) requires per-cell type dependence; a uniform stalk simplification cannot accommodate this |
| **仅 H⁰(globalSections)** | §3 + §5 main results use H⁰ only;H¹ introduced through (a)⇔(c) |
| **coboundary 当前为 LinearMap 接口** | Cochain data + globalSections kernel form;`(δ⁰)*δ⁰` spectrum (paper §5 thm:strict-equality) carried by ContinuousLinearMap layer |

## Interface boundaries

- **ContinuousLinearMap interface** (coboundary: `Cochain0 →L[ℂ] Cochain1`): carries the spectral-gap reasoning of paper §5 thm:strict-equality.
- **PiLp / plain Pi bridge**: in mathlib4 v4.30, `Cochain0 C stalk₀ ≠ (∀ v, stalk₀ v)` is not sufficiently reducible at LinearMap ascription positions — `WithLp.equiv` is used as an explicit bridge.
- **H¹ cohomology**: introduced for (a)⇔(c) via SVD + Courant-Fischer.
- **2D+ cell complex**: paper §6 instances are treated as informal physical correspondence; the current formalization works only with 0/1-cell complexes.

## Verification

`lake build` passes the entire library (8326 jobs, 0 error / 0 warning / 0 sorry / 0 admit).

Sanity invariants maintained throughout:
- `globalSections_eq_ker_coboundary` holds by `rfl`
- Heterogeneous stalks on `Samps` (E / 0-dim Hilbert / ℂ): Cochain0/1 InnerProductSpace ℂ auto-derived
- paper §5 sign convention preserved (face₀ ↔ σ_B (+1) / face₁ ↔ σ_∞ (-1))

## Implementation notes

1. **`noncomputable example` is the norm for ℂ**: mathlib4's normed-space instances for ℂ (`Complex.instRCLike` / `instCommCStarAlgebraComplex`) are noncomputable because they depend on `Complex.abs`. All def/example uses of ℂ default to `noncomputable`.
2. **`abbrev` enables type-class auto-derive**: `Cochain0 := PiLp 2 (...)` uses `abbrev` rather than `def`, so `inferInstance` can unfold to find PiLp's InnerProductSpace instance. All definitions whose downstream type-class search needs to see through them use `abbrev`.
3. **`PiLp` and plain Pi are not strict-defeq**: at LinearMap source/target ascription positions, Lean 4's typeclass solver does not unfold sufficiently — `WithLp.equiv` is used as an explicit bridge.
4. **Lean 4 identifier rules**: `∞` (U+221E, Sm category) is not a legal subsequent character. ASCII `σInf` is used in identifiers; the paper symbol σ_∞ is kept in docstrings/comments.
5. **mathlib4 `InnerProductSpace ℂ PUnit` not derivable**: mathlib4 v4.30 has `NormedAddCommGroup PUnit` but lacks `InnerProductSpace ℂ PUnit`. Alternative: `EuclideanSpace ℂ (Fin 0)` (mathlib standard 0-dim Hilbert space, auto-derived via PiLp 2).
6. **Heterogeneous stalks instance pattern**: `noncomputable instance (v : XsampVert) : NormedAddCommGroup (stalk0Samps E v) := by cases v <;> infer_instance` (requires `noncomputable` since EuclideanSpace's normed structure derives via `PiLp.normedAddCommGroup`).
