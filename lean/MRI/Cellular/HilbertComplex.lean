/-
  MRI.Cellular.HilbertComplex — Closed Hilbert complex structure + L⁰ spectrum

  + 2 实现。informal cross-ref:paper/v0.1 §5
    Theorem 5.11 thm:closed-hilbert-complex + Lemma lem:L0-spectrum。
  依赖:Coboundary.lean(CellularSheaf.coboundaryHilbert)+ Inner.lean。

  paper §5 Theorem 5.11 4 条件(Complex1D specialization):
  - (a) C^k(A) fin-dim Hilbert:`Cochain0/1 := PiLp 2` + Fintype + per-stalk FD
        → **auto-derive**,不需要单独定理。
  - (b) δ^k bounded:LinearMap on fin-dim → fin-dim 自动 bounded
        → **auto-derive**。
  - (c) δ^{k+1} ∘ δ^k = 0:Complex1D 无 2-cell → **vacuous**(δ¹ 不在数据中)。
  - (d) range(δ^0) closed:**真内容**,本文件 `coboundaryHilbert_range_isClosed`
        (via `Submodule.closed_of_finiteDimensional`)。

  paper §5 Lemma lem:L0-spectrum:
  - L⁰ := (δ⁰)* ∘ δ⁰ self-adjoint(`IsSymmetric`)+ positive(`IsPositive`)
        + ker L⁰ = ker δ⁰(= H⁰ at Hilbert layer)
  - 全部 apply mathlib `LinearMap.{isSymmetric,isPositive,ker}_adjoint_comp_self`。
-/

import MRI.Cellular.Coboundary
import MRI.Cellular.Inner
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive

namespace MRI.Cellular

namespace CellularSheaf

variable {C : Complex1D} [Fintype C.Cells₀] [Fintype C.Cells₁]
  {stalk₀ : C.Cells₀ → Type*}
  [∀ v, NormedAddCommGroup (stalk₀ v)] [∀ v, InnerProductSpace ℂ (stalk₀ v)]
  [∀ v, FiniteDimensional ℂ (stalk₀ v)]
  {stalk₁ : C.Cells₁ → Type*}
  [∀ e, NormedAddCommGroup (stalk₁ e)] [∀ e, InnerProductSpace ℂ (stalk₁ e)]

/-! ### §1 Closed Hilbert complex(paper §5 Theorem 5.11) -/

/-- **paper §5 Theorem 5.11 condition (d)**:
`range(δ⁰)` 在 `C^1(A)` 中 closed。

形式:`IsClosed (LinearMap.range S.coboundaryHilbert : Set (Cochain1 C stalk₁))`。

证:fin-dim 平凡 — `S.coboundaryHilbert.range` 是 fin-dim subspace(`source = Cochain0`
fin-dim,`LinearMap.finiteDimensional_range` instance auto-derive 给 range 一个
`FiniteDimensional ℂ` instance)→ `Submodule.closed_of_finiteDimensional` 直接 apply。

注:Theorem 5.11 其他三条:
- (a) `C^k(A)` fin-dim:auto-derive
- (b) `δ^k` bounded:fin-dim LinearMap → CLM auto
- (c) `δ¹ ∘ δ⁰ = 0`:vacuous on Complex1D(无 2-cell)

整体 Theorem 5.11 = (a)(b)(c) auto/vacuous + (d) 本定理。

paper-ref: `thm:closed-hilbert-complex` 条件 (d)(详见 `lean/CROSSREF.md`)。 -/
theorem coboundaryHilbert_range_isClosed (S : CellularSheaf C stalk₀ stalk₁) :
    IsClosed ((LinearMap.range S.coboundaryHilbert) : Set (Cochain1 C stalk₁)) :=
  Submodule.closed_of_finiteDimensional _

/-! ### §2 Sheaf Laplacian L⁰ spectrum(paper §5 Lemma lem:L0-spectrum)

`LinearMap.adjoint` 需要 target FD,故本节添加 `[∀ e, FiniteDimensional ℂ (stalk₁ e)]`。 -/

variable [∀ e, FiniteDimensional ℂ (stalk₁ e)]

/-- **Sheaf Laplacian of degree 0**(paper §5 def:sheaf-laplacian,k=0 case,
δ^{-1} := 0 故 L⁰ = (δ⁰)* ∘ δ⁰)。LinearMap layer(`Cochain0 →ₗ[ℂ] Cochain0`)。 -/
noncomputable def sheafLaplacian0 (S : CellularSheaf C stalk₀ stalk₁) :
    Cochain0 C stalk₀ →ₗ[ℂ] Cochain0 C stalk₀ :=
  LinearMap.adjoint S.coboundaryHilbert ∘ₗ S.coboundaryHilbert

/-- **lem:L0-spectrum 第一条**:L⁰ 是 self-adjoint(`IsSymmetric`)。 -/
theorem sheafLaplacian0_isSymmetric (S : CellularSheaf C stalk₀ stalk₁) :
    (sheafLaplacian0 S).IsSymmetric :=
  LinearMap.isSymmetric_adjoint_comp_self S.coboundaryHilbert

/-- **lem:L0-spectrum 第二条**:L⁰ positive(self-adjoint + ⟨L⁰ x, x⟩ ≥ 0)。 -/
theorem sheafLaplacian0_isPositive (S : CellularSheaf C stalk₀ stalk₁) :
    (sheafLaplacian0 S).IsPositive :=
  LinearMap.isPositive_adjoint_comp_self S.coboundaryHilbert

/-- **lem:L0-spectrum 第三条**:`ker L⁰ = ker δ⁰`(PiLp 2 / Hilbert layer)。

paper 完整链 `ker L⁰ = ker δ⁰ = H⁰(A)`:
- 本定理给 `ker L⁰ = ker δ⁰`(`coboundaryHilbert.ker`)
- `ker δ⁰ = H⁰(A) = globalSections` 在 plain Π layer 由 验收信号
  `globalSections_eq_ker_coboundary` (by `rfl`)给出;PiLp ↔ plain Π 桥接经
  `WithLp.linearEquiv 2`(`Coboundary.lean`)mechanically 等价。 -/
theorem sheafLaplacian0_ker_eq (S : CellularSheaf C stalk₀ stalk₁) :
    (sheafLaplacian0 S).ker = S.coboundaryHilbert.ker :=
  LinearMap.ker_adjoint_comp_self S.coboundaryHilbert

end CellularSheaf

end MRI.Cellular
