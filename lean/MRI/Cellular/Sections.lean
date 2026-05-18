/-
  MRI.Cellular.Sections — globalSections(discrepancy 的 kernel)

  适配(原 7.1 uniform-stalk 形态升级到 generic per-cell stalks)。
  informal cross-ref:paper/v0.1 §3 (F1) + §5 def:cochain-space。
  依赖:Sheaf.lean(CellularSheaf generic)。
-/

import MRI.Cellular.Sheaf

namespace MRI.Cellular

variable {C : Complex1D}
  {stalk₀ : C.Cells₀ → Type*}
  [∀ v, NormedAddCommGroup (stalk₀ v)] [∀ v, InnerProductSpace ℂ (stalk₀ v)]
  {stalk₁ : C.Cells₁ → Type*}
  [∀ e, NormedAddCommGroup (stalk₁ e)] [∀ e, InnerProductSpace ℂ (stalk₁ e)]

namespace CellularSheaf

/-- Discrepancy linear map:0-cochain `s : ∀ v, stalk₀ v` 映到 1-cochain
`e ↦ restrict₀ e (s (face₀ e)) - restrict₁ e (s (face₁ e))`。

0-cochain 是 *global section* iff 它在此 map 的 kernel 中。 -/
noncomputable def discrepancy (S : CellularSheaf C stalk₀ stalk₁) :
    (∀ v, stalk₀ v) →ₗ[ℂ] (∀ e, stalk₁ e) where
  toFun s := fun e => S.restrict₀ e (s (C.face₀ e)) - S.restrict₁ e (s (C.face₁ e))
  map_add' s t := by ext e; simp [map_add]; abel
  map_smul' c s := by ext e; simp [map_smul, smul_sub]

/-- Global sections of a cellular sheaf:cocycles 在每条 1-cell 上 restrictions 一致。

形式:`s ∈ globalSections S` ⇔ `∀ e, restrict₀ e (s (face₀ e)) = restrict₁ e (s (face₁ e))`。

定义:`discrepancy` 的 kernel,自动是 ℂ-submodule。 -/
noncomputable def globalSections (S : CellularSheaf C stalk₀ stalk₁) :
    Submodule ℂ (∀ v, stalk₀ v) :=
  LinearMap.ker S.discrepancy

end CellularSheaf

end MRI.Cellular
