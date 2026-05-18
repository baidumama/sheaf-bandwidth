/-
  MRI.Cellular.Inner — 0Cochain / 1Cochain ℓ² Hilbert 结构(via PiLp 2)

  适配(原 7.1 uniform-stalk 形态升级到 generic per-cell stalks)。
  informal cross-ref:paper/v0.1 §3 + §5 def:cochain-space。
  依赖:Sheaf.lean(CellularSheaf generic)。

  关键设计:用 `abbrev`(reducible)而非 `def`,使 mathlib4 type-class resolution
  能 unfold 看到 `PiLp 2`,自动 derive InnerProductSpace / NormedAddCommGroup 实例
  (即使 stalks 异型也能逐 component 解析)。
-/

import MRI.Cellular.Sheaf

namespace MRI.Cellular

/-- 0-cochain Hilbert space:ℓ² product 跨 0-cells 的(可异型)stalks。

形式:`Cochain0 C stalk₀ ≡ PiLp 2 (fun v : C.Cells₀ => stalk₀ v)`。
要求 `C.Cells₀ : Fintype`(paper §5 双 0-cell 模型 = `Fin 2` 或 `XsampVert`)。 -/
abbrev Cochain0 (C : Complex1D) [Fintype C.Cells₀]
    (stalk₀ : C.Cells₀ → Type*)
    [∀ v, NormedAddCommGroup (stalk₀ v)] [∀ v, InnerProductSpace ℂ (stalk₀ v)] : Type _ :=
  PiLp 2 (fun v : C.Cells₀ => stalk₀ v)

/-- 1-cochain Hilbert space:ℓ² product 跨 1-cells 的(可异型)stalks。

要求 `C.Cells₁ : Fintype`(paper §5 = `Fin M`,M = 采样总数)。 -/
abbrev Cochain1 (C : Complex1D) [Fintype C.Cells₁]
    (stalk₁ : C.Cells₁ → Type*)
    [∀ e, NormedAddCommGroup (stalk₁ e)] [∀ e, InnerProductSpace ℂ (stalk₁ e)] : Type _ :=
  PiLp 2 (fun e : C.Cells₁ => stalk₁ e)

/-- Sanity:`Cochain0 C stalk₀` 在 generic stalks 下仍自动 derive `InnerProductSpace ℂ`。 -/
noncomputable example (C : Complex1D) [Fintype C.Cells₀]
    (stalk₀ : C.Cells₀ → Type*)
    [∀ v, NormedAddCommGroup (stalk₀ v)] [∀ v, InnerProductSpace ℂ (stalk₀ v)] :
    InnerProductSpace ℂ (Cochain0 C stalk₀) := inferInstance

/-- Sanity:`Cochain1 C stalk₁` 同理。 -/
noncomputable example (C : Complex1D) [Fintype C.Cells₁]
    (stalk₁ : C.Cells₁ → Type*)
    [∀ e, NormedAddCommGroup (stalk₁ e)] [∀ e, InnerProductSpace ℂ (stalk₁ e)] :
    InnerProductSpace ℂ (Cochain1 C stalk₁) := inferInstance

end MRI.Cellular
