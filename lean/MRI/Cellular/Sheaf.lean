/-
  MRI.Cellular.Sheaf — Cellular sheaf 主结构(generic per-cell stalks)

  重写(原 uniform-stalk 形态升级)。
  informal cross-ref:paper/v0.1 §5 def:finite-dim-sheaf + def:sampling-sheaf。
  依赖:Complex.lean(Complex1D)。

  注:7.2 起 stalks 为 per-cell 异型 — `stalk₀ : Cells₀ → Type*` /
  `stalk₁ : Cells₁ → Type*`,每个 cell 独立配 ℂ-Hilbert 结构。
  这是 paper §5 sampling sheaf(σ_B = V_B / σ_∞ = 0 / τ_i = ℂ)的直接需求,
  不可由 7.1 uniform 形态承载。
-/

import MRI.Cellular.Complex

namespace MRI.Cellular

/-- Cellular sheaf(generic per-cell stalks):

* `stalk₀ v : Type*` 给每个 0-cell `v` 配 ℂ-Hilbert space;
* `stalk₁ e : Type*` 给每个 1-cell `e` 配 ℂ-Hilbert space;
* 每个 1-cell `e` 配两条 continuous linear 限制:
  * `restrict₀ e : stalk₀ (face₀ e) →L[ℂ] stalk₁ e` — paper σ_B 端(incidence +1);
  * `restrict₁ e : stalk₀ (face₁ e) →L[ℂ] stalk₁ e` — paper σ_∞ 端(incidence -1)。

两者之差 ↦ coboundary(`Coboundary.lean`)。

Cross-ref:`paper/v0.1` §5 def:finite-dim-sheaf + def:sampling-sheaf。
-/
structure CellularSheaf
    (C : Complex1D)
    (stalk₀ : C.Cells₀ → Type*)
    (stalk₁ : C.Cells₁ → Type*)
    [∀ v, NormedAddCommGroup (stalk₀ v)] [∀ v, InnerProductSpace ℂ (stalk₀ v)]
    [∀ e, NormedAddCommGroup (stalk₁ e)] [∀ e, InnerProductSpace ℂ (stalk₁ e)] where
  restrict₀ : (e : C.Cells₁) → stalk₀ (C.face₀ e) →L[ℂ] stalk₁ e
  restrict₁ : (e : C.Cells₁) → stalk₀ (C.face₁ e) →L[ℂ] stalk₁ e

/-- Trivial well-formed witness(7.1 uniform 例 用 constant stalk 函数 recover):
所有 stalks = ℂ,restrictions 均为 identity。证明 generic structure 上 instance
能自动 derive 且数据可填。`noncomputable` 因 ℂ 的 normed-space instance 依赖
`Complex.abs`(unconstructive),不影响形式化推理。 -/
noncomputable example (C : Complex1D) :
    CellularSheaf C (fun _ : C.Cells₀ => ℂ) (fun _ : C.Cells₁ => ℂ) where
  restrict₀ := fun _ => ContinuousLinearMap.id ℂ ℂ
  restrict₁ := fun _ => ContinuousLinearMap.id ℂ ℂ

end MRI.Cellular
