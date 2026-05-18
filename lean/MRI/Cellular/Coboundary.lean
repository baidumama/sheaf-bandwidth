/-
  MRI.Cellular.Coboundary — Coboundary 算子 + 第一个真定理

  适配(原 7.1 uniform-stalk 形态升级到 generic per-cell stalks)。
  informal cross-ref:paper/v0.1 §3 (F2) + §5 def:coboundary + prop:delta-equals-A。
  依赖:Sections.lean(discrepancy / globalSections)。

  接口定位:
  - 本层承载 *cochain 数据 + globalSections kernel 形态*。LinearMap 与 paper §5
    def:coboundary 在 *cochain 数据* 层完全对齐;`(δ⁰)*δ⁰` spectrum 等 spectral
    结构(paper §5 thm:strict-equality / def:spectral-gap)是 的职责,
    届时由 ContinuousLinearMap 承载 operator norm + spectrum。
  - 此命名固化 `globalSections = ker coboundary` 的 rfl 形态 —
    7.1 验收信号在 generic stalks 下机械保持。

  符号约定(paper §5 锁定):
  - `face₀` 对应 incidence +1 endpoint(paper σ_B,principal 0-cell)
  - `face₁` 对应 incidence -1 endpoint(paper σ_∞,auxiliary basepoint)
  - 故 coboundary = (+1) restrict₀ + (-1) restrict₁ = restrict₀ - restrict₁
-/

import MRI.Cellular.Sections
import MRI.Cellular.Inner

namespace MRI.Cellular

namespace CellularSheaf

variable {C : Complex1D}
  {stalk₀ : C.Cells₀ → Type*}
  [∀ v, NormedAddCommGroup (stalk₀ v)] [∀ v, InnerProductSpace ℂ (stalk₀ v)]
  {stalk₁ : C.Cells₁ → Type*}
  [∀ e, NormedAddCommGroup (stalk₁ e)] [∀ e, InnerProductSpace ℂ (stalk₁ e)]

/-- Coboundary 算子:`coboundary S` 是
`discrepancy S` 的显式命名 alias,与 paper §5 def:coboundary 在 cochain 数据
层完全对齐。

形式:`(coboundary S s) e = restrict₀ e (s (face₀ e)) - restrict₁ e (s (face₁ e))`。 -/
noncomputable def coboundary (S : CellularSheaf C stalk₀ stalk₁) :
    (∀ v, stalk₀ v) →ₗ[ℂ] (∀ e, stalk₁ e) :=
  S.discrepancy

/-- **第一个真定理**:
cellular sheaf 的全局截面 ≡ coboundary 的 kernel。

形式:`S.globalSections = LinearMap.ker S.coboundary`。

证:by `rfl` — `globalSections` 定义为 `LinearMap.ker discrepancy`,
`coboundary` definitionally = `discrepancy`。 -/
theorem globalSections_eq_ker_coboundary (S : CellularSheaf C stalk₀ stalk₁) :
    S.globalSections = LinearMap.ker S.coboundary := rfl

/-- **Hilbert-layer coboundary**:`CellularSheaf.coboundary`
(operator 层 plain Π)通过 `WithLp.linearEquiv 2` 桥接到 PiLp 2 wrapper
(`Cochain0 → Cochain1`)。

paper §5 def:spectral-gap 在 Hilbert 层定义,需要 InnerProductSpace 结构;
本 def 提供 `singularValues / adjoint / spectrum` 等谱论 API 在 PiLp 2 wrapper
上解析所需的 Cochain0/1 wrapper type。

operator-layer `coboundary` 与本 def 经 `WithLp.linearEquiv` 桥接 mechanically 等价。

paper-ref: `def:coboundary`(Hilbert layer specialization;详见 `lean/CROSSREF.md`)。 -/
noncomputable def coboundaryHilbert [Fintype C.Cells₀] [Fintype C.Cells₁]
    (S : CellularSheaf C stalk₀ stalk₁) :
    Cochain0 C stalk₀ →ₗ[ℂ] Cochain1 C stalk₁ :=
  (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap ∘ₗ S.coboundary ∘ₗ
    (WithLp.linearEquiv 2 ℂ _).toLinearMap

end CellularSheaf

end MRI.Cellular
