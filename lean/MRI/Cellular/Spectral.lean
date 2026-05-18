/-
  MRI.Cellular.Spectral — Spectral gap(γ_+ / Γ_+)+ sheaf bandwidth

  实现。informal cross-ref:paper/v0.1 §5
    def:spectral-gap (line 154-169) + def:sheafBW (line 38-50)。
  依赖:Coboundary.lean(CellularSheaf.coboundary)。

  paper §5 spectral-gap 双 def(line 161-164):
    γ_+(δᵏ) := inf{λ ∈ spec((δᵏ)*δᵏ) : λ > 0}
    Γ_+(δᵏ) := sup spec((δᵏ)*δᵏ) = ‖δᵏ‖²_op

  Lean 实施(design §10 refinement DC5):走 mathlib `LinearMap.singularValues`
  路径(spec form 的 *等价* form)— `sq_singularValues_fin` 桥接 lemma
  (SingularValues.lean line 127)直接提供 paper line 504-505 一行 mirror。
  operator norm identity `Γ_+ = ‖δ⁰‖²_op` 作为 *附加 lemma*(不阻挡主推理)。

  注:本文件 def 用于 paper §5 thm:strict-equality reduction 在 Sampling.lean
  完成(Samps 上 σ_min² / σ_max² 桥接 + 主定理)。
-/

import MRI.Cellular.Coboundary
import MRI.Cellular.Inner
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.Spectrum

namespace MRI.Cellular

open Module

section SpectralGap

variable {C : Complex1D} [Fintype C.Cells₀] [Fintype C.Cells₁]
  {stalk₀ : C.Cells₀ → Type*}
  [∀ v, NormedAddCommGroup (stalk₀ v)] [∀ v, InnerProductSpace ℂ (stalk₀ v)]
  [∀ v, FiniteDimensional ℂ (stalk₀ v)]
  {stalk₁ : C.Cells₁ → Type*}
  [∀ e, NormedAddCommGroup (stalk₁ e)] [∀ e, InnerProductSpace ℂ (stalk₁ e)]
  [∀ e, FiniteDimensional ℂ (stalk₁ e)]

/-- **Γ_+(δ⁰)**(paper §5 def:spectral-gap line 161-163):
    `:= sup spec((δ⁰)*δ⁰) = σ_max(δ⁰)²`。

    via mathlib `LinearMap.singularValues`(`antitone` → `singularValues 0 = max`)
    + `sq_singularValues_fin`(桥接到 `(δ⁰)*δ⁰` 的 max eigenvalue)。

    **Scope declaration**:paper def 第二条 identity `Γ_+ = ‖δ⁰‖_op²`
    经 mathlib `‖A* A‖ = ‖A‖²`(C* identity)+ symmetric operator
    spectrum identity 间接等价。本项目用 `singularValues 0 ^ 2` form 直接
    实现(paper 第一条 `sup spec` form),不独立 formalize paper 第二条
    operator-norm form;详见 `lean/CROSSREF.md` §5.2。下游 `sheafBW` 等
    lemma 仅依赖 `sup spec` form,不依赖 op-norm form。 -/
noncomputable def GammaPlus (S : CellularSheaf C stalk₀ stalk₁) : ℝ :=
  S.coboundaryHilbert.singularValues 0 ^ 2

/-- **γ_+(δ⁰)**(paper §5 def:spectral-gap line 158-160):
    `:= inf{λ ∈ spec((δ⁰)*δ⁰) : λ > 0}`,等价于 `σ_min(δ⁰)²` 在 paper 含义下
    (`σ_min` = 最小 *positive* singular value)。

    via mathlib `LinearMap.singularValues`(antitone,positive on `[0, rank δ⁰)`):
    `singularValues (rank δ⁰ - 1) = inf positive sv = σ_min`。

    Corner case `δ⁰ = 0`(`rank = 0`):`ℕ.sub: 0 - 1 = 0`,而 `T = 0 ⇒
    singularValues 0 = 0`,故 `gammaPlus = 0`,与 paper line 165-168 "left
    undefined; convention handled in def:sheafBW" 一致 — 形式化 verify by
    `gammaPlus_eq_zero_of_coboundaryHilbert_eq_zero`(§2)。 -/
noncomputable def gammaPlus (S : CellularSheaf C stalk₀ stalk₁) : ℝ :=
  S.coboundaryHilbert.singularValues
    (Module.finrank ℂ (LinearMap.range S.coboundaryHilbert) - 1) ^ 2

/-- **sheafBW(𝒜)**(paper §5 def:sheafBW line 38-50):
    `:= √(γ_+(δ⁰) / Γ_+(δ⁰))`(若 `δ⁰ ≠ 0`);**by convention `:= 0` if `δ⁰ = 0`**
    (paper line 53-58)。

    `δ⁰ = 0` 等价 `Γ_+ = 0`(因 `Γ_+ = ‖δ⁰‖²_op`)— Lean 中用 `GammaPlus = 0`
    检测 corner case;**该等价 iff 形式化 verify by
    `GammaPlus_eq_zero_iff_coboundaryHilbert_eq_zero`(§2)**(
    L2 audit 修补)。

    paper def equation 显式 carry `sheafBW ∈ [0, 1]`;**Lean general 上界
    verify by `sheafBW_le_one`(§2),下界 by `sheafBW_nonneg`(§1)**。 -/
noncomputable def sheafBW (S : CellularSheaf C stalk₀ stalk₁) : ℝ :=
  if GammaPlus S = 0 then 0
  else Real.sqrt (gammaPlus S / GammaPlus S)

-- =============================================================
-- §1 基本性质 lemmas
-- =============================================================

/-- `γ_+` 非负(squared singular value)。 -/
theorem gammaPlus_nonneg (S : CellularSheaf C stalk₀ stalk₁) : 0 ≤ gammaPlus S := by
  unfold gammaPlus; exact sq_nonneg _

/-- `Γ_+` 非负(squared singular value)。 -/
theorem GammaPlus_nonneg (S : CellularSheaf C stalk₀ stalk₁) : 0 ≤ GammaPlus S := by
  unfold GammaPlus; exact sq_nonneg _

/-- `sheafBW` 非负。 -/
theorem sheafBW_nonneg (S : CellularSheaf C stalk₀ stalk₁) : 0 ≤ sheafBW S := by
  unfold sheafBW
  split_ifs
  · exact le_refl 0
  · exact Real.sqrt_nonneg _

-- =============================================================
-- §2 退化 case + general bound bridge lemmas
--
--
--    paper §5 def:sheafBW 的 corner case "by convention sheafBW := 0
--    when δ⁰ ≡ 0" 在 Lean 用 `if GammaPlus S = 0` 拦截;paper convention
--    用 δ⁰ ≡ 0,Lean 用 Γ_+ = 0 — 二者等价但项目此前未独立 prove,本
--    section 形式化补桥。同时补 paper "$\sheafBW \in [0,1]$" 的 general
--    上界(下界 `sheafBW_nonneg` 已 §1)。
--
--    Scope declaration:paper def:spectral-gap 第二条 identity
--    `Γ_+ = ‖δ^k‖_op²` 经 mathlib `‖A* A‖ = ‖A‖²` + symmetric operator
--    spectrum identity 间接等价,本项目用 `singularValues 0 ^ 2` form 直接
--    实现,不独立 formalize paper 那条 operator-norm form(详见
--    `lean/CROSSREF.md`)。本 section 全部 lemma 不依赖该 identity。
-- =============================================================

/-- **paper §5 def:sheafBW corner case 的 Lean 形式 verify**:
    coboundaryHilbert = 0 ⇒ gammaPlus = 0。

    paper convention 当 `δ⁰ ≡ 0` 时 `γ_+` undefined / `sheafBW := 0`,
    Lean 用 `gammaPlus := singularValues (finrank range - 1) ^ 2` 在
    退化时取值 0(由 mathlib `singularValues_zero` 给:零算子 sv 全 0)。 -/
theorem gammaPlus_eq_zero_of_coboundaryHilbert_eq_zero
    (S : CellularSheaf C stalk₀ stalk₁) (h : S.coboundaryHilbert = 0) :
    gammaPlus S = 0 := by
  simp [gammaPlus, h, LinearMap.singularValues_zero]

/-- **paper §5 def:sheafBW corner case 的 Lean 形式 verify(F1 critical bridge)**:
    `Γ_+ = 0 ↔ δ⁰ = 0`。

    Lean `sheafBW` def 用 `if GammaPlus S = 0 then 0 else ...` 拦截退化 case,
    paper convention 用 `δ⁰ ≡ 0` 拦截 — 本 iff 是 Lean 检测条件等同 paper
    检测条件的形式化桥。

    Proof chain:
    `Γ_+ = singularValues 0 ^ 2 = 0`
    ↔ `singularValues 0 = 0`(by `sq_eq_zero_iff` + sv nonneg)
    ↔ `finrank range δ⁰ ≤ 0`(by mathlib `singularValues_eq_zero_iff_le_finrank_range`)
    ↔ `range δ⁰ = ⊥`(by `Submodule.finrank_eq_zero`,需 `FiniteDimensional`)
    ↔ `δ⁰ = 0`(by `LinearMap.range_eq_bot`) -/
theorem GammaPlus_eq_zero_iff_coboundaryHilbert_eq_zero
    (S : CellularSheaf C stalk₀ stalk₁) :
    GammaPlus S = 0 ↔ S.coboundaryHilbert = 0 := by
  unfold GammaPlus
  rw [sq_eq_zero_iff,
      LinearMap.singularValues_eq_zero_iff_le_finrank_range,
      Nat.le_zero, Submodule.finrank_eq_zero,
      LinearMap.range_eq_bot]

/-- **helper for `sheafBW_le_one`**:`γ_+ ≤ Γ_+`(由 mathlib
    `singularValues_antitone`:`singularValues (rank-1) ≤ singularValues 0`,
    平方保号)。 -/
theorem gammaPlus_le_GammaPlus (S : CellularSheaf C stalk₀ stalk₁) :
    gammaPlus S ≤ GammaPlus S := by
  unfold gammaPlus GammaPlus
  have h_nn : 0 ≤ S.coboundaryHilbert.singularValues
      (Module.finrank ℂ (LinearMap.range S.coboundaryHilbert) - 1) :=
    LinearMap.singularValues_nonneg _ _
  have h_anti : S.coboundaryHilbert.singularValues
      (Module.finrank ℂ (LinearMap.range S.coboundaryHilbert) - 1)
        ≤ S.coboundaryHilbert.singularValues 0 :=
    S.coboundaryHilbert.singularValues_antitone (Nat.zero_le _)
  exact pow_le_pow_left₀ h_nn h_anti 2

/-- **paper §5 def:sheafBW general 上界**:`sheafBW S ≤ 1`(对任意
    `CellularSheaf`)。

    paper def 的 equation 显式 carry `sheafBW ∈ [0, 1]`(line 48-49),
    Lean def 仅 `if-then-else` 给值,需要独立 lemma 形式化上界。`≥ 0` 已
    `sheafBW_nonneg` 给;本 lemma 补 `≤ 1`。

    Proof:分 Γ_+ = 0(=0 ≤ 1)/ ≠ 0(`γ_+ ≤ Γ_+` + sqrt 单调)两 branch。
    注意:本 lemma 对*所有* CellularSheaf 成立,*不仅* sampling sheaf;
    `strict_equality_with_interval` 已给 Samps specialization
    的 ∈ (0, 1]。 -/
theorem sheafBW_le_one (S : CellularSheaf C stalk₀ stalk₁) :
    sheafBW S ≤ 1 := by
  unfold sheafBW
  split_ifs with h
  · norm_num
  · have h_Γ_pos : 0 < GammaPlus S :=
      lt_of_le_of_ne (GammaPlus_nonneg S) (Ne.symm h)
    have h_div_le : gammaPlus S / GammaPlus S ≤ 1 :=
      (div_le_one h_Γ_pos).mpr (gammaPlus_le_GammaPlus S)
    calc Real.sqrt (gammaPlus S / GammaPlus S)
        ≤ Real.sqrt 1 := Real.sqrt_le_sqrt h_div_le
      _ = 1 := Real.sqrt_one

end SpectralGap

end MRI.Cellular
