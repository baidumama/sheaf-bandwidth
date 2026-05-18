/-
  MRI.Cellular.TriangleEquivalence — paper §3 Theorem 3.1 Triangle Equivalence


  .3 + 2.4 实现。informal cross-ref:
  paper/v0.1 §3 thm:triangle-equiv(line 53-86)+ proof of (a)⇔(c)(line 250-263)。

  本文件内容:
  - §1 Bridge `Injective samplingOp ↔ Injective samplingOpEuclidean`(WithLp)
  - §2 paper §3 (a) ↔ (c) Robinson sheaf form(specialized 到 Samps)
  - §3  paper §3 thm:triangle-equiv 三方等价主陈述(TFAE)

  依赖:
  - `Variational.lean`:(a)⇔(b) generic LinearMap form + `injective_iff_singularValues_last_pos`
  - `Sampling.lean`:samplingOp / samplingOpEuclidean / Samps
  - `SamplingSpectral.lean`:H0_vanishing_iff
-/

import MRI.Cellular.Variational
import MRI.Cellular.Sampling
import MRI.Cellular.SamplingSpectral

open Module

namespace MRI.Cellular

section TriangleEquivalence

variable {M : ℕ} (E : Type)
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

-- =============================================================
-- §1 Bridge:Injective samplingOp ↔ Injective samplingOpEuclidean
-- =============================================================

omit [FiniteDimensional ℂ E] in
/-- **Helper**:`Injective samplingOp ↔ Injective samplingOpEuclidean`。

    `samplingOpEuclidean = (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap ∘ₗ samplingOp`
    (`Sampling.lean` line 270-272 定义);WithLp.linearEquiv.symm 是 bijection,
    所以 Injective 等价。 -/
lemma injective_samplingOp_iff_injective_samplingOpEuclidean
    (eval : Fin M → E →L[ℂ] ℂ) :
    Function.Injective (samplingOp E eval) ↔
      Function.Injective (samplingOpEuclidean E eval) := by
  unfold samplingOpEuclidean
  rw [LinearMap.coe_comp]
  exact (Function.Injective.of_comp_iff
    (WithLp.linearEquiv 2 ℂ (Fin M → ℂ)).symm.injective _).symm

omit [FiniteDimensional ℂ E] in
/-- **paper §5 cor:H0-vanishing 第一条 statement**:
    `H^0(Samps) = ker A` 的 Lean 形态。

    paper 把 `H^0(Samps)` 通过 canonical isometry 视作 `V_B` 子空间然后等同于
    `ker A`。Lean 中两个 Submodule 在不同空间(`globalSections` 在 `∀ v, stalk0Samps`,
    `ker samplingOp` 在 `E`),通过 `Submodule.comap canonicalIsometryBackward`
    桥接表达精确等式。

    证明链:`globalSections = ker coboundary`(rfl-level by `globalSections_eq_ker_coboundary`)
    + `coboundary ∘ canonicalIsometryBackward = samplingOp`(prop:delta-equals-A)
    + `LinearMap.ker_comp`(mathlib)。

    paper-ref: `cor:H0-vanishing` 第一条 statement(`H^0(Samps) = ker A`)。 -/
theorem globalSections_comap_eq_ker_samplingOp (eval : Fin M → E →L[ℂ] ℂ) :
    Submodule.comap (canonicalIsometryBackward E) (Samps E eval).globalSections
      = LinearMap.ker (samplingOp E eval) := by
  rw [(Samps E eval).globalSections_eq_ker_coboundary,
      ← coboundary_eq_sampling_op E eval,
      LinearMap.ker_comp]

/-- **paper §5 cor:H0-vanishing 第二条 statement**:
    `H^0(Samps) = 0 ↔ σ_min(A) > 0`。

    完整链:
    `globalSections = ⊥`
      ↔ `Injective samplingOp`(by `H0_vanishing_iff`)
      ↔ `Injective samplingOpEuclidean`
        (by `injective_samplingOp_iff_injective_samplingOpEuclidean`)
      ↔ `0 < σ_min(samplingOpEuclidean)`
        (by `Variational.injective_iff_singularValues_last_pos`)

    paper-ref: `cor:H0-vanishing` 第二条 statement(`H^0(Samps) = 0 iff σ_min(A) > 0`)。 -/
theorem globalSections_eq_bot_iff_singularValues_last_pos
    [Nontrivial E] (eval : Fin M → E →L[ℂ] ℂ) (hn0 : 0 < finrank ℂ E) :
    (Samps E eval).globalSections = ⊥ ↔
      0 < (samplingOpEuclidean E eval).singularValues (finrank ℂ E - 1) := by
  rw [H0_vanishing_iff E eval,
      injective_samplingOp_iff_injective_samplingOpEuclidean E eval,
      LinearMap.injective_iff_singularValues_last_pos _ hn0]

-- =============================================================
-- §2 paper §3 (a) ↔ (c) Robinson sheaf form
-- =============================================================

/-- ** paper §3 Triangle Equivalence (a) ↔ (c)**(.3,
    Robinson sheaf form)。

    paper §3 line 250-263 mirror:
    - (a) `σ_min(A) ≥ τ · σ_max(A)`(FEEC singular value form)
    - (c) `H^0(Samps) = 0 ∧ sheafBW_cand(Samps) ≥ τ`(Robinson sheaf form)

    `sheafBW_cand(Samps) := σ_min(A) / σ_max(A)`(paper line 232-237 candidate
    def);本 Lean form 直接展开为 ratio,绕开 几何 `sheafBW`(Theorem
    5.3 strict equality 在 Samps 上两者重合,但 candidate def 本身简单 = ratio)。

    证明骨架(paper line 250-263):
    - `H^0 = 0 ↔ Injective A ↔ σ_min > 0`

    - `σ_min/σ_max ≥ τ ↔ σ_min ≥ τ σ_max`(σ_max > 0 + `le_div_iff`)
    - 合一 ↔ (a)。

    注:`_hτ_le : τ ≤ 1` 是 paper assumption,但 (a)⇔(c) 证明不需要 — 诚实标注。

    paper-ref: `thm:triangle-equiv` (a)⇔(c)(详见 `lean/CROSSREF.md`)。 -/
theorem triangle_equiv_a_iff_c
    (eval : Fin M → E →L[ℂ] ℂ) [Nontrivial E] (hn0 : 0 < finrank ℂ E)
    {τ : ℝ} (hτ_pos : 0 < τ) (_hτ_le : τ ≤ 1)
    (hsmax_pos : 0 < (samplingOpEuclidean E eval).singularValues 0) :
    ((samplingOpEuclidean E eval).singularValues (finrank ℂ E - 1)
        ≥ τ * (samplingOpEuclidean E eval).singularValues 0)
      ↔
    ((Samps E eval).globalSections = ⊥
      ∧ (samplingOpEuclidean E eval).singularValues (finrank ℂ E - 1) /
          (samplingOpEuclidean E eval).singularValues 0 ≥ τ) := by
  set A := samplingOpEuclidean E eval with hA_def
  -- 桥 1:H^0 = ⊥ ↔ 0 < σ_min(A)
  have h_H0_iff_smin :
      (Samps E eval).globalSections = ⊥ ↔ 0 < A.singularValues (finrank ℂ E - 1) := by
    rw [H0_vanishing_iff E eval,
        injective_samplingOp_iff_injective_samplingOpEuclidean E eval,
        ← hA_def, A.injective_iff_singularValues_last_pos hn0]
  -- 桥 2:σ_min/σ_max ≥ τ ↔ τ σ_max ≤ σ_min(σ_max > 0)
  have h_ratio_iff :
      A.singularValues (finrank ℂ E - 1) / A.singularValues 0 ≥ τ
        ↔ τ * A.singularValues 0 ≤ A.singularValues (finrank ℂ E - 1) := by
    rw [ge_iff_le, le_div_iff₀ hsmax_pos]
  constructor
  -- (a) ⇒ (c)
  · intro ha
    have hsmin_pos : 0 < A.singularValues (finrank ℂ E - 1) :=
      lt_of_lt_of_le (mul_pos hτ_pos hsmax_pos) ha
    exact ⟨h_H0_iff_smin.mpr hsmin_pos, h_ratio_iff.mpr ha⟩
  -- (c) ⇒ (a)
  · rintro ⟨_, h_c2⟩
    exact h_ratio_iff.mp h_c2

-- =============================================================
-- §3  paper §3 thm:triangle-equiv 三方等价主陈述(TFAE)
-- =============================================================

open List in
/-- ** paper §3 thm:triangle-equiv 主陈述**(.4,
    Triangle Equivalence Theorem)。

    paper §3 line 53-86 mirror,三方等价:
    - (a) FEEC singular value form:`σ_min(A) ≥ τ σ_max(A)`
    - (b) Hodge-spectrum Riesz form:`∃ α β, 0 < α ≤ β, β/α ≤ 1/τ, ∀ c ≠ 0,
                                       α‖c‖ ≤ ‖A c‖ ≤ β‖c‖`
    - (c) Robinson sheaf form:`H^0(Samps) = 0 ∧ sheafBW_cand(Samps) ≥ τ`

    `A := samplingOpEuclidean E eval`(paper sampling operator)。

    证明 = (a)⇔(b)(`Variational.triangle_equiv_a_iff_b` sub-step 2.2)
        + (a)⇔(c)(`triangle_equiv_a_iff_c` sub-step 2.3)
        + `tfae_finish` 拼接(transitive (b)⇔(c) 自动)。

    ****:lake build PASS / 0 sorry / 0 admitted 。
    paper §3 。 -/
theorem triangle_equivalence
    (eval : Fin M → E →L[ℂ] ℂ) [Nontrivial E] (hn0 : 0 < finrank ℂ E)
    {τ : ℝ} (hτ_pos : 0 < τ) (hτ_le : τ ≤ 1)
    (hsmax_pos : 0 < (samplingOpEuclidean E eval).singularValues 0) :
    List.TFAE
      [-- (a) FEEC singular value form
        (samplingOpEuclidean E eval).singularValues (finrank ℂ E - 1)
          ≥ τ * (samplingOpEuclidean E eval).singularValues 0,
       -- (b) Hodge-spectrum Riesz form
        ∃ α β : ℝ, 0 < α ∧ α ≤ β ∧ β / α ≤ 1 / τ ∧
          ∀ c : E, c ≠ 0 → α * ‖c‖ ≤ ‖samplingOpEuclidean E eval c‖
            ∧ ‖samplingOpEuclidean E eval c‖ ≤ β * ‖c‖,
       -- (c) Robinson sheaf form
        (Samps E eval).globalSections = ⊥
          ∧ (samplingOpEuclidean E eval).singularValues (finrank ℂ E - 1) /
              (samplingOpEuclidean E eval).singularValues 0 ≥ τ
      ] := by
  tfae_have 1 ↔ 2 :=
    (samplingOpEuclidean E eval).triangle_equiv_a_iff_b hn0 hτ_pos hτ_le hsmax_pos
  tfae_have 1 ↔ 3 :=
    triangle_equiv_a_iff_c E eval hn0 hτ_pos hτ_le hsmax_pos
  tfae_finish

end TriangleEquivalence

end MRI.Cellular
