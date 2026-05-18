/-
  MRI.Cellular.SamplingSpectral — Spectral analysis of Samps sheaf

  实现。informal cross-ref:paper/v0.1 §5
    Theorem 5.3 strict equality + cor:H0-vanishing(line 481-537);
    spectrum-via-conjugation:line 502-505 + line 213-225 unitary
    invariance pattern。
  依赖:Sampling.lean(Samps + coboundaryHilbert_eq_samplingOpEuclidean)
       + Spectral.lean(gammaPlus / GammaPlus / sheafBW general)。

  — spectrum-via-conjugation:
    通用 `LinearMap.singularValues_comp_linearIsometryEquiv` 桥接 +
    `singularValues_coboundaryHilbert_eq_samplingOpEuclidean`(Samps 上 form)。
-/

import MRI.Cellular.Sampling
import MRI.Cellular.Spectral

open Module

-- =============================================================
-- §1 General helper(LinearMap namespace,可上游 mathlib pattern):
--    singular values are preserved by pre-composition with a linear
--    isometric equivalence(unitary invariance of singular values,
--    paper §5 line 502-505 mirror)
-- =============================================================

namespace LinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
  {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [FiniteDimensional 𝕜 G]

/-- Pre-composition with a linear isometric equivalence preserves singular
    values(`σ_l(T ∘ V) = σ_l(T)` for `V : E ≃ₗᵢ F`)。

    paper §5 line 502-505 unitary invariance pattern。

    Proof outline:
    1. `adjoint(T ∘ V) ∘ (T ∘ V) = V.symm ∘ (T.adjoint ∘ T) ∘ V`
       (via `adjoint_comp` + `LinearIsometryEquiv.adjoint_toLinearMap_eq_symm`)
    2. RHS = `V.symm.toLinearEquiv.conj (T.adjoint ∘ T)`(by `LinearEquiv.conj_apply_apply`)
    3. `charpoly` 在 conjugation 下保持(`LinearEquiv.charpoly_conj`)
    4. 故 `IsSymmetric.eigenvalues` 相等(`eigenvalues_eq_eigenvalues_iff`)
    5. `singularValues = √ eigenvalues`(`singularValues_of_lt` + tail 0 via
       `singularValues_of_finrank_le`)— pointwise 相等。 -/
theorem singularValues_comp_linearIsometryEquiv
    (T : F →ₗ[𝕜] G) (V : E ≃ₗᵢ[𝕜] F) :
    (T ∘ₗ V.toLinearMap).singularValues = T.singularValues := by
  set n := finrank 𝕜 F
  have hn_E : finrank 𝕜 E = n := V.toLinearEquiv.finrank_eq
  have hn_F : finrank 𝕜 F = n := rfl
  -- Step 1+2: adjoint(T ∘ V) ∘ (T ∘ V) = V.symm.conj (adjoint T ∘ T)
  have h_adj_eq :
      LinearMap.adjoint (T ∘ₗ V.toLinearMap) ∘ₗ (T ∘ₗ V.toLinearMap)
        = V.symm.toLinearEquiv.conj (LinearMap.adjoint T ∘ₗ T) := by
    ext x
    simp [LinearMap.adjoint_comp, LinearIsometryEquiv.adjoint_toLinearMap_eq_symm,
          LinearEquiv.conj_apply_apply]
  -- Step 3: charpoly equality via LinearEquiv.charpoly_conj
  have h_charpoly :
      (LinearMap.adjoint (T ∘ₗ V.toLinearMap) ∘ₗ (T ∘ₗ V.toLinearMap)).charpoly
        = (LinearMap.adjoint T ∘ₗ T).charpoly := by
    rw [h_adj_eq]
    exact V.symm.toLinearEquiv.charpoly_conj _
  -- Step 4: eigenvalues equality via eigenvalues_eq_eigenvalues_iff
  have h_eig :
      (T ∘ₗ V.toLinearMap).isSymmetric_adjoint_comp_self.eigenvalues hn_E
        = T.isSymmetric_adjoint_comp_self.eigenvalues hn_F :=
    ((T ∘ₗ V.toLinearMap).isSymmetric_adjoint_comp_self.eigenvalues_eq_eigenvalues_iff
      hn_E T.isSymmetric_adjoint_comp_self hn_F).mpr h_charpoly
  -- Step 5: pointwise equality of singularValues : ℕ →₀ ℝ
  ext i
  by_cases hi : i < n
  · rw [(T ∘ₗ V.toLinearMap).singularValues_of_lt hn_E hi,
        T.singularValues_of_lt hn_F hi, h_eig]
  · push Not at hi
    rw [(T ∘ₗ V.toLinearMap).singularValues_of_finrank_le (hn_E ▸ hi),
        T.singularValues_of_finrank_le (hn_F ▸ hi)]

/-- Post-composition with a linear isometric equivalence preserves singular
    values(`σ_l(V ∘ T) = σ_l(T)` for `V : F ≃ₗᵢ G`)。

    paper §5 line 502-505 unitary invariance pattern 的 mirror form(本 lemma 是
    *post-compose*,与上方 `singularValues_comp_linearIsometryEquiv` 配对的 pre-compose)。
    用于 `prop:sheafBW-unitary` 证明。

    Proof:
    1. `adjoint(V ∘ T) ∘ (V ∘ T) = T.adjoint ∘ V.symm ∘ V ∘ T = T.adjoint ∘ T`
       (V isometry → `V.symm ∘ V = id` → adjoint_comp_self **直接相等**,
       不需要 conjugation)
    2. charpoly 相等(operator 相等)→ eigenvalues 相等 → singularValues 相等

     mathlib PR 候选。 -/
theorem singularValues_linearIsometryEquiv_comp
    (T : E →ₗ[𝕜] F) (V : F ≃ₗᵢ[𝕜] G) :
    (V.toLinearMap ∘ₗ T).singularValues = T.singularValues := by
  set n := finrank 𝕜 E
  have hn_E : finrank 𝕜 E = n := rfl
  -- Step 1: adjoint(V ∘ T) ∘ (V ∘ T) = T.adjoint ∘ T(V isometry → V.symm ∘ V = id)
  have h_adj_eq :
      LinearMap.adjoint (V.toLinearMap ∘ₗ T) ∘ₗ (V.toLinearMap ∘ₗ T)
        = LinearMap.adjoint T ∘ₗ T := by
    rw [LinearMap.adjoint_comp, LinearIsometryEquiv.adjoint_toLinearMap_eq_symm]
    ext x
    simp
  -- Step 2: charpoly 相等
  have h_charpoly :
      (LinearMap.adjoint (V.toLinearMap ∘ₗ T) ∘ₗ (V.toLinearMap ∘ₗ T)).charpoly
        = (LinearMap.adjoint T ∘ₗ T).charpoly := by
    rw [h_adj_eq]
  -- Step 3: eigenvalues 相等
  have h_eig :
      (V.toLinearMap ∘ₗ T).isSymmetric_adjoint_comp_self.eigenvalues hn_E
        = T.isSymmetric_adjoint_comp_self.eigenvalues hn_E :=
    ((V.toLinearMap ∘ₗ T).isSymmetric_adjoint_comp_self.eigenvalues_eq_eigenvalues_iff
      hn_E T.isSymmetric_adjoint_comp_self hn_E).mpr h_charpoly
  -- Step 4: pointwise singularValues 相等
  ext i
  by_cases hi : i < n
  · rw [(V.toLinearMap ∘ₗ T).singularValues_of_lt hn_E hi,
        T.singularValues_of_lt hn_E hi, h_eig]
  · push Not at hi
    rw [(V.toLinearMap ∘ₗ T).singularValues_of_finrank_le (hn_E ▸ hi),
        T.singularValues_of_finrank_le (hn_E ▸ hi)]

end LinearMap

namespace MRI.Cellular

-- =============================================================
-- §2 — Samps coboundaryHilbert vs samplingOpEuclidean
--    singular values 完全相等(via §1 桥接)
-- =============================================================

section SamplingSpectral

variable {M : ℕ} (E : Type)
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- σ_B stalk(`E`)+ σ_∞ stalk(`EuclideanSpace ℂ (Fin 0)`)均 FiniteDim —
    使 `(Samps E eval).coboundaryHilbert.singularValues` 解析所需。 -/
instance (v : XsampVert) : FiniteDimensional ℂ (stalk0Samps E v) := by
  cases v <;> infer_instance

/-- **paper §5 line 502-505**(spectrum-via-conjugation):

    Samps 的 Hilbert-layer coboundary `δ⁰` 与 sampling operator
    `A : E → EuclideanSpace ℂ (Fin M)` 通过 canonical isometry `ι_B`
    conjugation 后,**singular values 完全相等**(unitary invariance)。

    提供 `(Samps E eval).coboundaryHilbert ∘ₗ ι_B.symm.toLinearMap
    = samplingOpEuclidean`;本 lemma 通过通用 §1
    `singularValues_comp_linearIsometryEquiv` 桥接。

    用于 `gammaPlus(Samps) = σ_min(A)²` / `GammaPlus(Samps) = σ_max(A)²`
    桥接到 mathlib `LinearMap.sq_singularValues_fin`(SingularValues.lean line 127)。 -/
theorem singularValues_coboundaryHilbert_eq_samplingOpEuclidean
    (eval : Fin M → E →L[ℂ] ℂ) :
    (samplingOpEuclidean E eval).singularValues
      = (Samps E eval).coboundaryHilbert.singularValues := by
  rw [← coboundaryHilbert_eq_samplingOpEuclidean E eval]
  exact LinearMap.singularValues_comp_linearIsometryEquiv _ _

-- =============================================================
-- §3 — gammaPlus / GammaPlus on Samps via singular values of A
--    paper §5 line 504-513(Thm 5.3 proof 第 (2)(3) 步)
-- =============================================================

omit [FiniteDimensional ℂ E] in
/-- `range samplingOpEuclidean = range coboundaryHilbert`(conjugation +
    `range_comp_of_range_eq_top`,因 `ι_B.symm` 是 LinearIsometryEquiv 故 surjective)。

    用于 `gammaPlus` index 桥接(`finrank ℂ (range ·)`)。

    注:本 lemma 仅需 surjectivity,不依赖 `FiniteDimensional ℂ E`(`omit` 标注)。 -/
theorem range_samplingOpEuclidean_eq_range_coboundaryHilbert
    (eval : Fin M → E →L[ℂ] ℂ) :
    LinearMap.range (samplingOpEuclidean E eval)
      = LinearMap.range (Samps E eval).coboundaryHilbert := by
  rw [← coboundaryHilbert_eq_samplingOpEuclidean E eval]
  exact LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr (canonicalLinearIsometryEquiv E).symm.surjective)

omit [FiniteDimensional ℂ E] in
/-- `finrank ℂ (range samplingOpEuclidean) = finrank ℂ (range coboundaryHilbert)`
    — gammaPlus index `rank - 1` 桥接必需。 -/
theorem finrank_range_samplingOpEuclidean_eq_finrank_range_coboundaryHilbert
    (eval : Fin M → E →L[ℂ] ℂ) :
    finrank ℂ (LinearMap.range (samplingOpEuclidean E eval))
      = finrank ℂ (LinearMap.range (Samps E eval).coboundaryHilbert) := by
  rw [range_samplingOpEuclidean_eq_range_coboundaryHilbert]

/-- **paper §5 line 504-513**(Thm 5.3 proof 第 (3) 步 — `Γ_+(δ⁰) = σ_max(A)²`):

    `Samps E eval` 的 `GammaPlus` 等于 `samplingOpEuclidean E eval` 的最大
    singular value 的平方(即 `σ_max(A)²` — `singularValues 0` 因 antitone)。

    Proof:直接 unfold + singularValues 函数等。 -/
theorem GammaPlus_Samps_eq_singularValues_zero_sq (eval : Fin M → E →L[ℂ] ℂ) :
    GammaPlus (Samps E eval)
      = (samplingOpEuclidean E eval).singularValues 0 ^ 2 := by
  unfold GammaPlus
  rw [← singularValues_coboundaryHilbert_eq_samplingOpEuclidean]

/-- **paper §5 line 504-513**(Thm 5.3 proof 第 (2) 步 — `γ_+(δ⁰) = σ_min(A)²`):

    `Samps E eval` 的 `gammaPlus` 等于 `samplingOpEuclidean E eval` 在 `rank - 1`
    位置的 singular value 的平方(即 `σ_min(A)²` — 最小非零 singular value,
    `singularValues_pos_iff_lt_finrank_range` 在 `[0, rank)` 上 positive)。

    Proof:singularValues 函数等 + range 相等 ⇒ rank 相等。 -/
theorem gammaPlus_Samps_eq_singularValues_rank_pred_sq (eval : Fin M → E →L[ℂ] ℂ) :
    gammaPlus (Samps E eval)
      = (samplingOpEuclidean E eval).singularValues
          (finrank ℂ (LinearMap.range (samplingOpEuclidean E eval)) - 1) ^ 2 := by
  unfold gammaPlus
  rw [← singularValues_coboundaryHilbert_eq_samplingOpEuclidean,
      finrank_range_samplingOpEuclidean_eq_finrank_range_coboundaryHilbert]

-- =============================================================
-- §4 — sheafBW(Samps) = σ_min(A) / σ_max(A)
--    paper §5 line 514-520(Thm 5.3 proof 第 (4) 步)
-- =============================================================

/-- **paper §5 line 514-520**(— `sheafBW(Samps) = σ_min(A)/σ_max(A)`
    under `σ_max(A) ≠ 0` 假设):

    Samps 的 `sheafBW`(= `√(γ_+/Γ_+)`)在 `σ_max(A) = singularValues 0 ≠ 0`
    的非退化假设下,等于 `σ_min(A) / σ_max(A) = singularValues(rank-1) / singularValues 0`。

    Proof:
    - `unfold sheafBW` → `if GammaPlus = 0 then 0 else √(gammaPlus/GammaPlus)`
    - 重写 `GammaPlus = σ_max²` / `gammaPlus = σ_min²`
    - `σ_max ≠ 0 ⇒ σ_max² ≠ 0` (`pow_ne_zero`)→ 走 else 分支
    - `√(σ_min²/σ_max²) = √((σ_min/σ_max)²) = σ_min/σ_max`(`div_pow` + `Real.sqrt_sq`
      with `singularValues_nonneg`)。 -/
theorem sheafBW_Samps_eq_singularValues_div (eval : Fin M → E →L[ℂ] ℂ)
    (h_max : (samplingOpEuclidean E eval).singularValues 0 ≠ 0) :
    sheafBW (Samps E eval) =
      (samplingOpEuclidean E eval).singularValues
          (finrank ℂ (LinearMap.range (samplingOpEuclidean E eval)) - 1) /
        (samplingOpEuclidean E eval).singularValues 0 := by
  unfold sheafBW
  rw [GammaPlus_Samps_eq_singularValues_zero_sq E eval,
      gammaPlus_Samps_eq_singularValues_rank_pred_sq E eval]
  have h_sq : (samplingOpEuclidean E eval).singularValues 0 ^ 2 ≠ 0 := pow_ne_zero 2 h_max
  rw [if_neg h_sq, ← div_pow,
      Real.sqrt_sq (div_nonneg ((samplingOpEuclidean E eval).singularValues_nonneg _)
                                ((samplingOpEuclidean E eval).singularValues_nonneg _))]

-- =============================================================
-- §5 —  Theorem 5.3 strict equality(single statement)
--    paper §5 line 481-525:
-- =============================================================

/-- ** paper §5 Theorem 5.3 strict equality**:

    在 sampling operator `A : E → ℂ^M` 满秩(`σ_min(A) > 0`,等价 `A` injective,
    等价 `H^0(Samps) = 0`)的假设下:
    1. `sheafBW(Samps) = σ_min(A) / σ_max(A)`
    2. `sheafBW(Samps) ∈ (0, 1]`

    Proof (this single statement bundles paper §5 line 504-525 informal 4-step proof):
    - Step (1) — `δ⁰ = A` (canonical isometry conjugation):
      `coboundaryHilbert_eq_samplingOpEuclidean`
    - Steps (2)(3) — `spec((δ⁰)*δ⁰) = spec(A*A) = {σ_l(A)²}`:
      `singularValues_coboundaryHilbert_eq_samplingOpEuclidean`
    - Step (3') — `γ_+(δ⁰) = σ_min(A)²` / `Γ_+(δ⁰) = σ_max(A)²`:
      `gammaPlus_Samps_eq_*` / `GammaPlus_Samps_eq_*`
    - Step (4) — `sheafBW = √(γ_+/Γ_+) = σ_min/σ_max`:
      `sheafBW_Samps_eq_singularValues_div`
    - (0, 1] boundary: `σ_min > 0` + `singularValues_antitone` (σ_min ≤ σ_max) →
      `div_pos` + `div_le_one`.

    paper-ref: `thm:strict-equality` (see `lean/CROSSREF.md`). -/
theorem strict_equality (eval : Fin M → E →L[ℂ] ℂ)
    (h_full_rank : 0 < (samplingOpEuclidean E eval).singularValues
        (finrank ℂ (LinearMap.range (samplingOpEuclidean E eval)) - 1)) :
    sheafBW (Samps E eval) =
        (samplingOpEuclidean E eval).singularValues
            (finrank ℂ (LinearMap.range (samplingOpEuclidean E eval)) - 1) /
          (samplingOpEuclidean E eval).singularValues 0
      ∧ sheafBW (Samps E eval) ∈ Set.Ioc (0 : ℝ) 1 := by
  -- σ_min ≤ σ_max(via singularValues antitone)
  have h_le :
      (samplingOpEuclidean E eval).singularValues
          (finrank ℂ (LinearMap.range (samplingOpEuclidean E eval)) - 1)
        ≤ (samplingOpEuclidean E eval).singularValues 0 :=
    (samplingOpEuclidean E eval).singularValues_antitone (Nat.zero_le _)
  -- σ_max > 0(由 σ_min > 0 + σ_min ≤ σ_max)
  have h_max_pos : 0 < (samplingOpEuclidean E eval).singularValues 0 :=
    lt_of_lt_of_le h_full_rank h_le
  -- sheafBW = σ_min / σ_max()
  have h_eq : sheafBW (Samps E eval) =
      (samplingOpEuclidean E eval).singularValues
          (finrank ℂ (LinearMap.range (samplingOpEuclidean E eval)) - 1) /
        (samplingOpEuclidean E eval).singularValues 0 :=
    sheafBW_Samps_eq_singularValues_div E eval h_max_pos.ne'
  refine ⟨h_eq, ?_⟩
  rw [h_eq, Set.mem_Ioc]
  exact ⟨div_pos h_full_rank h_max_pos, (div_le_one h_max_pos).mpr h_le⟩

/-- If the domain-last singular value is positive, then the range rank equals
    the domain dimension. This is the bridge from the positive-spectrum
    formulation of `strict_equality` to the paper's full-column-rank
    `σ_min(A) = σ_{K-1}(A)` formulation. -/
theorem finrank_range_samplingOpEuclidean_eq_finrank_of_singularValues_last_pos
    (eval : Fin M → E →L[ℂ] ℂ) (hn0 : 0 < finrank ℂ E)
    (h_full_rank : 0 < (samplingOpEuclidean E eval).singularValues (finrank ℂ E - 1)) :
    finrank ℂ (LinearMap.range (samplingOpEuclidean E eval)) = finrank ℂ E := by
  let A := samplingOpEuclidean E eval
  have h_lt : finrank ℂ E - 1 < finrank ℂ (LinearMap.range A) :=
    (A.singularValues_pos_iff_lt_finrank_range).mp h_full_rank
  have hE_le : finrank ℂ E ≤ finrank ℂ (LinearMap.range A) := by
    rw [← Nat.succ_pred_eq_of_pos hn0]
    exact Nat.succ_le_of_lt h_lt
  have h_range_le : finrank ℂ (LinearMap.range A) ≤ finrank ℂ E :=
    LinearMap.finrank_range_le A
  exact le_antisymm h_range_le hE_le

/-- **paper §5 Theorem 5.3 strict equality, full-column-rank form**.

    This is the exact domain-`σ_min(A)` form stated in the paper:
    under `σ_{K-1}(A) > 0`, `sheafBW(Samps) = σ_{K-1}(A) / σ_0(A)`
    and the value lies in `(0,1]`.

    It specializes `strict_equality`, whose internal spectral-gap form uses
    the smallest positive singular value indexed by `finrank (range A) - 1`.
    The full-rank hypothesis proves `finrank (range A) = finrank E`, so the
    two indices coincide.

    paper-ref: `thm:strict-equality` main equality + interval statement. -/
theorem strict_equality_full_rank (eval : Fin M → E →L[ℂ] ℂ)
    (hn0 : 0 < finrank ℂ E)
    (h_full_rank : 0 < (samplingOpEuclidean E eval).singularValues (finrank ℂ E - 1)) :
    sheafBW (Samps E eval) =
        (samplingOpEuclidean E eval).singularValues (finrank ℂ E - 1) /
          (samplingOpEuclidean E eval).singularValues 0
      ∧ sheafBW (Samps E eval) ∈ Set.Ioc (0 : ℝ) 1 := by
  have h_rank :
      finrank ℂ (LinearMap.range (samplingOpEuclidean E eval)) = finrank ℂ E :=
    finrank_range_samplingOpEuclidean_eq_finrank_of_singularValues_last_pos E eval hn0
      h_full_rank
  have h_pos :
      0 < (samplingOpEuclidean E eval).singularValues
        (finrank ℂ (LinearMap.range (samplingOpEuclidean E eval)) - 1) := by
    simpa [h_rank] using h_full_rank
  simpa [h_rank] using strict_equality E eval h_pos

/-- **paper §5 thm:strict-equality 上边界 iff 子陈述**:
    `sheafBW(Samps) = 1 ↔ σ_min(A) = σ_max(A)`(under full column rank)。

    paper §5 line 494-497:"The upper boundary $\sheafBW(\samps) = 1$ is attained
    iff $\sigma_{\min}(A) = \sigma_{\max}(A)$"。

    Proof:`sheafBW = σ_min/σ_max`(by `sheafBW_Samps_eq_singularValues_div`)
    + `σ_min/σ_max = 1 ↔ σ_min = σ_max`(`div_eq_one_iff_eq`,σ_max ≠ 0)。

    **Scope declaration**:本 lemma 显式覆盖 paper §5 line 494-497 的
    *spectral 等价部分*(`sheafBW = 1 ↔ σ_min = σ_max`)。paper 同句的
    *几何 interpretation* "iff $A$ is a positive scalar multiple of an isometry on $V_B$"
    需 mathlib 不直接提供的"全部奇异值相等 ↔ scalar multiple of isometry"等价引理 —
    paper informal proof 已给出该 derivation;Lean 端 explicit Submodule equality
    形态需独立 lemma,在本文件 scope 之外。paper footnote 显式 declare 该边界。

    paper-ref: `thm:strict-equality` 上边界 iff(spectral 部分)。 -/
theorem sheafBW_Samps_eq_one_iff_singularValues_eq (eval : Fin M → E →L[ℂ] ℂ)
    (h_full_rank : 0 < (samplingOpEuclidean E eval).singularValues
        (finrank ℂ (LinearMap.range (samplingOpEuclidean E eval)) - 1)) :
    sheafBW (Samps E eval) = 1 ↔
      (samplingOpEuclidean E eval).singularValues
          (finrank ℂ (LinearMap.range (samplingOpEuclidean E eval)) - 1)
        = (samplingOpEuclidean E eval).singularValues 0 := by
  have h_le :
      (samplingOpEuclidean E eval).singularValues
          (finrank ℂ (LinearMap.range (samplingOpEuclidean E eval)) - 1)
        ≤ (samplingOpEuclidean E eval).singularValues 0 :=
    (samplingOpEuclidean E eval).singularValues_antitone (Nat.zero_le _)
  have h_max_pos : 0 < (samplingOpEuclidean E eval).singularValues 0 :=
    lt_of_lt_of_le h_full_rank h_le
  rw [sheafBW_Samps_eq_singularValues_div E eval h_max_pos.ne',
      div_eq_one_iff_eq h_max_pos.ne']

/-- **paper §5 Theorem 5.3 upper-boundary iff, full-column-rank form**:
    `sheafBW(Samps) = 1 ↔ σ_{K-1}(A) = σ_0(A)`.

    This is the domain-`σ_min(A)` version of
    `sheafBW_Samps_eq_one_iff_singularValues_eq`; the full-rank hypothesis
    identifies `finrank (range A)` with `finrank E`.

    paper-ref: `thm:strict-equality` upper-boundary iff(spectral part). -/
theorem sheafBW_Samps_eq_one_iff_singularValues_domain_eq (eval : Fin M → E →L[ℂ] ℂ)
    (hn0 : 0 < finrank ℂ E)
    (h_full_rank : 0 < (samplingOpEuclidean E eval).singularValues (finrank ℂ E - 1)) :
    sheafBW (Samps E eval) = 1 ↔
      (samplingOpEuclidean E eval).singularValues (finrank ℂ E - 1)
        = (samplingOpEuclidean E eval).singularValues 0 := by
  have h_rank :
      finrank ℂ (LinearMap.range (samplingOpEuclidean E eval)) = finrank ℂ E :=
    finrank_range_samplingOpEuclidean_eq_finrank_of_singularValues_last_pos E eval hn0
      h_full_rank
  have h_pos :
      0 < (samplingOpEuclidean E eval).singularValues
        (finrank ℂ (LinearMap.range (samplingOpEuclidean E eval)) - 1) := by
    simpa [h_rank] using h_full_rank
  simpa [h_rank] using sheafBW_Samps_eq_one_iff_singularValues_eq E eval h_pos

-- =============================================================
-- §6 — H0-vanishing corollary
--    paper §5 line 527-537:H^0(Samps) = 0 ↔ A injective
-- =============================================================

omit [FiniteDimensional ℂ E] in
/-- `canonicalIsometryBackward E` 是 bijection(σ_∞ stalk Subsingleton ⇒
    surjective;σ_B 分量直接 retract ⇒ injective)— 关键桥接。 -/
theorem canonicalIsometryBackward_bijective :
    Function.Bijective (canonicalIsometryBackward E) := by
  refine ⟨?_, ?_⟩
  · intro c c' h
    have := congr_fun h XsampVert.σB
    exact this
  · intro s
    refine ⟨s XsampVert.σB, ?_⟩
    funext v
    cases v with
    | σB => rfl
    | σInf => exact Subsingleton.elim _ _

omit [FiniteDimensional ℂ E] in
/-- **paper §5 cor:H0-vanishing**(— Theorem 5.3 直接 corollary):

    Samps sheaf 的 0-th cohomology vanish 当且仅当 sampling operator `A`
    injective(等价 `A` full column rank,等价 `σ_min(A) > 0`)。

    Proof:
    - `globalSections Samps = ⊥ ↔ Injective (coboundary Samps)`(main
      theorem + `LinearMap.ker_eq_bot`)
    - `samplingOp = coboundary Samps ∘ canonicalIsometryBackward`()
    - `canonicalIsometryBackward` bijective(σ_∞ Subsingleton)⇒
      `Injective (coboundary Samps) ↔ Injective samplingOp`(`Injective.of_comp_iff'`)。 -/
theorem H0_vanishing_iff (eval : Fin M → E →L[ℂ] ℂ) :
    (Samps E eval).globalSections = ⊥ ↔ Function.Injective (samplingOp E eval) := by
  rw [(Samps E eval).globalSections_eq_ker_coboundary, LinearMap.ker_eq_bot,
      ← coboundary_eq_sampling_op E eval, LinearMap.coe_comp]
  exact (Function.Injective.of_comp_iff' _ (canonicalIsometryBackward_bijective E)).symm

end SamplingSpectral

end MRI.Cellular
