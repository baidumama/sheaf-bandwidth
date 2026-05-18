/-
  MRI.Cellular.Variational — Singular value variational characterization
                            + paper §3 (a)⇔(b) Riesz form

  .1 + 2.2 实现。informal cross-ref:
  paper/v0.1 §3 (Triangle Equivalence) line 99-198。

  本文件内容(全 LinearMap namespace,通用 — 三件 mathlib PR 候选):
  - §1-§4 σ_max/σ_min eigenvalue variational form(IsSymmetric)
        + ‖A x‖²/‖x‖² form(对 A: E →ₗ[𝕜] F)
  - §5 Bridge `rayleighQuotient (A* ∘ A) = ‖A x‖²/‖x‖²`
        (打通 mathlib 球面化桥)
  - §6 B1/B2:σ_max²/σ_min² 球面 form(paper eq:sigma-max-var / sigma-min-var)
  - §7 T1:球面上下界(‖c‖=1 ⇒ σ_min ≤ ‖A c‖ ≤ σ_max)
  - §8 T2:同质化(c ≠ 0 ⇒ σ_min ‖c‖ ≤ ‖A c‖ ≤ σ_max ‖c‖)
  - §9 Bridge `Injective A ↔ 0 < σ_min(A)`
  - §10 paper §3 (a)⇔(b) Riesz form(generic LinearMap form)

  mathlib PR 候选(三件):
  - §1 + §3 `IsSymmetric.eigenvalues_{zero,last}_eq_{iSup,iInf}_rayleigh`
  - §9 `injective_iff_singularValues_last_pos`
-/

import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Positive

open Module RCLike

namespace LinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
  {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

-- =============================================================
-- §1 σ_max eigenvalue variational form(IsSymmetric)
-- =============================================================

/-- For an `IsSymmetric` operator `T` on a nontrivial finite-dim Hilbert space,
    `eigenvalues 0` (the maximum eigenvalue, by antitone ordering) equals the
    iSup of the Rayleigh quotient.

    可上游 mathlib 候选 — connects `Spectrum.eigenvalues hn 0` 与
    `Rayleigh.hasEigenvalue_iSup_of_finiteDimensional`。 -/
theorem _root_.LinearMap.IsSymmetric.eigenvalues_zero_eq_iSup_rayleigh
    [Nontrivial E] {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric)
    {n : ℕ} (hn : finrank 𝕜 E = n) (hn0 : 0 < n) :
    (hT.eigenvalues hn ⟨0, hn0⟩ : ℝ)
      = ⨆ x : { x : E // x ≠ 0 }, RCLike.re (inner 𝕜 (T x) (x : E)) / ‖(x : E)‖ ^ 2 := by
  set R : { x : E // x ≠ 0 } → ℝ :=
    fun x => RCLike.re (inner 𝕜 (T x.val) x.val) / ‖x.val‖ ^ 2 with hR_def
  apply le_antisymm
  -- ≤ 方向: eigenvalues hn ⟨0, hn0⟩ ≤ ⨆ R
  · set v := hT.eigenvectorBasis hn ⟨0, hn0⟩ with hv_def
    have hv_norm : ‖v‖ = 1 := (hT.eigenvectorBasis hn).orthonormal.1 ⟨0, hn0⟩
    have hv_ne : v ≠ 0 := fun h => one_ne_zero
      (by rw [h, norm_zero] at hv_norm; exact hv_norm.symm)
    have h_apply : T v = (hT.eigenvalues hn ⟨0, hn0⟩ : 𝕜) • v :=
      hT.apply_eigenvectorBasis hn ⟨0, hn0⟩
    have h_re : RCLike.re (inner 𝕜 v v) = 1 := by
      rw [inner_self_eq_norm_sq (𝕜 := 𝕜), hv_norm, one_pow]
    have h_R_v : R ⟨v, hv_ne⟩ = hT.eigenvalues hn ⟨0, hn0⟩ := by
      change RCLike.re (inner 𝕜 (T v) v) / ‖v‖ ^ 2 = _
      rw [h_apply, inner_smul_left, RCLike.conj_ofReal,
        RCLike.re_ofReal_mul, h_re, mul_one, hv_norm, one_pow, div_one]
    have h_bdd : BddAbove (Set.range R) := by
      refine ⟨‖T.toContinuousLinearMap‖, ?_⟩
      rintro _ ⟨x, rfl⟩
      change RCLike.re (inner 𝕜 (T x.val) x.val) / ‖x.val‖ ^ 2 ≤ _
      have h_rq : T.toContinuousLinearMap.rayleighQuotient x.val
          = RCLike.re (inner 𝕜 (T x.val) x.val) / ‖x.val‖ ^ 2 := rfl
      rw [← h_rq]
      exact (le_abs_self _).trans
        (T.toContinuousLinearMap.rayleighQuotient_le_norm x.val)
    rw [← h_R_v]
    exact le_ciSup h_bdd ⟨v, hv_ne⟩
  -- ≥ 方向: ⨆ R ≤ eigenvalues hn ⟨0, hn0⟩
  · have h_iSup_eig : Module.End.HasEigenvalue T (⨆ x : { x : E // x ≠ 0 },
        RCLike.re (inner 𝕜 (T x.val) x.val) / ‖x.val‖ ^ 2 : ℝ) :=
      hT.hasEigenvalue_iSup_of_finiteDimensional
    obtain ⟨k, hk⟩ := hT.exists_eigenvalues_eq hn h_iSup_eig
    have hk_real : hT.eigenvalues hn k = ⨆ x : { x : E // x ≠ 0 },
        RCLike.re (inner 𝕜 (T x.val) x.val) / ‖x.val‖ ^ 2 :=
      RCLike.ofReal_injective hk
    rw [← hk_real]
    exact hT.eigenvalues_antitone hn (Fin.le_def.mpr (Nat.zero_le k.val))

-- =============================================================
-- §2 σ_max² variational form(paper eq:sigma-max-var)
-- =============================================================

/-- **σ_max² variational form**(paper §3 eq:sigma-max-var,line 172-176):
    `σ_max(A)² = ⨆_{x ≠ 0} ‖A x‖² / ‖x‖²`。

    Proof chain:
    1. `sq_singularValues_of_lt`:`σ_max² = max eigenvalue (A* ∘ A)`
    2. `eigenvalues_zero_eq_iSup_rayleigh`(§1):`max eigenvalue = ⨆ Rayleigh (A*A)`
    3. `apply_norm_sq_eq_inner_adjoint_left`:`Rayleigh (A*A) at x = ‖A x‖² / ‖x‖²` -/
theorem sq_singularValues_zero_eq_iSup_norm_sq
    [Nontrivial E] (A : E →ₗ[𝕜] F) (hn0 : 0 < finrank 𝕜 E) :
    A.singularValues 0 ^ 2
      = ⨆ x : { x : E // x ≠ 0 }, ‖A x‖ ^ 2 / ‖(x : E)‖ ^ 2 := by
  have h1 : A.singularValues 0 ^ 2
      = A.isSymmetric_adjoint_comp_self.eigenvalues rfl ⟨0, hn0⟩ :=
    A.sq_singularValues_of_lt rfl hn0
  have h2 : (A.isSymmetric_adjoint_comp_self.eigenvalues rfl ⟨0, hn0⟩ : ℝ)
      = ⨆ x : { x : E // x ≠ 0 },
          RCLike.re (inner 𝕜 ((A.adjoint ∘ₗ A) x) (x : E)) / ‖(x : E)‖ ^ 2 :=
    A.isSymmetric_adjoint_comp_self.eigenvalues_zero_eq_iSup_rayleigh rfl hn0
  have h3 : ∀ x : E, RCLike.re (inner 𝕜 ((A.adjoint ∘ₗ A) x) x) = ‖A x‖ ^ 2 := by
    intro x
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left,
      ← inner_self_eq_norm_sq (𝕜 := 𝕜)]
  rw [h1, h2]
  congr 1
  ext x
  rw [h3 (x : E)]

-- =============================================================
-- §3 σ_min eigenvalue variational form(IsSymmetric,对偶 §1)
-- =============================================================

/-- For an `IsSymmetric` operator `T` on a nontrivial finite-dim Hilbert space,
    `eigenvalues (n-1)` (the minimum eigenvalue, by antitone ordering) equals
    the iInf of the Rayleigh quotient.

    可上游 mathlib 候选 — σ_max 对偶 form。 -/
theorem _root_.LinearMap.IsSymmetric.eigenvalues_last_eq_iInf_rayleigh
    [Nontrivial E] {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric)
    {n : ℕ} (hn : finrank 𝕜 E = n) (hn0 : 0 < n) :
    (hT.eigenvalues hn ⟨n - 1, Nat.sub_lt hn0 Nat.one_pos⟩ : ℝ)
      = ⨅ x : { x : E // x ≠ 0 }, RCLike.re (inner 𝕜 (T x) (x : E)) / ‖(x : E)‖ ^ 2 := by
  set R : { x : E // x ≠ 0 } → ℝ :=
    fun x => RCLike.re (inner 𝕜 (T x.val) x.val) / ‖x.val‖ ^ 2 with hR_def
  set last_idx : Fin n := ⟨n - 1, Nat.sub_lt hn0 Nat.one_pos⟩ with hlast_def
  apply le_antisymm
  -- ≤ 方向: eigenvalues last ≤ ⨅ R
  · have h_iInf_eig : Module.End.HasEigenvalue T (⨅ x : { x : E // x ≠ 0 },
        RCLike.re (inner 𝕜 (T x.val) x.val) / ‖x.val‖ ^ 2 : ℝ) :=
      hT.hasEigenvalue_iInf_of_finiteDimensional
    obtain ⟨k, hk⟩ := hT.exists_eigenvalues_eq hn h_iInf_eig
    have hk_real : hT.eigenvalues hn k = ⨅ x : { x : E // x ≠ 0 },
        RCLike.re (inner 𝕜 (T x.val) x.val) / ‖x.val‖ ^ 2 :=
      RCLike.ofReal_injective hk
    rw [← hk_real]
    apply hT.eigenvalues_antitone hn
    change k.val ≤ n - 1
    omega
  -- ≥ 方向: ⨅ R ≤ eigenvalues last
  · set v := hT.eigenvectorBasis hn last_idx with hv_def
    have hv_norm : ‖v‖ = 1 := (hT.eigenvectorBasis hn).orthonormal.1 last_idx
    have hv_ne : v ≠ 0 := fun h => one_ne_zero
      (by rw [h, norm_zero] at hv_norm; exact hv_norm.symm)
    have h_apply : T v = (hT.eigenvalues hn last_idx : 𝕜) • v :=
      hT.apply_eigenvectorBasis hn last_idx
    have h_re : RCLike.re (inner 𝕜 v v) = 1 := by
      rw [inner_self_eq_norm_sq (𝕜 := 𝕜), hv_norm, one_pow]
    have h_R_v : R ⟨v, hv_ne⟩ = hT.eigenvalues hn last_idx := by
      change RCLike.re (inner 𝕜 (T v) v) / ‖v‖ ^ 2 = _
      rw [h_apply, inner_smul_left, RCLike.conj_ofReal,
        RCLike.re_ofReal_mul, h_re, mul_one, hv_norm, one_pow, div_one]
    have h_bdd : BddBelow (Set.range R) := by
      refine ⟨-‖T.toContinuousLinearMap‖, ?_⟩
      rintro _ ⟨x, rfl⟩
      change -‖T.toContinuousLinearMap‖ ≤ RCLike.re (inner 𝕜 (T x.val) x.val) / ‖x.val‖ ^ 2
      have h_rq : T.toContinuousLinearMap.rayleighQuotient x.val
          = RCLike.re (inner 𝕜 (T x.val) x.val) / ‖x.val‖ ^ 2 := rfl
      rw [← h_rq]
      have h_abs : |T.toContinuousLinearMap.rayleighQuotient x.val|
          ≤ ‖T.toContinuousLinearMap‖ :=
        T.toContinuousLinearMap.rayleighQuotient_le_norm x.val
      linarith [abs_le.mp h_abs]
    rw [← h_R_v]
    exact ciInf_le h_bdd ⟨v, hv_ne⟩

-- =============================================================
-- §4 σ_min² variational form(paper eq:sigma-min-var,对偶 §2)
-- =============================================================

/-- **σ_min² variational form**(paper §3 eq:sigma-min-var,line 177-181):
    `σ_min(A)² = ⨅_{x ≠ 0} ‖A x‖² / ‖x‖²`。对偶 §2。 -/
theorem sq_singularValues_last_eq_iInf_norm_sq
    [Nontrivial E] (A : E →ₗ[𝕜] F) (hn0 : 0 < finrank 𝕜 E) :
    A.singularValues (finrank 𝕜 E - 1) ^ 2
      = ⨅ x : { x : E // x ≠ 0 }, ‖A x‖ ^ 2 / ‖(x : E)‖ ^ 2 := by
  have h1 : A.singularValues (finrank 𝕜 E - 1) ^ 2
      = A.isSymmetric_adjoint_comp_self.eigenvalues rfl
          ⟨finrank 𝕜 E - 1, Nat.sub_lt hn0 Nat.one_pos⟩ :=
    A.sq_singularValues_of_lt rfl (Nat.sub_lt hn0 Nat.one_pos)
  have h2 : (A.isSymmetric_adjoint_comp_self.eigenvalues rfl
        ⟨finrank 𝕜 E - 1, Nat.sub_lt hn0 Nat.one_pos⟩ : ℝ)
      = ⨅ x : { x : E // x ≠ 0 },
          RCLike.re (inner 𝕜 ((A.adjoint ∘ₗ A) x) (x : E)) / ‖(x : E)‖ ^ 2 :=
    A.isSymmetric_adjoint_comp_self.eigenvalues_last_eq_iInf_rayleigh rfl hn0
  have h3 : ∀ x : E, RCLike.re (inner 𝕜 ((A.adjoint ∘ₗ A) x) x) = ‖A x‖ ^ 2 := by
    intro x
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left,
      ← inner_self_eq_norm_sq (𝕜 := 𝕜)]
  rw [h1, h2]
  congr 1
  ext x
  rw [h3 (x : E)]

-- =============================================================
-- §5 Bridge:rayleighQuotient (A* ∘ A) = ‖A x‖² / ‖x‖²
-- =============================================================

/-- **Bridge lemma**:`(A* ∘ A) toCLM rayleighQuotient x = ‖A x‖² / ‖x‖²`。
    打通 mathlib 球面化桥(`iSup_rayleigh_eq_iSup_rayleigh_sphere`)与
    `‖A x‖²/‖x‖²` form。 -/
lemma rayleighQuotient_adjoint_comp_self_eq_norm_sq_ratio
    (A : E →ₗ[𝕜] F) (x : E) :
    (A.adjoint ∘ₗ A).toContinuousLinearMap.rayleighQuotient x
      = ‖A x‖ ^ 2 / ‖x‖ ^ 2 := by
  change RCLike.re (inner 𝕜 ((A.adjoint ∘ₗ A) x) x) / ‖x‖ ^ 2 = _
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left,
    inner_self_eq_norm_sq (𝕜 := 𝕜)]

-- =============================================================
-- §6 B1/B2:σ_max²/σ_min² 球面 form
-- =============================================================

/-- **B1 — σ_max² 球面 form**(paper §3 eq:sigma-max-var,line 172-176):
    `σ_max(A)² = ⨆_{‖x‖=1} ‖A x‖²`。从 §2 非零 ratio form 桥到球面 form。 -/
theorem sq_singularValues_zero_eq_iSup_norm_sq_sphere
    [Nontrivial E] (A : E →ₗ[𝕜] F) (hn0 : 0 < finrank 𝕜 E) :
    A.singularValues 0 ^ 2
      = ⨆ x : Metric.sphere (0 : E) 1, ‖A (x : E)‖ ^ 2 := by
  rw [A.sq_singularValues_zero_eq_iSup_norm_sq hn0]
  have hcongr_nz : ∀ x : { x : E // x ≠ 0 },
      ‖A x.val‖ ^ 2 / ‖x.val‖ ^ 2
        = (A.adjoint ∘ₗ A).toContinuousLinearMap.rayleighQuotient x.val := by
    intro x
    rw [rayleighQuotient_adjoint_comp_self_eq_norm_sq_ratio]
  rw [iSup_congr hcongr_nz]
  rw [(A.adjoint ∘ₗ A).toContinuousLinearMap.iSup_rayleigh_eq_iSup_rayleigh_sphere
    (r := 1) one_pos]
  refine iSup_congr (fun x => ?_)
  rw [rayleighQuotient_adjoint_comp_self_eq_norm_sq_ratio]
  have hx : ‖(x : E)‖ = 1 := by
    have := x.2
    rwa [mem_sphere_zero_iff_norm] at this
  rw [hx, one_pow, div_one]

/-- **B2 — σ_min² 球面 form**(paper §3 eq:sigma-min-var,line 177-181):
    `σ_min(A)² = ⨅_{‖x‖=1} ‖A x‖²`。对偶 B1。 -/
theorem sq_singularValues_last_eq_iInf_norm_sq_sphere
    [Nontrivial E] (A : E →ₗ[𝕜] F) (hn0 : 0 < finrank 𝕜 E) :
    A.singularValues (finrank 𝕜 E - 1) ^ 2
      = ⨅ x : Metric.sphere (0 : E) 1, ‖A (x : E)‖ ^ 2 := by
  rw [A.sq_singularValues_last_eq_iInf_norm_sq hn0]
  have hcongr_nz : ∀ x : { x : E // x ≠ 0 },
      ‖A x.val‖ ^ 2 / ‖x.val‖ ^ 2
        = (A.adjoint ∘ₗ A).toContinuousLinearMap.rayleighQuotient x.val := by
    intro x
    rw [rayleighQuotient_adjoint_comp_self_eq_norm_sq_ratio]
  rw [iInf_congr hcongr_nz]
  rw [(A.adjoint ∘ₗ A).toContinuousLinearMap.iInf_rayleigh_eq_iInf_rayleigh_sphere
    (r := 1) one_pos]
  refine iInf_congr (fun x => ?_)
  rw [rayleighQuotient_adjoint_comp_self_eq_norm_sq_ratio]
  have hx : ‖(x : E)‖ = 1 := by
    have := x.2
    rwa [mem_sphere_zero_iff_norm] at this
  rw [hx, one_pow, div_one]

-- =============================================================
-- §7 T1:球面上下界(‖c‖=1 ⇒ σ_min ≤ ‖A c‖ ≤ σ_max)
-- =============================================================

/-- **T1 上界**:`‖c‖ = 1 ⇒ ‖A c‖ ≤ σ_max(A)`。
    从 B1(平方球面 form)+ singularValues_nonneg + sqrt 单调推。 -/
theorem norm_apply_le_singularValues_zero_of_norm_one
    [Nontrivial E] (A : E →ₗ[𝕜] F) (hn0 : 0 < finrank 𝕜 E)
    {c : E} (hc : ‖c‖ = 1) :
    ‖A c‖ ≤ A.singularValues 0 := by
  have hc_sphere : c ∈ Metric.sphere (0 : E) 1 := mem_sphere_zero_iff_norm.mpr hc
  have h_bdd : BddAbove (Set.range
      (fun x : Metric.sphere (0 : E) 1 => ‖A (x : E)‖ ^ 2)) := by
    refine ⟨‖A.toContinuousLinearMap‖ ^ 2, ?_⟩
    rintro _ ⟨x, rfl⟩
    have hx_norm : ‖(x : E)‖ = 1 := mem_sphere_zero_iff_norm.mp x.2
    have h_le : ‖A x.val‖ ≤ ‖A.toContinuousLinearMap‖ := by
      have := A.toContinuousLinearMap.le_opNorm x.val
      rw [hx_norm, mul_one] at this
      exact this
    exact pow_le_pow_left₀ (norm_nonneg _) h_le 2
  have h_sq : ‖A c‖ ^ 2 ≤ A.singularValues 0 ^ 2 := by
    rw [A.sq_singularValues_zero_eq_iSup_norm_sq_sphere hn0]
    exact le_ciSup h_bdd ⟨c, hc_sphere⟩
  exact le_of_sq_le_sq h_sq (A.singularValues_nonneg 0)

/-- **T1 下界**:`‖c‖ = 1 ⇒ σ_min(A) ≤ ‖A c‖`。对偶 T1 上界。 -/
theorem singularValues_last_le_norm_apply_of_norm_one
    [Nontrivial E] (A : E →ₗ[𝕜] F) (hn0 : 0 < finrank 𝕜 E)
    {c : E} (hc : ‖c‖ = 1) :
    A.singularValues (finrank 𝕜 E - 1) ≤ ‖A c‖ := by
  have hc_sphere : c ∈ Metric.sphere (0 : E) 1 := mem_sphere_zero_iff_norm.mpr hc
  have h_bdd : BddBelow (Set.range
      (fun x : Metric.sphere (0 : E) 1 => ‖A (x : E)‖ ^ 2)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact sq_nonneg _
  have h_sq : A.singularValues (finrank 𝕜 E - 1) ^ 2 ≤ ‖A c‖ ^ 2 := by
    rw [A.sq_singularValues_last_eq_iInf_norm_sq_sphere hn0]
    exact ciInf_le h_bdd ⟨c, hc_sphere⟩
  exact le_of_sq_le_sq h_sq (norm_nonneg _)

-- =============================================================
-- §8 T2:同质化(c ≠ 0 ⇒ σ_min ‖c‖ ≤ ‖A c‖ ≤ σ_max ‖c‖)
-- =============================================================

/-- **T2 上界**:`‖A c‖ ≤ σ_max(A) · ‖c‖`(c = 0 时两边 = 0,c ≠ 0 通过 c/‖c‖ scale)。 -/
theorem norm_apply_le_singularValues_zero_mul_norm
    [Nontrivial E] (A : E →ₗ[𝕜] F) (hn0 : 0 < finrank 𝕜 E) (c : E) :
    ‖A c‖ ≤ A.singularValues 0 * ‖c‖ := by
  by_cases hc : c = 0
  · simp [hc]
  · have hcn_pos : 0 < ‖c‖ := norm_pos_iff.mpr hc
    set r : 𝕜 := (‖c‖ : 𝕜)⁻¹ with hr_def
    have hr_norm : ‖r‖ = (‖c‖)⁻¹ := by
      simp only [r, norm_inv, RCLike.norm_ofReal, abs_of_pos hcn_pos]
    set c' : E := r • c with hc'_def
    have hc'_norm : ‖c'‖ = 1 := by
      simp only [c', norm_smul, hr_norm]
      exact inv_mul_cancel₀ hcn_pos.ne'
    have h1 : ‖A c'‖ ≤ A.singularValues 0 :=
      A.norm_apply_le_singularValues_zero_of_norm_one hn0 hc'_norm
    have hAc' : ‖A c'‖ = (‖c‖)⁻¹ * ‖A c‖ := by
      simp only [c', LinearMap.map_smul, norm_smul, hr_norm]
    rw [hAc'] at h1
    rw [inv_mul_le_iff₀ hcn_pos] at h1
    linarith

/-- **T2 下界**:`σ_min(A) · ‖c‖ ≤ ‖A c‖`(c = 0 时两边 = 0)。 -/
theorem singularValues_last_mul_norm_le_norm_apply
    [Nontrivial E] (A : E →ₗ[𝕜] F) (hn0 : 0 < finrank 𝕜 E) (c : E) :
    A.singularValues (finrank 𝕜 E - 1) * ‖c‖ ≤ ‖A c‖ := by
  by_cases hc : c = 0
  · simp [hc]
  · have hcn_pos : 0 < ‖c‖ := norm_pos_iff.mpr hc
    set r : 𝕜 := (‖c‖ : 𝕜)⁻¹ with hr_def
    have hr_norm : ‖r‖ = (‖c‖)⁻¹ := by
      simp only [r, norm_inv, RCLike.norm_ofReal, abs_of_pos hcn_pos]
    set c' : E := r • c with hc'_def
    have hc'_norm : ‖c'‖ = 1 := by
      simp only [c', norm_smul, hr_norm]
      exact inv_mul_cancel₀ hcn_pos.ne'
    have h1 : A.singularValues (finrank 𝕜 E - 1) ≤ ‖A c'‖ :=
      A.singularValues_last_le_norm_apply_of_norm_one hn0 hc'_norm
    have hAc' : ‖A c'‖ = (‖c‖)⁻¹ * ‖A c‖ := by
      simp only [c', LinearMap.map_smul, norm_smul, hr_norm]
    rw [hAc'] at h1
    rw [le_inv_mul_iff₀ hcn_pos] at h1
    linarith

-- =============================================================
-- §9 Injective ↔ σ_min > 0(mathlib PR 候选)
-- =============================================================

/-- **Bridge lemma**:`Injective A ↔ 0 < A.singularValues (finrank E - 1)`(即 σ_min)。
    特化 mathlib `injective_iff_forall_lt_finrank_singularValues_pos` 到 σ_min,
    via `singularValues_antitone`。

    可上游 mathlib 候选。 -/
lemma injective_iff_singularValues_last_pos
    [Nontrivial E] (A : E →ₗ[𝕜] F) (hn0 : 0 < finrank 𝕜 E) :
    Function.Injective A ↔ 0 < A.singularValues (finrank 𝕜 E - 1) := by
  rw [A.injective_iff_forall_lt_finrank_singularValues_pos]
  refine ⟨fun h => h _ (Nat.sub_lt hn0 Nat.one_pos), ?_⟩
  intro h i hi
  exact lt_of_lt_of_le h (A.singularValues_antitone (Nat.le_sub_one_of_lt hi))

-- =============================================================
-- §10 paper §3 (a) ↔ (b) Riesz form(generic LinearMap form)
-- =============================================================

/-- ** paper §3 (a) ↔ (b)** — Triangle Equivalence 。

    (a):`σ_min(A) ≥ τ · σ_max(A)`(FEEC singular value form)
    (b):`∃ α β, 0 < α ∧ α ≤ β ∧ β/α ≤ 1/τ ∧ ∀ c ≠ 0, α‖c‖ ≤ ‖A c‖ ≤ β‖c‖`
         (Hodge-spectrum Riesz form)

    paper §3 line 99-114 + line 182-198 mirror。Lean 形式 ι_B isometric +
    A = Σ_{V_s} ∘ ι_B 已通过 abstract `A : E →ₗ[𝕜] F` 化掉 type plumbing
    (paper eq:Avariational 已做这件事 reduction)。

    ****:lake build PASS / 0 sorry / 0 admitted。

    注:`_hτ_le : τ ≤ 1` 是 paper assumption,但 (a)⇔(b) 证明不需要 — 诚实标注。

    paper-ref: `thm:triangle-equiv` (a)⇔(b)(详见 `lean/CROSSREF.md`)。 -/
theorem triangle_equiv_a_iff_b
    [Nontrivial E] (A : E →ₗ[𝕜] F) (hn0 : 0 < finrank 𝕜 E)
    {τ : ℝ} (hτ_pos : 0 < τ) (_hτ_le : τ ≤ 1)
    (hsmax_pos : 0 < A.singularValues 0) :
    (A.singularValues (finrank 𝕜 E - 1) ≥ τ * A.singularValues 0)
      ↔
    (∃ α β : ℝ, 0 < α ∧ α ≤ β ∧ β / α ≤ 1 / τ ∧
      ∀ c : E, c ≠ 0 → α * ‖c‖ ≤ ‖A c‖ ∧ ‖A c‖ ≤ β * ‖c‖) := by
  constructor
  -- (a) ⇒ (b):set α := σ_min, β := σ_max,T2 直接给
  · intro ha
    refine ⟨A.singularValues (finrank 𝕜 E - 1), A.singularValues 0, ?_, ?_, ?_, ?_⟩
    · exact lt_of_lt_of_le (mul_pos hτ_pos hsmax_pos) ha
    · exact A.singularValues_antitone (Nat.zero_le _)
    · have hsmin_pos : 0 < A.singularValues (finrank 𝕜 E - 1) :=
        lt_of_lt_of_le (mul_pos hτ_pos hsmax_pos) ha
      rw [div_le_div_iff₀ hsmin_pos hτ_pos]
      have : τ * A.singularValues 0 ≤ A.singularValues (finrank 𝕜 E - 1) := ha
      linarith
    · intro c _
      exact ⟨A.singularValues_last_mul_norm_le_norm_apply hn0 c,
        A.norm_apply_le_singularValues_zero_mul_norm hn0 c⟩
  -- (b) ⇒ (a):∃ α β + 球面 取 ⨅/⨆ → α ≤ σ_min ∧ σ_max ≤ β → σ_min ≥ τ σ_max
  · rintro ⟨α, β, hα_pos, hαβ, hβα_τ, hbnd⟩
    have h_sphere_ne : Nonempty (Metric.sphere (0 : E) 1) := by
      obtain ⟨v, hv⟩ := exists_ne (0 : E)
      have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
      refine ⟨⟨((‖v‖ : 𝕜))⁻¹ • v, ?_⟩⟩
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, RCLike.norm_ofReal,
        abs_of_pos hvn]
      exact inv_mul_cancel₀ hvn.ne'
    have hsmax_le_β : A.singularValues 0 ≤ β := by
      have hsq : A.singularValues 0 ^ 2 ≤ β ^ 2 := by
        rw [A.sq_singularValues_zero_eq_iSup_norm_sq_sphere hn0]
        apply ciSup_le
        intro x
        have hx_norm : ‖(x : E)‖ = 1 := mem_sphere_zero_iff_norm.mp x.2
        have hx_ne : (x : E) ≠ 0 := by
          intro h
          rw [h, norm_zero] at hx_norm
          exact zero_ne_one hx_norm
        have := (hbnd x.val hx_ne).2
        rw [hx_norm, mul_one] at this
        exact pow_le_pow_left₀ (norm_nonneg _) this 2
      have hβ_nn : 0 ≤ β := le_trans hα_pos.le hαβ
      exact le_of_sq_le_sq hsq hβ_nn
    have hα_le_smin : α ≤ A.singularValues (finrank 𝕜 E - 1) := by
      have hsq : α ^ 2 ≤ A.singularValues (finrank 𝕜 E - 1) ^ 2 := by
        rw [A.sq_singularValues_last_eq_iInf_norm_sq_sphere hn0]
        apply le_ciInf
        intro x
        have hx_norm : ‖(x : E)‖ = 1 := mem_sphere_zero_iff_norm.mp x.2
        have hx_ne : (x : E) ≠ 0 := by
          intro h
          rw [h, norm_zero] at hx_norm
          exact zero_ne_one hx_norm
        have := (hbnd x.val hx_ne).1
        rw [hx_norm, mul_one] at this
        exact pow_le_pow_left₀ hα_pos.le this 2
      exact le_of_sq_le_sq hsq (A.singularValues_nonneg _)
    have hβ_pos : 0 < β := lt_of_lt_of_le hα_pos hαβ
    have hτ_le_αβ : τ ≤ α / β := by
      rw [div_le_div_iff₀ hα_pos hτ_pos] at hβα_τ
      rw [le_div_iff₀ hβ_pos]
      linarith
    have hτ_smax_le_α : τ * A.singularValues 0 ≤ α := by
      have : τ * β ≤ α := by
        rw [le_div_iff₀ hβ_pos] at hτ_le_αβ
        linarith
      calc τ * A.singularValues 0
          ≤ τ * β := mul_le_mul_of_nonneg_left hsmax_le_β hτ_pos.le
        _ ≤ α := this
    exact le_trans hτ_smax_le_α hα_le_smin

end LinearMap
