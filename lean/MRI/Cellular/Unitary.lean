/-
  MRI.Cellular.Unitary — Unitary sheaf morphism + sheafBW invariance

  + 4 实现。informal cross-ref:paper/v0.1 §5
    Proposition 5.4 prop:sheafBW-unitary(line 199-232)+
    Subsection 5.4 subsec:sheafbw-unitary。
  依赖:Spectral.lean(GammaPlus / gammaPlus / sheafBW)+
       SamplingSpectral.lean §1(pre/post-compose LIE singularValues helper)。

  paper §5 prop:sheafBW-unitary:存在 unitary sheaf morphism Φ : A → A' ⇒
  sheafBW(A) = sheafBW(A')。

  Lean 实施(section 分层,最小化 typeclass 假设):
  §1 UnitarySheafMorphism structure(NACG + IPS,不需 Fintype/FD)
  §3 Discrepancy-level commute(plain Π,NACG + IPS)
  §2 Cochain-level unitary 装配 + §4 Cochain-level commute + finrank_range(加 Fintype)
  §5 singularValues invariance + sheafBW invariance(加 FD)
-/

import MRI.Cellular.Spectral
import MRI.Cellular.SamplingSpectral

namespace MRI.Cellular

/-! ### §1 UnitarySheafMorphism structure(基础 — 仅需 NACG + IPS) -/

section UnitarySheafMorphism_Base

variable {C : Complex1D}
  {stalk₀ : C.Cells₀ → Type*}
  [∀ v, NormedAddCommGroup (stalk₀ v)] [∀ v, InnerProductSpace ℂ (stalk₀ v)]
  {stalk₁ : C.Cells₁ → Type*}
  [∀ e, NormedAddCommGroup (stalk₁ e)] [∀ e, InnerProductSpace ℂ (stalk₁ e)]
  {stalk₀' : C.Cells₀ → Type*}
  [∀ v, NormedAddCommGroup (stalk₀' v)] [∀ v, InnerProductSpace ℂ (stalk₀' v)]
  {stalk₁' : C.Cells₁ → Type*}
  [∀ e, NormedAddCommGroup (stalk₁' e)] [∀ e, InnerProductSpace ℂ (stalk₁' e)]

/-- **Unitary sheaf morphism**(paper §5 prop:sheafBW-unitary 前提):
两个 cellular sheaf `S, S'` 之间的 *unitary* sheaf morphism,即一族 stalk-wise
linear isometric equivalence,满足 sheaf-morphism 相容性。

字段(对应 paper "family of stalk-wise unitaries Φ_σ satisfying compatibility
`Φ_τ ∘ A(σ ≤ τ) = A'(σ ≤ τ) ∘ Φ_σ`"):
- `Φ₀ v` — 每个 0-cell `v` 上的 unitary `stalk₀ v ≃ₗᵢ[ℂ] stalk₀' v`
- `Φ₁ e` — 每个 1-cell `e` 上的 unitary `stalk₁ e ≃ₗᵢ[ℂ] stalk₁' e`
- `compat_restrict₀ e` — 对 face₀(paper +1 端,σ_B)的相容性
- `compat_restrict₁ e` — 对 face₁(paper -1 端,σ_∞)的相容性

注:`≃ₗᵢ[ℂ]`(`LinearIsometryEquiv`)是 mathlib4 中 "unitary on fin-dim Hilbert
space" 的标准表示(等价于 Hilbert 意义的 unitary operator)。 -/
structure UnitarySheafMorphism
    (S : CellularSheaf C stalk₀ stalk₁) (S' : CellularSheaf C stalk₀' stalk₁') where
  Φ₀ : ∀ v, stalk₀ v ≃ₗᵢ[ℂ] stalk₀' v
  Φ₁ : ∀ e, stalk₁ e ≃ₗᵢ[ℂ] stalk₁' e
  compat_restrict₀ : ∀ e (x : stalk₀ (C.face₀ e)),
    Φ₁ e (S.restrict₀ e x) = S'.restrict₀ e (Φ₀ (C.face₀ e) x)
  compat_restrict₁ : ∀ e (x : stalk₀ (C.face₁ e)),
    Φ₁ e (S.restrict₁ e x) = S'.restrict₁ e (Φ₀ (C.face₁ e) x)

namespace UnitarySheafMorphism

variable {S : CellularSheaf C stalk₀ stalk₁} {S' : CellularSheaf C stalk₀' stalk₁'}

/-! ### §3 Discrepancy-level commute(plain Π,仅需 NACG + IPS) -/

/-- **Discrepancy-level commute helper**:在 plain Π 层 `discrepancy` 与
stalk-wise Φ₀/Φ₁ 满足 component-wise commute:`Φ₁ e (discrepancy_S s e) =
discrepancy_{S'} (Φ₀ ∘ s) e`。

证:展开 discrepancy = restrict₀ - restrict₁,Φ₁ map_sub,然后 compat_restrict₀/₁
替换。 -/
theorem discrepancy_commute (Φ : UnitarySheafMorphism S S') (s : ∀ v, stalk₀ v)
    (e : C.Cells₁) :
    Φ.Φ₁ e (S.discrepancy s e) =
      S'.discrepancy (fun v => Φ.Φ₀ v (s v)) e := by
  simp only [CellularSheaf.discrepancy, LinearMap.coe_mk, AddHom.coe_mk, map_sub]
  rw [Φ.compat_restrict₀ e, Φ.compat_restrict₁ e]

end UnitarySheafMorphism

end UnitarySheafMorphism_Base

/-! ### §2 + §4 Cochain-level unitary + commute + finrank_range(加 Fintype) -/

section UnitarySheafMorphism_Cochain

variable {C : Complex1D} [Fintype C.Cells₀] [Fintype C.Cells₁]
  {stalk₀ : C.Cells₀ → Type*}
  [∀ v, NormedAddCommGroup (stalk₀ v)] [∀ v, InnerProductSpace ℂ (stalk₀ v)]
  {stalk₁ : C.Cells₁ → Type*}
  [∀ e, NormedAddCommGroup (stalk₁ e)] [∀ e, InnerProductSpace ℂ (stalk₁ e)]
  {stalk₀' : C.Cells₀ → Type*}
  [∀ v, NormedAddCommGroup (stalk₀' v)] [∀ v, InnerProductSpace ℂ (stalk₀' v)]
  {stalk₁' : C.Cells₁ → Type*}
  [∀ e, NormedAddCommGroup (stalk₁' e)] [∀ e, InnerProductSpace ℂ (stalk₁' e)]
  {S : CellularSheaf C stalk₀ stalk₁} {S' : CellularSheaf C stalk₀' stalk₁'}

namespace UnitarySheafMorphism

/-- **Cochain-level unitary on C^0**:把 stalk-wise `Φ₀` 装配成
`Cochain0 C stalk₀ ≃ₗᵢ[ℂ] Cochain0 C stalk₀'` via `piLpCongrRight`。 -/
noncomputable def cochainUnitary0 (Φ : UnitarySheafMorphism S S') :
    Cochain0 C stalk₀ ≃ₗᵢ[ℂ] Cochain0 C stalk₀' :=
  LinearIsometryEquiv.piLpCongrRight 2 Φ.Φ₀

/-- **Cochain-level unitary on C^1**:同上对 1-cells。 -/
noncomputable def cochainUnitary1 (Φ : UnitarySheafMorphism S S') :
    Cochain1 C stalk₁ ≃ₗᵢ[ℂ] Cochain1 C stalk₁' :=
  LinearIsometryEquiv.piLpCongrRight 2 Φ.Φ₁

/-- **Cochain-level commute(element form)**:`δ_{S'} (U₀ s) = U₁ (δ_S s)`,即
`coboundaryHilbert ∘ U₀ = U₁ ∘ coboundaryHilbert`(per s)。

证:展开 coboundaryHilbert 到 plain Π discrepancy 层(via WithLp.linearEquiv 桥),
内层等式归约到 `discrepancy_commute`。 -/
theorem coboundaryHilbert_commute (Φ : UnitarySheafMorphism S S')
    (s : Cochain0 C stalk₀) :
    S'.coboundaryHilbert (Φ.cochainUnitary0 s) =
      Φ.cochainUnitary1 (S.coboundaryHilbert s) := by
  ext e
  change (S'.coboundary (fun v => Φ.Φ₀ v (s.ofLp v))) e =
        Φ.Φ₁ e ((S.coboundary s.ofLp) e)
  exact (Φ.discrepancy_commute s.ofLp e).symm

/-- **LinearMap form of `coboundaryHilbert_commute`**:`δ_{S'} ∘ U₀ = U₁ ∘ δ_S`
作为 LinearMap 等式。本 form 直接喂给 `singularValues_{comp,linearIsometryEquiv_comp}`。 -/
theorem coboundaryHilbert_commute_linearMap (Φ : UnitarySheafMorphism S S') :
    S'.coboundaryHilbert ∘ₗ Φ.cochainUnitary0.toLinearMap =
      Φ.cochainUnitary1.toLinearMap ∘ₗ S.coboundaryHilbert :=
  LinearMap.ext fun s => Φ.coboundaryHilbert_commute s

/-- **Range finrank invariance under unitary sheaf morphism**:`range(δ_{S'})`
与 `range(δ_S)` 有相同 finrank。

证:由 `coboundaryHilbert_commute_linearMap` 得 `range(δ_{S'}) = U₁.map(range δ_S)`
(经 `range_comp` + `U₀` surjective),再用 `LinearEquiv.finrank_map_eq`。

注:不依赖 FD instance(仅用 LinearEquiv 装备的 finrank 不变性),故放 §4 cochain
section,留 §5 仅含真正需要 FD 的 singularValues + sheafBW。 -/
theorem finrank_range_coboundaryHilbert_eq (Φ : UnitarySheafMorphism S S') :
    Module.finrank ℂ (LinearMap.range S.coboundaryHilbert)
      = Module.finrank ℂ (LinearMap.range S'.coboundaryHilbert) := by
  have h_commute := Φ.coboundaryHilbert_commute_linearMap
  have h_range_eq : LinearMap.range S'.coboundaryHilbert
                    = (LinearMap.range S.coboundaryHilbert).map
                        Φ.cochainUnitary1.toLinearMap := by
    have hsurj : LinearMap.range Φ.cochainUnitary0.toLinearMap = ⊤ :=
      LinearMap.range_eq_top.mpr Φ.cochainUnitary0.surjective
    have : LinearMap.range (S'.coboundaryHilbert ∘ₗ Φ.cochainUnitary0.toLinearMap)
            = LinearMap.range S'.coboundaryHilbert := by
      rw [LinearMap.range_comp, hsurj, Submodule.map_top]
    rw [← this, h_commute, LinearMap.range_comp]
  rw [h_range_eq, LinearEquiv.finrank_map_eq Φ.cochainUnitary1.toLinearEquiv]

end UnitarySheafMorphism

end UnitarySheafMorphism_Cochain

/-! ### §5 sheafBW invariance(paper §5 Prop 5.4 主陈述,加 FD)  -/

section UnitarySheafMorphism_FD

variable {C : Complex1D} [Fintype C.Cells₀] [Fintype C.Cells₁]
  {stalk₀ : C.Cells₀ → Type*}
  [∀ v, NormedAddCommGroup (stalk₀ v)] [∀ v, InnerProductSpace ℂ (stalk₀ v)]
  [∀ v, FiniteDimensional ℂ (stalk₀ v)]
  {stalk₁ : C.Cells₁ → Type*}
  [∀ e, NormedAddCommGroup (stalk₁ e)] [∀ e, InnerProductSpace ℂ (stalk₁ e)]
  [∀ e, FiniteDimensional ℂ (stalk₁ e)]
  {stalk₀' : C.Cells₀ → Type*}
  [∀ v, NormedAddCommGroup (stalk₀' v)] [∀ v, InnerProductSpace ℂ (stalk₀' v)]
  [∀ v, FiniteDimensional ℂ (stalk₀' v)]
  {stalk₁' : C.Cells₁ → Type*}
  [∀ e, NormedAddCommGroup (stalk₁' e)] [∀ e, InnerProductSpace ℂ (stalk₁' e)]
  [∀ e, FiniteDimensional ℂ (stalk₁' e)]
  {S : CellularSheaf C stalk₀ stalk₁} {S' : CellularSheaf C stalk₀' stalk₁'}

namespace UnitarySheafMorphism

/-- **singularValues invariance under unitary sheaf morphism**:
`S'.coboundaryHilbert.singularValues = S.coboundaryHilbert.singularValues`。

证:从 `coboundaryHilbert_commute_linearMap` 出发,两边 singularValues 各用
pre-compose / post-compose unitary invariance,得
`δ_{S'}.sv = (δ_{S'} ∘ U₀).sv = (U₁ ∘ δ_S).sv = δ_S.sv`。 -/
theorem singularValues_coboundaryHilbert_eq (Φ : UnitarySheafMorphism S S') :
    S'.coboundaryHilbert.singularValues = S.coboundaryHilbert.singularValues := by
  have h_commute := Φ.coboundaryHilbert_commute_linearMap
  have h1 : (S'.coboundaryHilbert ∘ₗ Φ.cochainUnitary0.toLinearMap).singularValues
              = S'.coboundaryHilbert.singularValues :=
    LinearMap.singularValues_comp_linearIsometryEquiv _ _
  have h2 : (Φ.cochainUnitary1.toLinearMap ∘ₗ S.coboundaryHilbert).singularValues
              = S.coboundaryHilbert.singularValues :=
    LinearMap.singularValues_linearIsometryEquiv_comp _ _
  rw [← h1, h_commute, h2]

/-- **paper §5 Proposition 5.4 prop:sheafBW-unitary 主陈述 **
:存在 unitary sheaf morphism `Φ : S → S'` ⇒
`sheafBW S = sheafBW S'`。

证:`GammaPlus / gammaPlus` 都是 `coboundaryHilbert.singularValues + finrank range`
的 pointwise 表达,两者在 unitary morphism 下不变 → `sheafBW` 不变。 -/
theorem sheafBW_eq (Φ : UnitarySheafMorphism S S') :
    sheafBW S = sheafBW S' := by
  have h_sv := Φ.singularValues_coboundaryHilbert_eq
  have h_finrank := Φ.finrank_range_coboundaryHilbert_eq
  simp only [sheafBW, GammaPlus, gammaPlus, h_sv, h_finrank]

end UnitarySheafMorphism

end UnitarySheafMorphism_FD

end MRI.Cellular
