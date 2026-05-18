/-
  MRI.Cellular.Sampling — Abstract sampling cell complex Xsamp + sampling sheaf Samps

  -3 实现。informal cross-ref:paper/v0.1 §5 def:Xsamp + def:sampling-sheaf。
  依赖:Complex.lean(Complex1D) + Sheaf.lean(CellularSheaf generic)。

  paper §5 双 0-cell 模型:
  - σ_B(principal 0-cell)+ σ_∞(auxiliary basepoint,no physical content)
  - M 条 1-cells τ_i,boundary ∂τ_i = {σ_B, σ_∞}
  - incidence:[σ_B : τ_i] = +1,[σ_∞ : τ_i] = -1

  :Xsamp 抽象 cell complex(§1)
  :Samps sampling sheaf(§2)
  :canonical isometry V_B ⊕ 0 ≅ V_B(§3)+ prop:delta-equals-A(§4)
-/

import MRI.Cellular.Sheaf
import MRI.Cellular.Sections
import MRI.Cellular.Inner
import MRI.Cellular.Coboundary

namespace MRI.Cellular

-- =============================================================
-- §1 Abstract sampling cell complex(Xsamp,paper §5 def:Xsamp)
-- =============================================================

/-- Xsamp 的 0-cell 类型:`σB`(principal,paper σ_B)+ `σInf`(auxiliary basepoint
paper σ_∞)。

paper §5 def:Xsamp:σ_∞ 是"no physical content" 的 auxiliary basepoint —
用于满足 regular cell complex 的 "1-cell 两端必须是 distinct 0-cells" 条件
(Cond. 4 of [HansenGhrist2019] §2 Def. 1)。

注:Lean 4 identifier 规则中 `∞`(U+221E,Sm category)不是合法 subsequent
character — 故用 ASCII `Inf` 命名,paper σ_∞ 在 docstring / 注释里保持原符号。

`deriving DecidableEq, Fintype` 提供 ℓ² Hilbert 结构(Cochain0 via PiLp 2)所需的
finite enumerability。 -/
inductive XsampVert : Type
  | σB
  | σInf
  deriving DecidableEq, Fintype

/-- Abstract sampling cell complex `X^A`(paper §5 def:Xsamp):
2 个 0-cell(σ_B, σ_∞)+ M 条 1-cells(每条 τ_i 从 σ_B 到 σ_∞)。

face₀ ↔ σ_B(incidence +1)/ face₁ ↔ σ_∞(incidence -1)
— 与 paper §5 + 7.1 Coboundary.lean 符号约定锁定一致。

`abbrev` 而非 `def`:Lean 4 type-class 搜索需在 `(Xsamp M).Cells₀` 能 unfold 到
`XsampVert` 才能找到 `Fintype` instance(Cochain0 PiLp 2 解析必需)。 -/
abbrev Xsamp (M : ℕ) : Complex1D where
  Cells₀ := XsampVert
  Cells₁ := Fin M
  face₀ := fun _ => XsampVert.σB
  face₁ := fun _ => XsampVert.σInf

/-- Well-formed example:M = 1(paper §5 minimal sampling instance)。 -/
example : Complex1D := Xsamp 1

/-- Sanity:`Xsamp M` 的 0-cell 类型自动可枚举(Fintype derive 通过)。 -/
example (M : ℕ) : Fintype (Xsamp M).Cells₀ := inferInstance

/-- Sanity:`Xsamp M` 的 1-cell 类型自动可枚举(`Fin M` 标准 Fintype)。 -/
example (M : ℕ) : Fintype (Xsamp M).Cells₁ := inferInstance

-- =============================================================
-- §2 Sampling sheaf(Samps,paper §5 def:sampling-sheaf)
-- =============================================================

section Samps

variable {M : ℕ} (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- 0-cell stalks of Samps:σ_B → E(paper V_B 抽象层)/ σ_∞ → EuclideanSpace ℂ (Fin 0)(paper 零 Hilbert)。

7.2 design DC4 接口定位:E 是 V_B 抽象,具体 `V_B ⊂ EuclideanSpace ℂ (Fin N)`
落 instantiation;本层只需 finite-dim ℂ-Hilbert 接口。

`abbrev`:type-class 搜索需在 `stalk0Samps E XsampVert.σB / σInf` 处 unfold
到 `E / EuclideanSpace ℂ (Fin 0)` 才能找到 NormedAddCommGroup / InnerProductSpace ℂ instance。 -/
abbrev stalk0Samps : XsampVert → Type
  | XsampVert.σB => E
  | XsampVert.σInf => EuclideanSpace ℂ (Fin 0)

/-- 1-cell stalks of Samps:每条 τ_i → ℂ(paper §5 def:sampling-sheaf)。 -/
abbrev stalk1Samps : Fin M → Type := fun _ => ℂ

/-- σ_B → E NormedAddCommGroup;σ_∞ → EuclideanSpace ℂ (Fin 0) NormedAddCommGroup。
`noncomputable` 因 EuclideanSpace 经 PiLp.normedAddCommGroup(noncomputable)derive。 -/
noncomputable instance (v : XsampVert) : NormedAddCommGroup (stalk0Samps E v) := by
  cases v <;> infer_instance

/-- σ_B → E InnerProductSpace ℂ;σ_∞ → EuclideanSpace ℂ (Fin 0) InnerProductSpace ℂ。
`noncomputable` 因 ℂ 的 RCLike instance 是 noncomputable(经 Complex.abs)。 -/
noncomputable instance (v : XsampVert) : InnerProductSpace ℂ (stalk0Samps E v) := by
  cases v <;> infer_instance

/-- Sampling sheaf `Samps E eval`(paper §5 def:sampling-sheaf):
- 0-cell stalks:σ_B → E,σ_∞ → EuclideanSpace ℂ (Fin 0)
- 1-cell stalks:τ_i → ℂ
- restrict₀ τ_i = eval τ_i:E → ℂ(paper σ_B ≤ τ_i,= eval_i)
- restrict₁ τ_i = 0:EuclideanSpace ℂ (Fin 0) → ℂ(paper σ_∞ ≤ τ_i,unique zero map) -/
noncomputable def Samps (eval : Fin M → E →L[ℂ] ℂ) :
    CellularSheaf (Xsamp M) (stalk0Samps E) (stalk1Samps (M := M)) where
  restrict₀ := fun τ => eval τ
  restrict₁ := fun _ => 0

/-- Sanity:`Samps E eval` 的 globalSections 类型可解析。 -/
noncomputable example (eval : Fin M → E →L[ℂ] ℂ) :
    Submodule ℂ (∀ v, stalk0Samps E v) :=
  (Samps E eval).globalSections

/-- Sanity:`Cochain0 (Xsamp M) (stalk0Samps E)` 在异型 stalks(E + EuclideanSpace ℂ (Fin 0))下
自动 derive `InnerProductSpace ℂ`(design §6 风险 2 实测验证)。 -/
noncomputable example :
    InnerProductSpace ℂ (Cochain0 (Xsamp M) (stalk0Samps E)) := inferInstance

/-- Sanity:`Cochain1 (Xsamp M) stalk1Samps` 自动 derive `InnerProductSpace ℂ`。 -/
noncomputable example :
    InnerProductSpace ℂ (Cochain1 (Xsamp M) (stalk1Samps (M := M))) := inferInstance

end Samps

-- =============================================================
-- §3 Canonical linear equivalence(operator 层,plain Π type)
--    paper §5 lem:canonical-isometry — operator-layer LinearEquiv;
--    Hilbert-layer LinearIsometryEquiv(PiLp 2 / Cochain0 + isometry
--    property `‖(c, 0)‖² = ‖c‖²`)在 Spectral.lean 同步 form
-- =============================================================

section CanonicalIsometry

variable {M : ℕ} (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- σ_∞ stalk(EuclideanSpace ℂ (Fin 0))上元素唯一(空向量)— paper §5 zero
    Hilbert space {0} 的 Lean 实现(Subsingleton.elim 用于 left_inv σInf 分支)。 -/
instance : Subsingleton (stalk0Samps E XsampVert.σInf) := by
  unfold stalk0Samps
  exact inferInstanceAs (Subsingleton (EuclideanSpace ℂ (Fin 0)))

/-- ι_B(paper §5 line 417):c ↦ (σ_B ↦ c, σ_∞ ↦ 0)。

    operator 层 plain Π type — 与 `(Samps E eval).coboundary` source
    类型对齐(Sections.lean discrepancy `(∀ v, stalk₀ v) →ₗ[ℂ] ...`)。 -/
noncomputable def canonicalIsometryBackward :
    E →ₗ[ℂ] (∀ v : XsampVert, stalk0Samps E v) where
  toFun c := fun v => match v with
    | XsampVert.σB => c
    | XsampVert.σInf => 0
  map_add' c c' := by funext v; cases v <;> simp
  map_smul' a c := by funext v; cases v <;> simp

/-- π_B(paper §5 line 416):s ↦ s σ_B。 -/
noncomputable def canonicalIsometryForward :
    (∀ v : XsampVert, stalk0Samps E v) →ₗ[ℂ] E where
  toFun s := s XsampVert.σB
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- canonical linear equivalence(operator 层,plain Π type)V_B ⊕ 0 ≅ V_B
    (paper §5 lem:canonical-isometry,LinearEquiv level)。

    Hilbert-level upgrade `canonicalLinearIsometryEquiv`(下方)承担 paper §5
    lem:canonical-isometry 的 isometry property `‖(c, 0)‖ = ‖c‖`。 -/
noncomputable def canonicalLinearEquiv :
    (∀ v : XsampVert, stalk0Samps E v) ≃ₗ[ℂ] E where
  toFun s := s XsampVert.σB
  invFun c := canonicalIsometryBackward E c
  left_inv s := by
    funext v
    cases v with
    | σB => rfl
    | σInf => exact Subsingleton.elim _ _
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- canonical LinearIsometryEquiv between Hilbert-layer `Cochain0` and `E`
    (paper §5 lem:canonical-isometry 的 isometry property 完整 form)。

    构造:LinearEquiv(operator 层 plain Π)+ `WithLp.linearEquiv 2`
    桥接到 PiLp 2 wrapper(Cochain0)。

    isometry property:
    `‖s‖_{PiLp 2}² = ∑ v ∈ XsampVert, ‖s v‖²`(by `PiLp.norm_eq_of_L2`)
    `= ‖s σB‖² + ‖s σInf‖²`(展开 XsampVert 2-element sum)
    `= ‖s σB‖² + 0`(σ_∞ stalk Subsingleton ⇒ `s σInf = 0`)
    `= ‖toLinearEquiv s‖²`(`toLinearEquiv s = s σB ∈ E`)。 -/
noncomputable def canonicalLinearIsometryEquiv :
    Cochain0 (Xsamp M) (stalk0Samps E) ≃ₗᵢ[ℂ] E where
  toLinearEquiv :=
    (WithLp.linearEquiv 2 ℂ _).trans (canonicalLinearEquiv E)
  norm_map' s := by
    rw [PiLp.norm_eq_of_L2]
    have hinf : s XsampVert.σInf = 0 := Subsingleton.elim _ _
    have huniv : (Finset.univ : Finset XsampVert) =
        {XsampVert.σB, XsampVert.σInf} := by decide
    rw [huniv, Finset.sum_pair (by decide : XsampVert.σB ≠ XsampVert.σInf),
        hinf, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero,
        Real.sqrt_sq (norm_nonneg _)]
    rfl

end CanonicalIsometry

-- =============================================================
-- §4 Sampling operator A + prop:delta-equals-A(operator-level equality)
--    paper §5 prop:delta-equals-A — plain Π layer
--    (EuclideanSpace ℂ (Fin M) PiLp 2 wrapper 桥接 Spectral.lean)
-- =============================================================

section DeltaEqualsA

variable {M : ℕ} (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Sampling operator `A : V_B → ℂ^M`(paper §5 eq:A-def):由 `eval : Fin M → E →L[ℂ] ℂ`
    装配为 LinearMap `E → (∀ _ : Fin M, ℂ)`(plain Π type)。

    EuclideanSpace ℂ (Fin M)(PiLp 2 wrapper)的 Hilbert-level wrap 在     Spectral.lean form(用于 paper §5 spec(A*A) = singular values²)。 -/
noncomputable def samplingOp (eval : Fin M → E →L[ℂ] ℂ) :
    E →ₗ[ℂ] (∀ _ : Fin M, ℂ) where
  toFun c := fun i => eval i c
  map_add' c c' := by funext i; simp
  map_smul' a c := by funext i; simp

/-- **paper §5 prop:delta-equals-A**(operator-level equality after canonical identification):

    在 canonical isometry `ι_B : E → ∀ v, stalk0Samps E v` 下,coboundary δ⁰
    与 sampling operator A 一致 — 即 `(Samps E eval).coboundary ∘ₗ
    canonicalIsometryBackward E = samplingOp E eval`。

    proof 走 paper §5 line 458-471:
    - `(δ⁰(c, 0))(τ_i) = [σ_B : τ_i] · samps(σ_B ≤ τ_i)(c)
                       + [σ_∞ : τ_i] · samps(σ_∞ ≤ τ_i)(0)`
    - `= (+1) · eval_i(c) + (-1) · 0 = eval_i(c)`

    Lean 实施:展开 `coboundary = discrepancy = restrict₀ - restrict₁`;
    `(Xsamp M).face₀ i = σB` / `face₁ i = σInf`(by Xsamp def);
    `canonicalIsometryBackward E c · σB = c` / `· σInf = 0`(by match);
    `(Samps E eval).restrict₀ i = eval i` / `restrict₁ i = 0`(by Samps def);
    `(0 : ...→L[ℂ] ℂ) 0 = 0`(by `ContinuousLinearMap.zero_apply`)。 -/
theorem coboundary_eq_sampling_op (eval : Fin M → E →L[ℂ] ℂ) :
    (Samps E eval).coboundary ∘ₗ canonicalIsometryBackward E = samplingOp E eval := by
  ext c i
  change (Samps E eval).restrict₀ i ((canonicalIsometryBackward E c) ((Xsamp M).face₀ i))
      - (Samps E eval).restrict₁ i ((canonicalIsometryBackward E c) ((Xsamp M).face₁ i))
    = (samplingOp E eval c) i
  change (eval i) c - (0 : EuclideanSpace ℂ (Fin 0) →L[ℂ] ℂ) 0 = eval i c
  simp

end DeltaEqualsA

-- =============================================================
-- §5 Hilbert-layer sampling operator(EuclideanSpace 桥接)
--    paper §5 lem:samps-cochain-spaces (C^1(samps) ≅ ℂ^M)
-- =============================================================

section SamplingOpEuclidean

variable {M : ℕ} (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Hilbert-layer sampling operator `A : E → ℂ^M`(paper §5 eq:A-def + lem:samps-cochain-spaces
    line 423-432:`C^1(samps) ≅ ℂ^M`)。

    operator 层(plain Π,§4 `samplingOp`)通过 `WithLp.linearEquiv 2` 桥接到
    Hilbert 层 PiLp 2 wrapper `EuclideanSpace ℂ (Fin M)`,用于 主定理
    `Samps.strict_equality` 中 singular value spec 桥接(`sq_singularValues_fin`)。 -/
noncomputable def samplingOpEuclidean (eval : Fin M → E →L[ℂ] ℂ) :
    E →ₗ[ℂ] EuclideanSpace ℂ (Fin M) :=
  (WithLp.linearEquiv 2 ℂ (Fin M → ℂ)).symm.toLinearMap ∘ₗ samplingOp E eval

/-- **paper §5 prop:delta-equals-A**(Hilbert-layer form,):

    在 `canonicalLinearIsometryEquiv : Cochain0 ≃ₗᵢ E` 下,`Samps` 的 Hilbert-layer
    coboundary `δ⁰ : Cochain0 → Cochain1` 与 Hilbert-layer sampling operator
    `A : E → EuclideanSpace ℂ (Fin M)` 一致(`Cochain1 = EuclideanSpace ℂ (Fin M)`
    by reducible def)— 即 `δ⁰ ∘ ι_B = A`(在 Hilbert 层)。

    proof 走 operator-layer `coboundary_eq_sampling_op` + WithLp.linearEquiv
    左右桥接。 -/
theorem coboundaryHilbert_eq_samplingOpEuclidean (eval : Fin M → E →L[ℂ] ℂ) :
    (Samps E eval).coboundaryHilbert ∘ₗ
      (canonicalLinearIsometryEquiv E).symm.toLinearMap
      = samplingOpEuclidean E eval := by
  ext c i
  change ((Samps E eval).coboundary (canonicalIsometryBackward E c)) i
    = ((samplingOp E eval) c) i
  exact congrFun (LinearMap.congr_fun (coboundary_eq_sampling_op E eval) c) i

end SamplingOpEuclidean

end MRI.Cellular
