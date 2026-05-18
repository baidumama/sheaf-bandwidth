# paper ↔ Lean cross-reference

> This table is the bidirectional correspondence between the informal paper
> `paper/v0.1/main.pdf` (29 pages, 9 sections) and the Lean 4 formalization
> in `lean/MRI/Cellular/` (12 files, 2169 lines, 0 sorry / 0 admit / 0 warning).
>
> Status: `lake build` passes the entire library (8326 jobs).

---

## §3 Triangle Equivalence

| paper label | paper 类型 | Lean 文件 | Lean 名 |
|---|---|---|---|
| `thm:triangle-equiv` (line 110) | theorem | `TriangleEquivalence.lean` | **`triangle_equivalence`** (a)⇔(b)⇔(c),formalizes finite-dimensional operator/sheaf core; `V_B(V)` geometry treated as setup data |
| ↳ (a)⇔(b) Riesz form | — | `Variational.lean` | `triangle_equiv_a_iff_b` |
| ↳ (a)⇔(c) Robinson sheaf form | — | `TriangleEquivalence.lean` | `triangle_equiv_a_iff_c` |
| `def:sheafbw-candidate` (line 243) | definition | — | **no separate Lean def**;candidate form `σ_min(A)/σ_max(A)` 在 `TriangleEquivalence.lean:triangle_equiv_a_iff_c` 内 inline 展开为 ratio;the full-rank geometric equivalence to `sheafBW` on `Samps` is covered by `strict_equality_full_rank` |

**Bridge lemmas** (supporting §3):
- `Variational.lean:sq_singularValues_zero_eq_iSup_norm_sq` — σ_max² 球面 Rayleigh form
- `Variational.lean:sq_singularValues_last_eq_iInf_norm_sq` — σ_min² 球面 Rayleigh form
- `Variational.lean:injective_iff_singularValues_last_pos` — Injective ↔ σ_min > 0
- `TriangleEquivalence.lean:injective_samplingOp_iff_injective_samplingOpEuclidean` — WithLp 桥

---

## §5 Sheaf Bandwidth

### §5.1 sheafBW design (subsec:sheafbw-design, line 1-130)

| paper label | paper 类型 | Lean 文件 | Lean 名 |
|---|---|---|---|
| `def:sheafBW` (line 38) | definition | `Spectral.lean` | `sheafBW`;**general bound `sheafBW ∈ [0, 1]`** by `sheafBW_nonneg` + `sheafBW_le_one` 双侧 formalize;corner case "by convention 0 when δ⁰ ≡ 0" 由 `GammaPlus_eq_zero_iff_coboundaryHilbert_eq_zero` 桥(Lean 用 `Γ_+ = 0` 检测 ↔ paper `δ⁰ ≡ 0`)+ `gammaPlus_eq_zero_of_coboundaryHilbert_eq_zero` verify |
| `def:finite-dim-sheaf` (line 253) | definition | `Sheaf.lean` | **`CellularSheaf`** structure |
| `def:cochain-space` (line 270) | definition | `Inner.lean` | `Cochain0` + `Cochain1`(via PiLp 2) |
| `def:coboundary` (line 281) | definition | `Coboundary.lean` | `coboundary` + `coboundaryHilbert` |

### §5.2 Sheaf Laplacian + spectral gap (subsec:sheafbw-spectral-gap, line 131-191)

| paper label | paper 类型 | Lean 文件 | Lean 名 |
|---|---|---|---|
| `def:sheaf-laplacian` (line 137) | definition | `HilbertComplex.lean` | `sheafLaplacian0`(0-cochain Laplacian) |
| `def:spectral-gap` (line 154) | definition | `Spectral.lean` | `gammaPlus` + `GammaPlus`;**Scope declaration**:Lean 用 paper 第一条 form `Γ_+ := sup spec((δ^k)*δ^k) = singularValues 0 ^ 2`(经 mathlib `sq_singularValues_fin` 桥)。paper 第二条 identity `Γ_+ = ‖δ^k‖_op²` 经 mathlib `‖A* A‖ = ‖A‖²`(C* identity)+ symmetric-operator spectrum identity 间接等价,**本项目未独立 formalize 该 op-norm form**(下游所有 lemma 仅依赖 sup-spec form,不依赖 op-norm form;无 silent gap)|
| `lem:gap-well-defined` (line 171) | lemma | — | **auto-derive**:paper 内容是 "γ_+ / Γ_+ basis-independent,只依赖 sheaf categorical data";在 Lean 端 `LinearMap.singularValues` 本身即 operator invariant(不依赖 basis 表示),故无需单独定理。**Note**:mathlib4 `Mathlib/Analysis/InnerProductSpace/SingularValues.lean` 定义 `singularValues T := √(eigenvalues T.isSymmetric_adjoint_comp_self ...) `,其中 `eigenvalues` 是 self-adjoint operator 的 abstract spectral data,definitionally operator invariant(不依赖 basis 选择)。故 paper basis-independence 在 Lean 端是定义层 mechanical。注:这与 `prop:sheafBW-unitary`(跨 sheaves unitary equivalence)是不同命题,前者更弱(同 sheaf 换 basis)。 |

### §5.3 Unitary invariance

| paper label | paper 类型 | Lean 文件 | Lean 名 |
|---|---|---|---|
| `prop:sheafBW-unitary` (line 199) | proposition | `Unitary.lean` | **`sheafBW_eq`**;formalized on project `Complex1D` / `δ⁰` core,category packaging remains informal in §5.7 |

**Supporting structure & lemmas**:
- `Unitary.lean:UnitarySheafMorphism` structure(unitary sheaf morphism Φ : A → A')
- `Unitary.lean:discrepancy_commute` / `coboundaryHilbert_commute` / `coboundaryHilbert_commute_linearMap`
- `Unitary.lean:finrank_range_coboundaryHilbert_eq` / `singularValues_coboundaryHilbert_eq`
- `SamplingSpectral.lean:singularValues_comp_linearIsometryEquiv` / `singularValues_linearIsometryEquiv_comp`(unitary invariance of σ;mathlib PR candidates)

### §5.4 Closed Hilbert complex (subsec:sheafbw-hilbert-complex, line 243-334)

| paper label | paper 类型 | Lean 文件 | Lean 名 |
|---|---|---|---|
| `thm:closed-hilbert-complex` (line 296) | theorem | `HilbertComplex.lean` | **`coboundaryHilbert_range_isClosed`**(Complex1D/δ⁰ 条件 (d);(a)(b) finite-dim auto-derive,(c) vacuous;all-k finite-regular-cell-complex theorem 未包装为单个 Lean theorem) |
| `lem:L0-spectrum` (line 319) | lemma | `HilbertComplex.lean` | `sheafLaplacian0_isSymmetric` + `sheafLaplacian0_isPositive` + `sheafLaplacian0_ker_eq`;finite-spectrum/norm-bound consequences = mathlib standard facts,非单独 project theorem |

### §5.5 Xsamp + Samps (subsec:sheafBW-Xsamp, line 335-474)

| paper label | paper 类型 | Lean 文件 | Lean 名 |
|---|---|---|---|
| `def:Xsamp` (line 346) | definition | `Sampling.lean §1` | `XsampVert` + `Xsamp`(Complex1D instance) |
| `def:sampling-sheaf` (line 386) | definition | `Sampling.lean §2` | **`Samps`**(CellularSheaf instance) |
| `lem:canonical-isometry` (line 414) | lemma | `Sampling.lean §3` | `canonicalIsometryBackward` / `Forward` / `LinearEquiv` / **`canonicalLinearIsometryEquiv`** |
| `lem:samps-cochain-spaces` (line 423) | lemma | `Sampling.lean §3` | C⁰(Samps) ≅ V_B 经 `canonicalLinearIsometryEquiv` 实现 |

### §5.6 Strict equality

| paper label | paper 类型 | Lean 文件 | Lean 名 |
|---|---|---|---|
| `prop:delta-equals-A` (line 442) | proposition | `Sampling.lean §4` | `coboundary_eq_sampling_op`(operator/plain Π layer) + `coboundaryHilbert_eq_samplingOpEuclidean`(Hilbert/PiLp singular-value layer) |
| `thm:strict-equality` (line 481) | theorem | `SamplingSpectral.lean` | **paper full-rank form**:`strict_equality_full_rank` gives `sheafBW = σ_{K-1}/σ_0 ∈ (0,1]`;upper-boundary iff `sheafBW = 1 ↔ σ_{K-1}=σ_0` → `sheafBW_Samps_eq_one_iff_singularValues_domain_eq`;helper `strict_equality` / `sheafBW_Samps_eq_one_iff_singularValues_eq` cover positive-spectrum `finrank(range A)-1` form。注:paper "iff $A$ scalar multiple of isometry" 是 σ_min = σ_max 的几何 corollary,未独立形式化(paper footnote 显式 disclaim) |
| `cor:H0-vanishing` (line 527) | corollary | `TriangleEquivalence.lean` + `SamplingSpectral.lean` | **两条 statement 分别形式化**:(i) `H^0 = ker A` → `TriangleEquivalence.globalSections_comap_eq_ker_samplingOp`(Submodule.comap form);(ii) `H^0 = 0 ↔ σ_min > 0` → `TriangleEquivalence.globalSections_eq_bot_iff_singularValues_last_pos`;(intermediate) `SamplingSpectral.H0_vanishing_iff`(Injective form bridge) |

**Bridge theorems** (strict equality assembly):
- `SamplingSpectral.lean:singularValues_coboundaryHilbert_eq_samplingOpEuclidean`
- `SamplingSpectral.lean:range_samplingOpEuclidean_eq_range_coboundaryHilbert`
- `SamplingSpectral.lean:GammaPlus_Samps_eq_singularValues_zero_sq` / `gammaPlus_Samps_eq_singularValues_rank_pred_sq`
- `SamplingSpectral.lean:sheafBW_Samps_eq_singularValues_div`
- `SamplingSpectral.lean:canonicalIsometryBackward_bijective`

---

## C. Informal-only (not formalized; explicitly declared)

以下 paper label **不在 Lean 形式化范围**,以 informal-only 形态保留(显式 disclaim,不假装是 formal 证明)。

### §5.7 Unitary subcategory (line 566-629)

| paper label | 状态 | 理由 |
|---|---|---|
| `def:unitary-subcat` (line 573) | informal-only | 范畴论 setup(`CellSh^fin_Hilb,u(X)` 子范畴),Lean mathlib4 当前 cellular sheaf category 未充分建模,完整 category-theoretic 形式化超出当前范围 |
| `prop:unitary-groupoid` (line 584) | informal-only | 同上(子范畴是 groupoid + dagger structure);**核心 sheafBW 不变量性已被 `prop:sheafBW-unitary` (`Unitary.lean:sheafBW_eq`) 形式化捕捉**,groupoid 形态仅是范畴论包装 |

### §6 Three Instances (physical correspondence, line 358-373)

| paper label | 状态 | 理由 |
|---|---|---|
| `def:sampling-map` | informal-only(物理对应) | sampling map S: geometry → spectral data,物理映射(B-spline FE / quadrature / Bloch-Floquet ψ_θ),不是数学定理 |
| `def:integration-map` | informal-only(物理对应) | integration map I: geometry → quadrature error,同上 |

### §6 Empirical evidence

- `Empirical Proposition 8b` — empirical, marked with explicit evidence channels ("2 quantitative channels + heuristic"), not softened to a formal claim.

---

## A. paper §4 FEEC review (literature, 9 entries — not formalized)

paper §4 是 FEEC(Finite Element Exterior Calculus)文献综述,以下 label 均为外部已知结果引用,**不在本项目 formalize 范围**:

| label | 出处 |
|---|---|
| `prop:commuting-stokes` | Christiansen 2010 |
| `def:christiansen-fes` | Christiansen 2010 |
| `prop:fes-derham` | Christiansen 2010 Prop 2.10 |
| `def:afw-hilbert-complex` | Arnold-Falk-Winther 2010 + Brüning-Lesch 1992 |
| `thm:afw-hodge` | AFW 2010 §3.2 + BL 1992 |
| `def:bounded-pi` | AFW 2010 §3.1.1 + Falk-Winther 2014 |
| `thm:afw-cohomology` | AFW 2010 Thm 3.6 |
| `prop:galerkin-dagger` | Lahtinen-Stenvall 2020 |
| `def:bh-RI` | (内部定义,bridge 用) |

---

## File → paper index (reverse lookup)

| Lean 文件 | 行数 | 主要承载 paper labels |
|---|---|---|
| `Complex.lean` | 36 | (基础结构,§3 双-Z₂ 模型隐含) |
| `Sheaf.lean` | 48 | `def:finite-dim-sheaf` + `def:sampling-sheaf`(数据结构) |
| `Sections.lean` | 42 | (discrepancy + globalSections,§3 F1 + §5 def:cochain-space 辅助) |
| `Inner.lean` | 46 | `def:cochain-space` |
| `Coboundary.lean` | 73 | `def:coboundary` |
| `Sampling.lean` | 294 | `def:Xsamp` + `def:sampling-sheaf` + `lem:canonical-isometry` + `prop:delta-equals-A` |
| `Spectral.lean` | 198 | `def:sheafBW` + `def:spectral-gap` (含 `gammaPlus_eq_zero_of_coboundaryHilbert_eq_zero` + `GammaPlus_eq_zero_iff_coboundaryHilbert_eq_zero` + `gammaPlus_le_GammaPlus` + `sheafBW_le_one`) |
| `SamplingSpectral.lean` | 453 | **`thm:strict-equality`** + full-rank / boundary corollaries + `cor:H0-vanishing` bridge |
| `Variational.lean` | 471 | `thm:triangle-equiv` (a)⇔(b) + three mathlib PR candidates |
| `TriangleEquivalence.lean` | 195 | **`thm:triangle-equiv`** (a)⇔(c) + 三方 TFAE + H⁰ full-rank repair lemmas |
| `HilbertComplex.lean` | 99 | `thm:closed-hilbert-complex` + `lem:L0-spectrum` |
| `Unitary.lean` | 214 | **`prop:sheafBW-unitary`** |

---

## Mechanical verification status

- **Formal proof (Lean 4)**: the main results and supporting definitions/lemmas in the formalized scope are mechanically verified by `lake build`, 0 sorry / 0 admit / 0 warning.
- **Informal-only parts** (§5.7 category-theoretic packaging + §6 physical instances + Empirical 8b): explicitly disclaimed; not claimed to be formal theorems.
- **Scope declaration**: `def:spectral-gap` paper 第二条 identity `Γ_+ = ‖δ^k‖_op²` 在 Lean 端未独立 formalize(走 sup-spec form 替代,经 mathlib C* identity 间接等价);§5.2 已显式 disclaim,下游无 silent gap。
