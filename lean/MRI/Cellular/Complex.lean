/-
  MRI.Cellular.Complex — 1D cell complex(0-cells + 1-cells + face maps)

  实现。informal cross-ref:paper/v0.1 §3 双-Z₂ 模型。
-/

import Mathlib

namespace MRI.Cellular

/-- 1D cell complex:0-cells(顶点)+ 1-cells(边)+ face maps。

每个 1-cell `e ∈ Cells₁` 有两个端点 `face₀ e, face₁ e ∈ Cells₀`(unsigned incidence)。
Orientation convention(face₀ 是 tail 还是 head)在 `Coboundary.lean` 锁定 —
这一层只保证 incidence 数据结构 well-formed,不锁定方向语义。

Cross-ref:`paper/v0.1` §3(double-Z₂ sampling complex,双 0-cell + M edges)。
-/
structure Complex1D where
  Cells₀ : Type*
  Cells₁ : Type*
  face₀ : Cells₁ → Cells₀
  face₁ : Cells₁ → Cells₀

/-- Smallest non-trivial well-formed witness:两顶点 + 一条边。

对应 paper §3 的 minimal double-Z₂ instance(M = 1)。
M ≥ 2 的实例同形,只需把 `Cells₁` 换成 `Fin M`。
-/
example : Complex1D where
  Cells₀ := Fin 2
  Cells₁ := Unit
  face₀ := fun _ => 0
  face₁ := fun _ => 1

end MRI.Cellular
