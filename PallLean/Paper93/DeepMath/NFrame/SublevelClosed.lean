import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Sublevel-set closedness and lower semicontinuity of continuous functions

This file provides three convenience facts about continuous real-valued
functions on a topological space:

* `isClosed_sublevel`: the sublevel set `{x | f x ≤ c}` of a continuous
  function is closed.
* `preimage_closed_of_continuous`: the preimage of a closed set under a
  continuous function is closed.
* `Continuous.lowerSemicontinuous`: every continuous function (into an
  appropriate linearly ordered target) is lower semicontinuous.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- For a continuous `f`, the sublevel set `{x | f x ≤ c}` is closed. -/
theorem isClosed_sublevel {X : Type*} [TopologicalSpace X]
    (f : X → ℝ) (hf : Continuous f) (c : ℝ) :
    IsClosed {x | f x ≤ c} :=
  isClosed_le hf continuous_const

/-- Preimage of a closed set under a continuous function is closed. -/
theorem preimage_closed_of_continuous {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) {s : Set Y} (hs : IsClosed s) :
    IsClosed (f ⁻¹' s) :=
  hs.preimage hf

/-- A continuous function is lower semicontinuous. -/
theorem Continuous.lowerSemicontinuous {X : Type*} [TopologicalSpace X]
    {f : X → ℝ} (hf : Continuous f) : LowerSemicontinuous f :=
  hf.lowerSemicontinuous

end PallLean.Paper93.DeepMath.NFrame
