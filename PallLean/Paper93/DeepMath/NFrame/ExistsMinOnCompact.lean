import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Extreme value theorem wrapper: minimum on a compact set

A continuous real-valued function on a nonempty compact set attains its minimum.
This file provides a thin, plainly-stated wrapper around Mathlib's
`IsCompact.exists_isMinOn` that returns the raw pointwise inequality
`∀ y ∈ s, f x ≤ f y` rather than the `IsMinOn` predicate.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- Continuous function on a nonempty compact set attains its minimum. Wraps Mathlib's
    `IsCompact.exists_isMinOn`. -/
theorem exists_minimum_on_compact {X : Type*} [TopologicalSpace X]
    {s : Set X} (hs : IsCompact s) (hne : s.Nonempty)
    (f : X → ℝ) (hf : ContinuousOn f s) :
    ∃ x ∈ s, ∀ y ∈ s, f x ≤ f y := by
  obtain ⟨x, hxs, hmin⟩ := hs.exists_isMinOn hne hf
  refine ⟨x, hxs, ?_⟩
  intros y hy
  exact hmin hy

end PallLean.Paper93.DeepMath.NFrame
