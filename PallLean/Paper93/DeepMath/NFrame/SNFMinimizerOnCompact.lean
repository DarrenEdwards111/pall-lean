import PallLean.Paper93.DeepMath.NFrame.ExistsMinOnCompact

namespace PallLean.Paper93.DeepMath.NFrame

/-- Generic existence: continuous function on a nonempty compact product attains minimum. -/
theorem exists_min_continuous_on_compact {X : Type*} [TopologicalSpace X]
    (s : Set X) (hs : IsCompact s) (hne : s.Nonempty)
    (f : X → ℝ) (hf : ContinuousOn f s) :
    ∃ x ∈ s, ∀ y ∈ s, f x ≤ f y :=
  exists_minimum_on_compact hs hne f hf

end PallLean.Paper93.DeepMath.NFrame
