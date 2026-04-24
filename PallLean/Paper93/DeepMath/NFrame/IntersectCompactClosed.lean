import Mathlib.Topology.Compactness.Compact

namespace PallLean.Paper93.DeepMath.NFrame

/-- Intersection of a closed set with a compact set is compact.
    Wraps `IsCompact.inter_left` / `IsCompact.inter_right` from Mathlib. -/
theorem isCompact_inter_closed {X : Type*} [TopologicalSpace X]
    {s t : Set X} (hs : IsCompact s) (ht : IsClosed t) :
    IsCompact (s ∩ t) :=
  hs.inter_right ht

/-- `s ∩ t` compact when t compact. -/
theorem isCompact_closed_inter {X : Type*} [TopologicalSpace X]
    {s t : Set X} (hs : IsClosed s) (ht : IsCompact t) :
    IsCompact (s ∩ t) :=
  ht.inter_left hs

end PallLean.Paper93.DeepMath.NFrame
