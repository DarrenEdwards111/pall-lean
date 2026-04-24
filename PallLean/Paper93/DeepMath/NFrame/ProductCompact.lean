import Mathlib.Topology.Constructions
import Mathlib.Topology.CompactOpen

/-!
# Product of compact sets is compact (N-Frame)

A thin Mathlib wrapper around `IsCompact.prod`: the product of two
compact sets (in the product topology) is compact.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- Product of compact sets is compact. Wraps `IsCompact.prod`. -/
theorem isCompact_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {s : Set X} {t : Set Y} (hs : IsCompact s) (ht : IsCompact t) :
    IsCompact (s ×ˢ t) :=
  hs.prod ht

end PallLean.Paper93.DeepMath.NFrame
