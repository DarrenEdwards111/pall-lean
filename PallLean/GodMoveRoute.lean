import PallLean.GodMoveExtraction

/-!
# GodMoveRoute

A small wrapper module collecting the paper-faithful God-Move route.

Use this as the integration point when wiring the extraction theorem into a
future active separation pipeline.
-/

namespace GodMoveRoute

open GodMoveExtraction

/-- Marker theorem name matching the paper-faithful extraction inequality route. -/
abbrev godMove_extraction_rank_monotone :=
  GodMoveExtraction.godMove_extraction_rank_monotone

/-- Same-space version for embedded hard objects already living in the compiled space. -/
abbrev godMove_extraction_rank_monotone_sameSpace :=
  GodMoveExtraction.godMove_extraction_rank_monotone_sameSpace

end GodMoveRoute
