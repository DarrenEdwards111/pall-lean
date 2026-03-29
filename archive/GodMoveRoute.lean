import PallLean.GodMoveExtraction

/-!
# GodMoveRoute

A small wrapper module collecting the paper-faithful God-Move route.

Use this as the integration point when wiring the extraction theorem into a
future active separation pipeline.
-/

namespace GodMoveRoute

open GodMoveExtraction SPDP

/-- Marker theorem name matching the paper-faithful extraction inequality route. -/
theorem godMove_extraction_rank_monotone
    {F : Type*} [Field F] {n m : ℕ}
    (D : GodMoveData (F := F) n m) :
    blockedSpdpRank D.hardPart D.κ D.ℓ D.hardPoly ≤
      blockedSpdpRank D.compiledPart D.κ D.ℓ D.compiledPoly :=
  GodMoveExtraction.godMove_extraction_rank_monotone D

/-- Same-space version for embedded hard objects already living in the compiled space. -/
theorem godMove_extraction_rank_monotone_sameSpace
    {F : Type*} [Field F] {n : ℕ}
    (D : SameSpaceGodMoveData (F := F) n) :
    blockedSpdpRank D.part D.κ D.ℓ D.hardPoly ≤
      blockedSpdpRank D.part D.κ D.ℓ D.compiledPoly :=
  GodMoveExtraction.godMove_extraction_rank_monotone_sameSpace D

end GodMoveRoute
