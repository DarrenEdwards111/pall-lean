/-
Copyright (c) 2026. All rights reserved.

Archived note: legacy `spdp_profile_generators` route.

This file intentionally contains no active proof dependency.  It records the
status of `SymmetricPower.spdp_profile_generators` as an archived / known-false
legacy surface so future Route B work does not accidentally revive it.

Summary:
* `SymmetricPower.spdp_profile_generators` is a legacy P-side profile-generator
  axiom.
* The repo flags it as provably inconsistent with the NP-side lower-bound route;
  see `PaperFaithfulSeparation.spdp_profile_generators_inconsistent_with_np_side`
  and `Archive/AxiomAnalysis.lean`.
* New paper-faithful Route B work should use the local-type / factor-fiber /
  selected-profile seams instead of trying to discharge or depend on
  `spdp_profile_generators` as stated.
* Treat any theorem whose `#print axioms` includes
  `SymmetricPower.spdp_profile_generators` as archival/legacy, not part of the
  active final route.
-/

namespace PallLean.Archive

/-- Marker for the archived known-false legacy `spdp_profile_generators` route. -/
theorem spdp_profile_generators_legacy_archived : True := trivial

end PallLean.Archive
