import PallLean.Paper93.Paper283.RouteBMatrixToSATGauge
import PallLean.Paper93.DeepMath.PathB.ActiveProfileTemplateCollapseAssembly
import PallLean.ProfileCompression

/-!
# Route B transport P-side bound

This file names the real Cook-Levin P-side rank frontier in the Route B
transport vocabulary.  The target field
`RouteBSATUnprojectedPSideRankBound` is definitionally the unprojected
Cook-Levin SPDP rank estimate; the theorems below connect it to the currently
checked non-legacy profile-collapse surfaces.
-/

namespace PallLean.Paper93.Paper283

open TuringMachine
open WithinProfileBound

/-- The exact compiled-family within-profile theorem is enough for the Route B
unprojected SAT P-side rank field. -/
theorem routeBSATUnprojectedPSideRankBound_of_exactWithinProfileLemma
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hexact :
      CookLevinExactWithinProfileFinrankLemma M n hn2 htb hns) :
    RouteBSATUnprojectedPSideRankBound M n hn2 htb hns := by
  simpa [RouteBSATUnprojectedPSideRankBound] using
    ProfileCompression.p_side_rank_bound_for_cook_levin_of_exactWithinProfileLemma
      M n hn2 htb hns hexact

/-- A bounded-profile common-span theorem is enough for the Route B unprojected
SAT P-side rank field. -/
theorem routeBSATUnprojectedPSideRankBound_of_boundedProfileCommonSpan
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hspan : CookLevinBoundedProfileCommonSpanLemma M n hn2 htb hns) :
    RouteBSATUnprojectedPSideRankBound M n hn2 htb hns := by
  simpa [RouteBSATUnprojectedPSideRankBound] using
    ProfileCompression.p_side_rank_bound_for_cook_levin_of_boundedProfileCommonSpan
      M n hn2 htb hns hspan

/-- The all-bounded per-profile common-span frontier is enough for the Route B
unprojected SAT P-side rank field. -/
theorem routeBSATUnprojectedPSideRankBound_of_allBoundedProfileCommonSpan
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hspan : CookLevinAllBoundedProfileCommonSpanLemma M n hn2 htb hns) :
    RouteBSATUnprojectedPSideRankBound M n hn2 htb hns := by
  simpa [RouteBSATUnprojectedPSideRankBound] using
    ProfileCompression.p_side_rank_bound_for_cook_levin_of_allBoundedProfileCommonSpan
      M n hn2 htb hns hspan

/-- Active common-span blockers plus the zero-profile common-span blocker are
enough for the Route B unprojected SAT P-side rank field.  This is the
non-template active-profile route through the exact within-profile theorem. -/
theorem routeBSATUnprojectedPSideRankBound_of_activeTypeCaseBlockers_and_zeroProfileCommonSpan
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4)
    (hzero :
      PallLean.Paper93.DeepMath.PathB.CookLevinZeroHistogramShiftCommonSpan
        M n hn2 htb hns)
    (hblock :
      PallLean.Paper93.DeepMath.PathB.CookLevinActiveProfileTypeCaseBlockers
        M n hn2 htb hns) :
    RouteBSATUnprojectedPSideRankBound M n hn2 htb hns :=
  routeBSATUnprojectedPSideRankBound_of_exactWithinProfileLemma
    M n hn2 htb hns
    (PallLean.Paper93.DeepMath.PathB.cookLevinExactWithinProfileFinrankLemma_of_activeTypeCaseBlockers_and_zeroProfileCommonSpan
      M n hn2 htb hns hn4 hzero hblock)

/-- Bounded-profile template collapse is enough for the Route B unprojected SAT
P-side rank field, via the checked bounded-profile to all-profile lift. -/
theorem routeBSATUnprojectedPSideRankBound_of_boundedProfileTemplateCollapse
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hcollapse :
      CookLevinProfileTemplateCollapseLemmaBoundedProfile M n hn2 htb hns) :
    RouteBSATUnprojectedPSideRankBound M n hn2 htb hns := by
  simpa [RouteBSATUnprojectedPSideRankBound] using
    ProfileCompression.p_side_rank_bound_for_cook_levin_of_templateCollapse
      M n hn2 htb hns
      (cookLevinProfileTemplateCollapseLemma_of_boundedProfile
        M n hn2 htb hns hcollapse)

/-- Active-template blockers are enough for the Route B unprojected SAT P-side
rank field.  This keeps the Route B field reduced to the current active
profile/template-collapse frontier. -/
theorem routeBSATUnprojectedPSideRankBound_of_activeTemplateBlockers
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4)
    (hblock :
      PallLean.Paper93.DeepMath.PathB.CookLevinActiveProfileTemplateCollapseBlockers
        M n hn2 htb hns) :
    RouteBSATUnprojectedPSideRankBound M n hn2 htb hns :=
  routeBSATUnprojectedPSideRankBound_of_boundedProfileTemplateCollapse
    M n hn2 htb hns
    (PallLean.Paper93.DeepMath.PathB.cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_activeTemplateBlockers
      M n hn2 htb hns hn4 hblock)

/-! ## Axiom audit anchors -/

#print axioms routeBSATUnprojectedPSideRankBound_of_exactWithinProfileLemma
#print axioms routeBSATUnprojectedPSideRankBound_of_boundedProfileCommonSpan
#print axioms routeBSATUnprojectedPSideRankBound_of_allBoundedProfileCommonSpan
#print axioms routeBSATUnprojectedPSideRankBound_of_activeTypeCaseBlockers_and_zeroProfileCommonSpan
#print axioms routeBSATUnprojectedPSideRankBound_of_boundedProfileTemplateCollapse
#print axioms routeBSATUnprojectedPSideRankBound_of_activeTemplateBlockers

end PallLean.Paper93.Paper283
