import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeFinalTarget
import PallLean.Paper93.FinalComposition

/-!
# SAT-decider gauge bridge from bounded-profile template collapse

This module connects the already-landed bounded-profile template-collapse
surface to the current Path B final targets.

The bridge is deliberately narrow:

* bounded-profile template collapse is first lifted through
  `WithinProfileBound.cookLevinProfileTemplateCollapseLemma_of_boundedProfile`;
* the P-side/projected contradiction route then reuses the existing
  `ProjectedIdentityMinorConcrete.false_of_cookLevin_templateCollapse_projected`;
* `CookLevinRichProjectionDischarge` is obtained only through its existing
  equivalence with `NoBoundedSATDeciderAtPaperScale`, so no final gauge witness
  is constructed here.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation
open TuringMachine

/-- Bounded-profile template collapse supplies the concrete projected P-side
bound used by the Path B projected contradiction package. -/
theorem cookLevinProjectedPSideBound_of_boundedProfileTemplateCollapse
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hcollapse :
      WithinProfileBound.CookLevinProfileTemplateCollapseLemmaBoundedProfile
        M n hn2 htb hns) :
    ProjectedIdentityMinorConcrete.CookLevinProjectedPSideBound
      M n hn2 htb hns :=
  ProjectedIdentityMinorConcrete.cookLevinProjectedPSideBound_of_templateCollapse
    M n hn htb hns hn2
    (WithinProfileBound.cookLevinProfileTemplateCollapseLemma_of_boundedProfile
      M n hn2 htb hns hcollapse)

/-- Fully instantiated projected Cook-Levin contradiction from the
bounded-profile template-collapse lemma. -/
theorem false_of_boundedProfileTemplateCollapse_projected
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hcollapse :
      WithinProfileBound.CookLevinProfileTemplateCollapseLemmaBoundedProfile
        M n hn2 htb hns) :
    False :=
  ProjectedIdentityMinorConcrete.false_of_cookLevinProjectedPSideBound
    M n hn htb hns hn2
    (cookLevinProjectedPSideBound_of_boundedProfileTemplateCollapse
      M n hn hn2 htb hns hcollapse)

/-- Per-instance rich-projection target packaging from bounded-profile
template collapse, provided a concrete gauge already has rank monotonicity and
NP identity-minor preservation.

This theorem does not assert gauge existence. -/
theorem cookLevinRichProjectionTarget_of_boundedProfileTemplateCollapse_of_npPreservation
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    (hrank : SATDeciderGaugeRankMonotonicity M n hn2 htb hns gauge)
    (hnp : SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns gauge)
    (hcollapse :
      WithinProfileBound.CookLevinProfileTemplateCollapseLemmaBoundedProfile
        M n hn2 htb hns) :
    CookLevinRichProjectionTarget M n hn hn2 htb hns :=
  cookLevinRichProjectionTarget_of_templateCollapse_of_npPreservation
    M n hn hn2 htb hns gauge hrank hnp
    (WithinProfileBound.cookLevinProfileTemplateCollapseLemma_of_boundedProfile
      M n hn2 htb hns hcollapse)

/-- A uniform bounded-profile template-collapse theorem rules out bounded
SAT deciders at the paper scale by the existing projected contradiction route. -/
theorem noBoundedSATDeciderAtPaperScale_of_boundedProfileTemplateCollapse
    (hcollapse : ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
      (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
      WithinProfileBound.CookLevinProfileTemplateCollapseLemmaBoundedProfile
        M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns _hdec
  exact false_of_boundedProfileTemplateCollapse_projected
    M n hn hn2 htb hns (hcollapse M n hn hn2 htb hns)

/-- A uniform bounded-profile template-collapse theorem discharges the rich
projection frontier only through the already-proved no-decider equivalence.

This is a vacuous discharge under the contradictory `DecidesSAT M` input, not a
construction of a final gauge. -/
theorem cookLevinRichProjectionDischarge_of_boundedProfileTemplateCollapse
    (hcollapse : ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
      (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
      WithinProfileBound.CookLevinProfileTemplateCollapseLemmaBoundedProfile
        M n hn2 htb hns) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_boundedProfileTemplateCollapse hcollapse)

/-- `Paper93.BoundedProfileTemplateCollapseDischarge` specialized to the Path B
no-bounded-SAT-decider target. -/
theorem noBoundedSATDeciderAtPaperScale_of_BoundedProfileTemplateCollapseDischarge
    (hDischarge : PallLean.Paper93.BoundedProfileTemplateCollapseDischarge) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_boundedProfileTemplateCollapse
    (fun M n _hn hn2 htb hns => hDischarge M n hn2 htb hns)

/-- `Paper93.BoundedProfileTemplateCollapseDischarge` specialized to the Path B
rich projection discharge, again through the no-decider equivalence rather than
through a constructed gauge. -/
theorem cookLevinRichProjectionDischarge_of_BoundedProfileTemplateCollapseDischarge
    (hDischarge : PallLean.Paper93.BoundedProfileTemplateCollapseDischarge) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_of_boundedProfileTemplateCollapse
    (fun M n _hn hn2 htb hns => hDischarge M n hn2 htb hns)

/-! ## Axiom audit anchors -/

#print axioms cookLevinProjectedPSideBound_of_boundedProfileTemplateCollapse
#print axioms false_of_boundedProfileTemplateCollapse_projected
#print axioms cookLevinRichProjectionTarget_of_boundedProfileTemplateCollapse_of_npPreservation
#print axioms noBoundedSATDeciderAtPaperScale_of_boundedProfileTemplateCollapse
#print axioms cookLevinRichProjectionDischarge_of_boundedProfileTemplateCollapse
#print axioms noBoundedSATDeciderAtPaperScale_of_BoundedProfileTemplateCollapseDischarge
#print axioms cookLevinRichProjectionDischarge_of_BoundedProfileTemplateCollapseDischarge

end PallLean.Paper93.DeepMath.PathB
