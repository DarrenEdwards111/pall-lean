import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeContainmentAssembly
import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeKeepFOB

/-!
# Assembly for the `keepFOB` SAT-decider gauge candidate

This file connects the concrete `PiStarConcrete.keepFOB` projection to the
existing Path B rich-projection target surfaces.

The only concrete construction here is the witness
`PiStarConcrete.piZero PiStarConcrete.keepFOB`.  Its SPDP image-containment,
and hence rank monotonicity, follow from the existing generic `piZero`
criterion.  NP identity-minor preservation and the profile/template-collapse
frontier remain explicit honest hypotheses.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation
open TuringMachine

/-- Per-instance assembly: if `keepFOB` has NP preservation and the
profile-template-collapse frontier holds, then `keepFOB` is the witness for
the rich Cook-Levin projection target. -/
theorem cookLevinRichProjectionTarget_of_keepFOB_templateCollapse_npPreservation
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hnp :
      SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns
        (satDeciderGaugeKeepFOBProjection M n hn2 htb hns))
    (hcollapse :
      WithinProfileBound.CookLevinProfileTemplateCollapseLemma
        M n hn2 htb hns) :
    CookLevinRichProjectionTarget M n hn hn2 htb hns :=
  cookLevinRichProjectionTarget_of_containment_templateCollapse_npPreservation
    M n hn hn2 htb hns
    (satDeciderGaugeKeepFOBProjection M n hn2 htb hns)
    (satDeciderGaugeKeepFOBProjection_spdpSubspaceImageContainment
      M n hn2 htb hns)
    hnp hcollapse

/-- Bounded-profile form of the per-instance `keepFOB` assembly. -/
theorem cookLevinRichProjectionTarget_of_keepFOB_boundedProfileTemplateCollapse_npPreservation
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hnp :
      SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns
        (satDeciderGaugeKeepFOBProjection M n hn2 htb hns))
    (hcollapse :
      WithinProfileBound.CookLevinProfileTemplateCollapseLemmaBoundedProfile
        M n hn2 htb hns) :
    CookLevinRichProjectionTarget M n hn hn2 htb hns :=
  cookLevinRichProjectionTarget_of_keepFOB_templateCollapse_npPreservation
    M n hn hn2 htb hns hnp
    (WithinProfileBound.cookLevinProfileTemplateCollapseLemma_of_boundedProfile
      M n hn2 htb hns hcollapse)

/-- Global assembly: uniform NP preservation for the `keepFOB` witness plus a
uniform profile-template-collapse theorem discharges the rich-projection
target surface. -/
theorem cookLevinRichProjectionDischarge_of_keepFOB_templateCollapse_npPreservation
    (hnp :
      ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
        (_hdec : DecidesSAT M),
        SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns
          (satDeciderGaugeKeepFOBProjection M n hn2 htb hns))
    (hcollapse :
      ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        WithinProfileBound.CookLevinProfileTemplateCollapseLemma
          M n hn2 htb hns) :
    CookLevinRichProjectionDischarge := by
  intro M n hn hn2 htb hns hdec
  exact
    cookLevinRichProjectionTarget_of_keepFOB_templateCollapse_npPreservation
      M n hn hn2 htb hns
      (hnp M n hn hn2 htb hns hdec)
      (hcollapse M n hn hn2 htb hns)

/-- Global bounded-profile form: uniform NP preservation for `keepFOB` plus a
uniform bounded-profile template-collapse theorem discharges the rich
projection target surface. -/
theorem cookLevinRichProjectionDischarge_of_keepFOB_boundedProfileTemplateCollapse_npPreservation
    (hnp :
      ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
        (_hdec : DecidesSAT M),
        SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns
          (satDeciderGaugeKeepFOBProjection M n hn2 htb hns))
    (hcollapse :
      ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        WithinProfileBound.CookLevinProfileTemplateCollapseLemmaBoundedProfile
          M n hn2 htb hns) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_of_keepFOB_templateCollapse_npPreservation
    hnp
    (by
      intro M n hn hn2 htb hns
      exact WithinProfileBound.cookLevinProfileTemplateCollapseLemma_of_boundedProfile
        M n hn2 htb hns (hcollapse M n hn hn2 htb hns))

/-! ## Axiom audit anchors -/

#print axioms cookLevinRichProjectionTarget_of_keepFOB_templateCollapse_npPreservation
#print axioms cookLevinRichProjectionTarget_of_keepFOB_boundedProfileTemplateCollapse_npPreservation
#print axioms cookLevinRichProjectionDischarge_of_keepFOB_templateCollapse_npPreservation
#print axioms cookLevinRichProjectionDischarge_of_keepFOB_boundedProfileTemplateCollapse_npPreservation

end PallLean.Paper93.DeepMath.PathB
