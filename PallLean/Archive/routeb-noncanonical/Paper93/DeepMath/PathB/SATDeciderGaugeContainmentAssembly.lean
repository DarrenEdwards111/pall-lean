import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeFinalTarget
import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeRankMonotoneCriterion

/-!
# Assembly from SPDP containment to the final SAT-decider gauge target

This file connects the rank-monotone image-containment criterion to the final
Cook-Levin richer-projection target.

It does not construct `Π⋆`.  It records the exact reusable assembly theorem:
once a candidate gauge satisfies SPDP-subspace image containment, NP identity
minor preservation, and the honest Cook-Levin template-collapse P-side
frontier, it is a witness for the final target.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation
open TuringMachine

/-- Per-instance assembly theorem from the new SPDP image-containment criterion
to the final richer-projection target. -/
theorem cookLevinRichProjectionTarget_of_containment_templateCollapse_npPreservation
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    (hcontain :
      SATDeciderGaugeSPDPSubspaceImageContainment M n hn2 htb hns gauge)
    (hnp : SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns gauge)
    (hcollapse : WithinProfileBound.CookLevinProfileTemplateCollapseLemma
      M n hn2 htb hns) :
    CookLevinRichProjectionTarget M n hn hn2 htb hns :=
  cookLevinRichProjectionTarget_of_templateCollapse_of_npPreservation
    M n hn hn2 htb hns gauge
    (satDeciderGaugeRankMonotonicity_of_spdpSubspaceImageContainment
      M n hn2 htb hns gauge hcontain)
    hnp hcollapse

/-- Global assembly theorem for a uniform candidate-gauge construction stated
in terms of SPDP-subspace containment. -/
theorem cookLevinRichProjectionDischarge_of_uniform_containment_templateCollapse_npPreservation
    (hconstruct :
      ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
        (_hdec : DecidesSAT M),
        ∃ gauge : SATDeciderGaugeMap M n hn2 htb hns,
          SATDeciderGaugeSPDPSubspaceImageContainment M n hn2 htb hns gauge ∧
            SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns gauge)
    (hcollapse :
      ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        WithinProfileBound.CookLevinProfileTemplateCollapseLemma
          M n hn2 htb hns) :
    CookLevinRichProjectionDischarge := by
  intro M n hn hn2 htb hns hdec
  obtain ⟨gauge, hcontain, hnp⟩ :=
    hconstruct M n hn hn2 htb hns hdec
  exact
    cookLevinRichProjectionTarget_of_containment_templateCollapse_npPreservation
      M n hn hn2 htb hns gauge hcontain hnp
      (hcollapse M n hn hn2 htb hns)

/-- Bounded-profile template-collapse is enough for the same assembly, via the
existing bounded-profile-to-template-collapse bridge. -/
theorem cookLevinRichProjectionDischarge_of_uniform_containment_boundedProfileCollapse_npPreservation
    (hconstruct :
      ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
        (_hdec : DecidesSAT M),
        ∃ gauge : SATDeciderGaugeMap M n hn2 htb hns,
          SATDeciderGaugeSPDPSubspaceImageContainment M n hn2 htb hns gauge ∧
            SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns gauge)
    (hcollapse :
      ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        WithinProfileBound.CookLevinProfileTemplateCollapseLemmaBoundedProfile
          M n hn2 htb hns) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_of_uniform_containment_templateCollapse_npPreservation
    hconstruct
    (by
      intro M n hn hn2 htb hns
      exact WithinProfileBound.cookLevinProfileTemplateCollapseLemma_of_boundedProfile
        M n hn2 htb hns (hcollapse M n hn hn2 htb hns))

/-! ## Axiom audit anchors -/

#print axioms cookLevinRichProjectionTarget_of_containment_templateCollapse_npPreservation
#print axioms cookLevinRichProjectionDischarge_of_uniform_containment_templateCollapse_npPreservation
#print axioms cookLevinRichProjectionDischarge_of_uniform_containment_boundedProfileCollapse_npPreservation

end PallLean.Paper93.DeepMath.PathB
