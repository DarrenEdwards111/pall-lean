import PallLean.Paper93.DeepMath.PathB.R72AmplituhedronFrontier
import PallLean.Paper93.DeepMath.PathB.ProjectedIdentityMinorConcrete
import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeTemplateCollapse

/-!
# Final SAT-decider gauge target

This file names the integrated remaining Π⋆ target for the real Cook-Levin
SAT-decider object.  The P-side collapse is kept as part of the same target,
because in the paper-faithful route the projection may have to be constructed
from the same profile/template-collapse machinery that proves the bound.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MultilinearSPDP
open PaperFaithfulSeparation
open TuringMachine

/-- Per-instance final richer projection target for the exact Cook-Levin
SAT-decider object.  This is just the three field obligations stated as one
integrated existence claim. -/
def CookLevinRichProjectionTarget
    (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ (gauge : SATDeciderGaugeMap M n hn2 htb hns),
    SATDeciderGaugeRankMonotonicity M n hn2 htb hns gauge ∧
      SATDeciderGaugePSideBound M n hn2 htb hns gauge ∧
        SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns gauge

/-- The named target is definitionally the existing explicit subgoal package. -/
theorem cookLevinRichProjectionTarget_iff_subgoals
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    CookLevinRichProjectionTarget M n hn hn2 htb hns ↔
      ∃ (gauge : SATDeciderGaugeMap M n hn2 htb hns),
        SATDeciderGaugeSubgoals M n hn2 htb hns gauge := by
  rfl

/-- Global final richer projection discharge for the SAT-decider branch. -/
def CookLevinRichProjectionDischarge : Prop :=
  ∀ (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (_hdec : DecidesSAT M),
    CookLevinRichProjectionTarget M n hn hn2 htb hns

/-- The integrated target is exactly the current SAT-decider gauge frontier. -/
theorem cookLevinRichProjectionDischarge_iff_satDeciderSpecificGaugeSubgoalDischarge :
    CookLevinRichProjectionDischarge ↔
      SATDeciderSpecificGaugeSubgoalDischarge := by
  rfl

/-- Consequently, the integrated Π⋆ target is equivalent to the already named
no-bounded-SAT-decider frontier.  This records that completing this target is
the final contradiction-strength theorem, not a bookkeeping lemma. -/
theorem cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider :
    CookLevinRichProjectionDischarge ↔
      NoBoundedSATDeciderAtPaperScale :=
  cookLevinRichProjectionDischarge_iff_satDeciderSpecificGaugeSubgoalDischarge.trans
    satDeciderSpecificGaugeSubgoalDischarge_iff_no_bounded_sat_decider

/-- Honest P-side bridge for the integrated target: if a candidate gauge is
rank-monotone, the current template-collapse frontier supplies its projected
P-side bound.  The NP-preservation field is deliberately not asserted here. -/
theorem satDeciderGaugePSideBound_of_rankMonotone_of_templateCollapse
    (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    (hrank : SATDeciderGaugeRankMonotonicity M n hn2 htb hns gauge)
    (hcollapse : WithinProfileBound.CookLevinProfileTemplateCollapseLemma
      M n hn2 htb hns) :
    SATDeciderGaugePSideBound M n hn2 htb hns gauge :=
  satDeciderGaugePSideBound_of_templateCollapse
    M n hn2 htb hns gauge hrank hcollapse

/-- If a candidate gauge has rank monotonicity and projected NP preservation,
then the template-collapse frontier completes the integrated Π⋆ target for
that candidate. -/
theorem cookLevinRichProjectionTarget_of_templateCollapse_of_npPreservation
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    (hrank : SATDeciderGaugeRankMonotonicity M n hn2 htb hns gauge)
    (hnp : SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns gauge)
    (hcollapse : WithinProfileBound.CookLevinProfileTemplateCollapseLemma
      M n hn2 htb hns) :
    CookLevinRichProjectionTarget M n hn hn2 htb hns :=
  ⟨gauge, hrank,
    satDeciderGaugePSideBound_of_rankMonotone_of_templateCollapse
      M n hn hn2 htb hns gauge hrank hcollapse,
    hnp⟩

/-- A uniform projected P-side bound on the concrete Step247 Cook-Levin output
already rules out bounded SAT deciders at the paper scale.  This is the honest
logical bridge: it does not construct a final gauge; it consumes the concrete
projected contradiction package. -/
theorem noBoundedSATDeciderAtPaperScale_of_cookLevinProjectedPSideBound
    (hP : ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
      (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
      ProjectedIdentityMinorConcrete.CookLevinProjectedPSideBound
        M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns _hdec
  exact ProjectedIdentityMinorConcrete.false_of_cookLevinProjectedPSideBound
    M n hn htb hns hn2 (hP M n hn hn2 htb hns)

/-- Uniform concrete projected P-side bounds discharge the integrated Π⋆
frontier, but only through the already proved no-decider equivalence. -/
theorem cookLevinRichProjectionDischarge_of_uniformProjectedPSideBound
    (hP : ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
      (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
      ProjectedIdentityMinorConcrete.CookLevinProjectedPSideBound
        M n hn2 htb hns) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_cookLevinProjectedPSideBound hP)

/-- A uniform template-collapse theorem for the concrete Cook-Levin family
would rule out bounded SAT deciders at the paper scale. -/
theorem noBoundedSATDeciderAtPaperScale_of_cookLevinTemplateCollapse
    (hcollapse : ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
      (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
      WithinProfileBound.CookLevinProfileTemplateCollapseLemma
        M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns _hdec
  exact ProjectedIdentityMinorConcrete.false_of_cookLevin_templateCollapse_projected
    M n hn htb hns hn2 (hcollapse M n hn hn2 htb hns)

/-- A uniform template-collapse theorem discharges the integrated Π⋆ frontier
through the no-decider equivalence. -/
theorem cookLevinRichProjectionDischarge_of_uniformTemplateCollapse
    (hcollapse : ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
      (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
      WithinProfileBound.CookLevinProfileTemplateCollapseLemma
        M n hn2 htb hns) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_cookLevinTemplateCollapse hcollapse)

/-- A uniform bounded-profile template-collapse theorem is already enough to
rule out bounded SAT deciders at the paper scale.  This is the smallest
currently named P-side frontier consumed by the final target. -/
theorem noBoundedSATDeciderAtPaperScale_of_cookLevinBoundedProfileTemplateCollapse
    (hcollapse : ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
      (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
      WithinProfileBound.CookLevinProfileTemplateCollapseLemmaBoundedProfile
        M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale := by
  apply noBoundedSATDeciderAtPaperScale_of_cookLevinTemplateCollapse
  intro M n hn hn2 htb hns
  exact WithinProfileBound.cookLevinProfileTemplateCollapseLemma_of_boundedProfile
    M n hn2 htb hns (hcollapse M n hn hn2 htb hns)

/-- A uniform bounded-profile template-collapse theorem discharges the
integrated Π⋆ frontier through the no-decider equivalence. -/
theorem cookLevinRichProjectionDischarge_of_uniformBoundedProfileTemplateCollapse
    (hcollapse : ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
      (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
      WithinProfileBound.CookLevinProfileTemplateCollapseLemmaBoundedProfile
        M n hn2 htb hns) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_cookLevinBoundedProfileTemplateCollapse
      hcollapse)

/-! ## Axiom audit anchors -/

#print axioms cookLevinRichProjectionTarget_iff_subgoals
#print axioms cookLevinRichProjectionDischarge_iff_satDeciderSpecificGaugeSubgoalDischarge
#print axioms cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider
#print axioms satDeciderGaugePSideBound_of_rankMonotone_of_templateCollapse
#print axioms cookLevinRichProjectionTarget_of_templateCollapse_of_npPreservation
#print axioms noBoundedSATDeciderAtPaperScale_of_cookLevinProjectedPSideBound
#print axioms cookLevinRichProjectionDischarge_of_uniformProjectedPSideBound
#print axioms noBoundedSATDeciderAtPaperScale_of_cookLevinTemplateCollapse
#print axioms cookLevinRichProjectionDischarge_of_uniformTemplateCollapse
#print axioms noBoundedSATDeciderAtPaperScale_of_cookLevinBoundedProfileTemplateCollapse
#print axioms cookLevinRichProjectionDischarge_of_uniformBoundedProfileTemplateCollapse

end PallLean.Paper93.DeepMath.PathB
