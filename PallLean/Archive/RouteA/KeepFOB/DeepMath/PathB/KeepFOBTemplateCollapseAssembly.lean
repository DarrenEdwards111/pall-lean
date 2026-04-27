import PallLean.Archive.RouteA.KeepFOB.DeepMath.PathB.KeepFOBProjectedLowerBound
import PallLean.Archive.RouteA.KeepFOB.DeepMath.PathB.SATDeciderGaugeKeepFOBAssembly

/-!
# keepFOB assembly with template collapse

This file closes the `keepFOB` NP side using
`satDeciderGaugeKeepFOBProjection_npIdentityMinorPreservation` and leaves only
the honest template-collapse input on the P side.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation
open TuringMachine

/-- For the concrete `keepFOB` projection, bounded-profile template collapse
fills the P-side field, while the projected lower-bound file supplies NP
identity-minor preservation. -/
theorem satDeciderGaugeKeepFOBProjection_subgoals_of_boundedProfileTemplateCollapse
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hcollapse :
      WithinProfileBound.CookLevinProfileTemplateCollapseLemmaBoundedProfile
        M n hn2 htb hns) :
    SATDeciderGaugeSubgoals M n hn2 htb hns
      (satDeciderGaugeKeepFOBProjection M n hn2 htb hns) :=
  satDeciderGaugeSubgoals_of_boundedProfileTemplateCollapse
    M n hn2 htb hns
    (satDeciderGaugeKeepFOBProjection M n hn2 htb hns)
    (satDeciderGaugeKeepFOBProjection_rankMonotonicity M n hn2 htb hns)
    hcollapse
    (satDeciderGaugeKeepFOBProjection_npIdentityMinorPreservation
      M n hn hn2 htb hns)

/-- Per-instance rich projection target from the concrete `keepFOB` gauge and
bounded-profile template collapse.  No separate NP-preservation hypothesis is
needed. -/
theorem cookLevinRichProjectionTarget_of_keepFOB_boundedProfileTemplateCollapse
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hcollapse :
      WithinProfileBound.CookLevinProfileTemplateCollapseLemmaBoundedProfile
        M n hn2 htb hns) :
    CookLevinRichProjectionTarget M n hn hn2 htb hns :=
  ⟨satDeciderGaugeKeepFOBProjection M n hn2 htb hns,
    (satDeciderGaugeKeepFOBProjection_subgoals_of_boundedProfileTemplateCollapse
      M n hn hn2 htb hns hcollapse).1,
    (satDeciderGaugeKeepFOBProjection_subgoals_of_boundedProfileTemplateCollapse
      M n hn hn2 htb hns hcollapse).2.1,
    (satDeciderGaugeKeepFOBProjection_subgoals_of_boundedProfileTemplateCollapse
      M n hn hn2 htb hns hcollapse).2.2⟩

/-- All-profile template collapse version of the concrete `keepFOB` target. -/
theorem cookLevinRichProjectionTarget_of_keepFOB_templateCollapse
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hcollapse :
      WithinProfileBound.CookLevinProfileTemplateCollapseLemma
        M n hn2 htb hns) :
    CookLevinRichProjectionTarget M n hn hn2 htb hns :=
  cookLevinRichProjectionTarget_of_keepFOB_templateCollapse_npPreservation
    M n hn hn2 htb hns
    (satDeciderGaugeKeepFOBProjection_npIdentityMinorPreservation
      M n hn hn2 htb hns)
    hcollapse

/-- Uniform bounded-profile template collapse discharges the rich projection
target using the concrete `keepFOB` gauge. -/
theorem cookLevinRichProjectionDischarge_of_keepFOB_boundedProfileTemplateCollapse
    (hcollapse :
      ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        WithinProfileBound.CookLevinProfileTemplateCollapseLemmaBoundedProfile
          M n hn2 htb hns) :
    CookLevinRichProjectionDischarge := by
  intro M n hn hn2 htb hns _hdec
  exact cookLevinRichProjectionTarget_of_keepFOB_boundedProfileTemplateCollapse
    M n hn hn2 htb hns (hcollapse M n hn hn2 htb hns)

end PallLean.Paper93.DeepMath.PathB
