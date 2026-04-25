import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugePSideBridge

/-!
# SAT-decider gauge P-side from template collapse

This file packages the honest template-collapse P-side route into the
field-level SAT-decider gauge vocabulary.

It does not construct a SAT-decider gauge.  The gauge, rank-monotonicity, and
NP identity-minor preservation remain explicit hypotheses when needed.  The
only new work here is the P-side field: bounded-profile template collapse
implies the unprojected Cook-Levin rank bound, and rank monotonicity transports
that bound through the chosen gauge.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MultilinearSPDP
open PaperFaithfulSeparation
open TuringMachine

/-- All-profile template collapse supplies the SAT-decider gauge P-side field
for any already-rank-monotone gauge.

This is the honest replacement surface for the legacy flat P-side route: the
unprojected bound is obtained from the honest template-collapse theorem,
not from the legacy false profile-generator route or the bad unconditional
P-side theorem. -/
theorem satDeciderGaugePSideBound_of_templateCollapse
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    (hrank : SATDeciderGaugeRankMonotonicity M n hn2 htb hns gauge)
    (hcollapse :
      WithinProfileBound.CookLevinProfileTemplateCollapseLemma
        M n hn2 htb hns) :
    SATDeciderGaugePSideBound M n hn2 htb hns gauge :=
  satDeciderGaugePSideBound_of_rankMonotone_of_unprojected_bound
    M n hn2 htb hns gauge hrank
    (PaperFaithfulSeparation.p_side_rank_bound_for_cook_levin_of_templateCollapse
      M n hn2 htb hns hcollapse)

/-- Bounded-profile template collapse is enough for the SAT-decider gauge
P-side field, again for any already-rank-monotone gauge.

This is the finite-profile version used by the current paper-faithful route. -/
theorem satDeciderGaugePSideBound_of_boundedProfileTemplateCollapse
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    (hrank : SATDeciderGaugeRankMonotonicity M n hn2 htb hns gauge)
    (hcollapse :
      WithinProfileBound.CookLevinProfileTemplateCollapseLemmaBoundedProfile
        M n hn2 htb hns) :
    SATDeciderGaugePSideBound M n hn2 htb hns gauge :=
  satDeciderGaugePSideBound_of_templateCollapse
    M n hn2 htb hns gauge hrank
    (WithinProfileBound.cookLevinProfileTemplateCollapseLemma_of_boundedProfile
      M n hn2 htb hns hcollapse)

/-- If rank monotonicity and NP preservation are supplied for a chosen gauge,
bounded-profile template collapse fills in the missing P-side field and hence
packages the three explicit SAT-decider gauge subgoals.

No existence statement is made here: the gauge and the two non-P-side fields are
inputs. -/
theorem satDeciderGaugeSubgoals_of_boundedProfileTemplateCollapse
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    (hrank : SATDeciderGaugeRankMonotonicity M n hn2 htb hns gauge)
    (hcollapse :
      WithinProfileBound.CookLevinProfileTemplateCollapseLemmaBoundedProfile
        M n hn2 htb hns)
    (hNP :
      SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns gauge) :
    SATDeciderGaugeSubgoals M n hn2 htb hns gauge :=
  ⟨hrank,
    satDeciderGaugePSideBound_of_boundedProfileTemplateCollapse
      M n hn2 htb hns gauge hrank hcollapse,
    hNP⟩

/-!
## Axiom audit anchors
-/
#print axioms satDeciderGaugePSideBound_of_templateCollapse
#print axioms satDeciderGaugePSideBound_of_boundedProfileTemplateCollapse
#print axioms satDeciderGaugeSubgoals_of_boundedProfileTemplateCollapse

end PallLean.Paper93.DeepMath.PathB
