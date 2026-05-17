import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedRank
import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeRealFrontier

/-!
# Boolean-projected Route C frontier

This file repackages Route C after the `mlProj` obstruction.

The old Route-C frontier asked for raw `Pi+` rank invariance.  That is not the
right target.  The repaired constructive gauge is

`Pi+ᵦ = zeroProfileBooleanNormalize ∘ Pi+`,

and the rank field is obtained from the backward generator transport criterion
proved in `PiPlusBooleanProjectedRank`.

The remaining Route-C fields are now the three actual SAT-gauge fields for this
projected gauge:

* backward projected generator transport, which gives rank monotonicity;
* the projected P-side bound;
* projected NP identity-minor preservation.

No raw algebra-equivalence claim is made here.
-/

namespace PallLean.Paper93.DeepMath.PathC

open PallLean.Paper93.DeepMath.PathB
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec

/-- The corrected Route-C frontier for the Boolean-projected `Pi+` gauge. -/
structure PiPlusBooleanProjectedSATGaugeFrontier
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns) : Prop where
  backward_generator_transport :
    PiPlusBooleanProjectedBackwardGeneratorTransport M n hn2 htb hns piP
  p_side_bound :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (piPlusBooleanProjectedGauge M n hn2 htb hns piP)
  identity_minor_preservation :
    SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns
      (piPlusBooleanProjectedGauge M n hn2 htb hns piP)

/-- The corrected Route-C frontier discharges the explicit SAT-decider gauge
subgoals for the Boolean-projected `Pi+` gauge. -/
theorem satDeciderGaugeSubgoals_of_piPlusBooleanProjected_frontier
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (F : PiPlusBooleanProjectedSATGaugeFrontier M n hn2 htb hns piP) :
    SATDeciderGaugeSubgoals M n hn2 htb hns
      (piPlusBooleanProjectedGauge M n hn2 htb hns piP) :=
  ⟨piPlusBooleanProjected_rankMonotonicity_of_backwardGeneratorTransport
      M n hn2 htb hns piP F.backward_generator_transport,
    F.p_side_bound,
    F.identity_minor_preservation⟩

/-- Paper-scale abbreviation for the corrected Boolean-projected Route-C
frontier. -/
abbrev PaperScalePiPlusBooleanProjectedSATGaugeFrontier
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusBooleanProjectedSATGaugeFrontier M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns)

/-- Paper-scale corrected Route C discharges the explicit SAT-decider gauge
subgoals for the concrete Boolean-projected `Pi+` gauge. -/
theorem satDeciderGaugeSubgoals_paperScale_of_piPlusBooleanProjected_frontier
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (F : PaperScalePiPlusBooleanProjectedSATGaugeFrontier M htb hns) :
    SATDeciderGaugeSubgoals M (2 ^ 804) paperScale_ge_two htb hns
      (cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns) := by
  exact satDeciderGaugeSubgoals_of_piPlusBooleanProjected_frontier
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns) F

/-- A paper-scale Route-C closure proposition using the corrected
Boolean-projected `Pi+` gauge.  This is intentionally SAT-decider-specific: it
only asks for the frontier under the `DecidesSAT M` hypothesis consumed by the
NP identity-minor field. -/
def PaperScalePiPlusBooleanProjectedRouteCClosure : Prop :=
  ∀ (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (_hdec : DecidesSAT M),
    PaperScalePiPlusBooleanProjectedSATGaugeFrontier M htb hns

/-- Corrected Route C closes the exact paper-scale SAT-decider gauge-discharge
frontier at `n = 2^804`. -/
theorem satDeciderSpecificGaugeSubgoalDischarge_at_paperScale_of_piPlusBooleanProjectedRouteCClosure
    (hC : PaperScalePiPlusBooleanProjectedRouteCClosure) :
    ∀ (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
      (_hdec : DecidesSAT M),
      ∃ (gauge : SATDeciderGaugeMap M (2 ^ 804) paperScale_ge_two htb hns),
        SATDeciderGaugeSubgoals M (2 ^ 804) paperScale_ge_two htb hns gauge := by
  intro M htb hns hdec
  exact ⟨cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns,
    satDeciderGaugeSubgoals_paperScale_of_piPlusBooleanProjected_frontier
      M htb hns (hC M htb hns hdec)⟩

/-- At exact paper scale, the corrected Route-C closure is already logically
incompatible with a bounded SAT decider.  This is the same P-side/NP-side gap as
Route B, now specialized to the Boolean-projected `Pi+` gauge. -/
theorem no_decidesSAT_at_paperScale_of_piPlusBooleanProjectedRouteCClosure
    (hC : PaperScalePiPlusBooleanProjectedRouteCClosure)
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    ¬ DecidesSAT M := by
  intro hdec
  obtain ⟨gauge, hsub⟩ :=
    satDeciderSpecificGaugeSubgoalDischarge_at_paperScale_of_piPlusBooleanProjectedRouteCClosure
      hC M htb hns hdec
  exact not_satDeciderGaugeSubgoals_at_large_n
    M (2 ^ 804) (le_rfl : 2 ^ 804 ≥ 2 ^ 804) paperScale_ge_two htb hns
    gauge hdec hsub

/-! ## Axiom audit anchors -/

#print axioms satDeciderGaugeSubgoals_of_piPlusBooleanProjected_frontier
#print axioms satDeciderGaugeSubgoals_paperScale_of_piPlusBooleanProjected_frontier
#print axioms satDeciderSpecificGaugeSubgoalDischarge_at_paperScale_of_piPlusBooleanProjectedRouteCClosure
#print axioms no_decidesSAT_at_paperScale_of_piPlusBooleanProjectedRouteCClosure

end PallLean.Paper93.DeepMath.PathC
