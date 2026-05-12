import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeDischargeSubgoals
import PallLean.Paper93.DeepMath.PathB.ZeroGaugeNPIdentityMinorObstruction
import PallLean.Paper93.NFrame.NontrivialIdentityMinorObstruction
import PallLean.Paper93.NFrame.UnitPreservingAdmissible
import PallLean.Paper93.NFrame.UnitPreservingValueSet
import PallLean.Paper93.NFrame.NonTrivialGaugeHypotheses

/-!
# Path B R71 amplituhedron progress surface

This file is a wrapper surface only.  It lists the R71 progress that is now
available without pretending to close the remaining final gauge axiom:

* the SAT-decider gauge frontier is equivalent to its three explicit subgoals;
* the zero gauge cannot discharge those subgoals at the paper scale;
* the unit-preserving N-frame minimizer surface is nonzero;
* the concrete constants projection satisfies the currently provable
  N-frame hypotheses for the constant-one family.

No theorem in this file asserts `SATDeciderSpecificGaugeDischarge` or
`SATDeciderSpecificGaugeSubgoalDischarge`.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MvPolynomial
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.NFrame

/-- R71 field-level subgoal equivalence surface. -/
def R71FieldSubgoalEquivalenceSurface : Prop :=
  ∀ (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns),
    SATDeciderGaugeSubgoals M n hn2 htb hns gauge ↔
      GlobalGodMoveGauge.IsAmplituhedronGauge M n hn hn2 htb hns gauge

/-- R71 top-level frontier equivalence surface. -/
def R71FrontierSubgoalEquivalenceSurface : Prop :=
  SATDeciderSpecificGaugeSubgoalDischarge ↔
    SATDeciderSpecificGaugeDischarge

/-- R71 zero-gauge obstruction surface at the paper scale. -/
def R71ZeroGaugeObstructionSurface : Prop :=
  ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (_hdec : DecidesSAT M),
    ¬ SATDeciderGaugeSubgoals M n hn2 htb hns
      (0 : SATDeciderGaugeMap M n hn2 htb hns)

/-- R71 unit-preserving minimizer surface: a minimizer exists, its projection
is nonzero, and its natural N-frame value is nonzero. -/
def R71UnitPreservingMinimizerNonzeroSurface : Prop :=
  ∀ (N : Nat) (family : Nat → MvPolynomial (Fin N) Rat),
    ∃ Pi : CandidateGauge N,
      UnitPreservingAdmissibleGauge Pi ∧
        Pi.projection ≠ 0 ∧
        lagrangianNat Pi ≠ 0 ∧
        ∀ Pi' : CandidateGauge N,
          UnitPreservingAdmissibleGauge Pi' →
            nframeLagrangian family Pi ≤ nframeLagrangian family Pi'

/-- R71 constants-gauge hypotheses surface for the current concrete SPDP rank
functional and the constant-one family. -/
def R71ConstantsGaugeHypothesesSurface : Prop :=
  ∀ (N : Nat) (B : SPDP.BlockPartition N) (κ ℓ : Nat), 1 ≤ κ →
    AdmissibleGauge (PallLean.Paper93.Substantive.nonTrivialGauge N) ∧
      RankMonotoneHypothesis
        (PallLean.Paper93.Substantive.nonTrivialGauge N)
        (spdpRankFunctional B κ ℓ) ∧
      IdentityMinorPreservationHypothesis
        (PallLean.Paper93.Substantive.nonTrivialGauge N)
        (constantOneFamily N) ∧
      PSideCollapseHypothesis
        (PallLean.Paper93.Substantive.nonTrivialGauge N)
        (constantOneFamily N) (spdpRankFunctional B κ ℓ)

/-- The R71 progress surface deliberately lists progress only; it does not
inhabit the remaining SAT-decider gauge discharge. -/
def R71AmplituhedronProgressSurface : Prop :=
  R71FieldSubgoalEquivalenceSurface ∧
    R71FrontierSubgoalEquivalenceSurface ∧
    R71ZeroGaugeObstructionSurface ∧
    R71UnitPreservingMinimizerNonzeroSurface ∧
    R71ConstantsGaugeHypothesesSurface

/-- Field-level equivalence between the explicit three subgoals and the
bundled `GlobalGodMoveGauge.IsAmplituhedronGauge` record. -/
theorem r71_field_subgoal_equivalence :
    R71FieldSubgoalEquivalenceSurface := by
  intro M n hn hn2 htb hns gauge
  exact satDeciderGaugeSubgoals_iff_isAmplituhedronGauge
    M n hn hn2 htb hns gauge

/-- Top-level equivalence between the explicit three-subgoal frontier and the
R70 bundled SAT-decider gauge frontier. -/
theorem r71_frontier_subgoal_equivalence :
    R71FrontierSubgoalEquivalenceSurface :=
  satDeciderSpecificGaugeSubgoalDischarge_iff

/-- At `n ≥ 2^804`, the zero linear gauge cannot satisfy the explicit
SAT-decider gauge subgoals for a SAT-deciding machine. -/
theorem r71_zeroGauge_obstruction_at_large_n :
    R71ZeroGaugeObstructionSurface := by
  intro M n hn hn2 htb hns hdec
  exact zeroGauge_not_satDeciderGaugeSubgoals_at_large_n
    M n hn hn2 htb hns hdec

/-- The unit-preserving N-frame minimizer surface is nonzero: any minimizer
returned by the unit-preserving value-set construction has nonzero projection
and nonzero natural Lagrangian value. -/
theorem r71_unitPreserving_minimizer_nonzero :
    R71UnitPreservingMinimizerNonzeroSurface := by
  intro N family
  obtain ⟨Pi, hUnit, hmin⟩ :=
    unitPreserving_minimizer_exists (N := N) family
  have hproj : Pi.projection ≠ 0 :=
    unitPreserving_projection_ne_zero hUnit
  have hnat : lagrangianNat Pi ≠ 0 :=
    Nat.pos_iff_ne_zero.mp (unitPreserving_lagrangianNat_pos hUnit)
  exact ⟨Pi, hUnit, hproj, hnat, hmin⟩

/-- The concrete constants projection satisfies the currently proved
rank-monotone, constant-one identity-minor, and P-side-collapse hypotheses. -/
theorem r71_constantsGauge_hypotheses :
    R71ConstantsGaugeHypothesesSurface := by
  intro N B κ ℓ hκ
  exact nonTrivialGauge_constantOne_hypotheses B hκ

/-- The combined R71 progress theorem.  This is a theorem listing only: it
does not assert the final SAT-decider gauge discharge. -/
theorem r71_amplituhedron_progress_surface :
    R71AmplituhedronProgressSurface := by
  exact
    ⟨r71_field_subgoal_equivalence,
      r71_frontier_subgoal_equivalence,
      r71_zeroGauge_obstruction_at_large_n,
      r71_unitPreserving_minimizer_nonzero,
      r71_constantsGauge_hypotheses⟩

/-!
## Axiom audit anchors

These anchors should not include a proof of the remaining final frontier:
`SATDeciderSpecificGaugeDischarge` and
`SATDeciderSpecificGaugeSubgoalDischarge` remain explicit propositions, not
closed theorems.
-/
#print axioms r71_field_subgoal_equivalence
#print axioms r71_frontier_subgoal_equivalence
#print axioms r71_zeroGauge_obstruction_at_large_n
#print axioms r71_unitPreserving_minimizer_nonzero
#print axioms r71_constantsGauge_hypotheses
#print axioms r71_amplituhedron_progress_surface

end PallLean.Paper93.DeepMath.PathB
