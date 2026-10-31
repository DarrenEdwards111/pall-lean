import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameOrientedChargeEndpoint
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPDynamicHolonomyQueryTranscriptBridge

/-!
# Solver-induced oriented conservation: correctness no-go and exact calibration

The complete weighted orientation charge separates all search labels, and a
polynomial positive-cell amplituhedron cannot conserve it.  The remaining
proposal is therefore:

```text
SAT decision correctness -> conservation of the complete oriented charge.
```

This file tests that implication directly.

First, a truth-flat residual family gives the counterexample.  Every branch is
the same satisfiable CNF, so the constant-`true` Boolean observer is correct on
the entire family.  The branches still carry distinct search labels.  A
one-cell amplituhedron may merge them without losing the SAT decision, but it
cannot conserve their complete oriented charge.

Second, the global claim that every correct SAT decider induces such a
polynomial conservation package is calibrated exactly.  Each individual
package is contradictory by the oriented-charge lower bound, so the universal
claim is equivalent to `¬ SATDecisionInP U`: its reverse direction is vacuous
because no correct decider remains.

Thus decision correctness alone cannot be the missing conservation law.  A
successful proof needs a new *decision-relevance/self-reduction theorem* tying
all search labels to actual SAT answers under continuations.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameSolverOrientedConservationNoGo

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPObserverSwitchToy
open PallLean.Paper93.DeepMath.PathB.PvsNPTranscriptObserver
open PallLean.Paper93.DeepMath.PathB.PvsNPRamanujanHolographicAmplituhedronExtraction
open PallLean.Paper93.DeepMath.PathB.PvsNPDynamicHolonomyQueryTranscriptBridge
open PallLean.Paper93.DeepMath.PathB.NFrameOrientedChargeEndpoint

/-! ## A truth-flat, search-label-rich family -/

/-- Every branch contains the same trivially satisfiable residual CNF. -/
def truthFlatResidual : ResidualInstance where
  φ := yesCNF
  pref := []

/-- Identity search labels over a completely truth-flat SAT family. -/
def truthFlatFoolingFamily (m : Nat) : FoolingResidualFamily m :=
  identityFoolingFamily m (fun _ => truthFlatResidual)

theorem truthFlat_all_satisfiable (m : Nat) (a : Assignment m) :
    Satisfiable ((truthFlatFoolingFamily m).instanceOf a).φ :=
  yesCNF_satisfiable

/-- The constant-true Boolean observer is perfectly correct on this entire
family. -/
theorem constantTrue_correct_on_truthFlat (m : Nat) :
    forall a : Assignment m,
      true = satTruth ((truthFlatFoolingFamily m).instanceOf a).φ := by
  intro a
  exact (satTruth_yesCNF).symm

/-! ## A one-cell Ramanujan/amplituhedron presentation -/

def flatRamanujanCertificate : RamanujanBoundaryCertificate where
  vertices := 1
  degree := 0
  spectralSlack := 0
  expansionPayload := True
  expansion_realized := trivial

def flatHolographicStage : HolographicProjectionStage PUnit PUnit where
  ramanujan := flatRamanujanCertificate
  projectToScreen := fun _ => PUnit.unit
  boundary_respects_expander := True
  boundary_respects_expander_realized := trivial

def flatAmplituhedronStage : AmplituhedronPositiveCellStage PUnit PUnit where
  projectToCell := fun _ => PUnit.unit
  positiveCell := fun _ => True
  project_positive := fun _ => trivial
  orientationPayload := True
  orientation_realized := trivial

def flatRawObserver : TranscriptObserver PUnit := fun _ => PUnit.unit

/-- Despite perfect Boolean correctness, no real-valued action on the single
positive cell can conserve both one-bit oriented labels. -/
theorem truthFlat_correct_but_no_orientedConservation :
    (forall a : Assignment 1,
      true = satTruth ((truthFlatFoolingFamily 1).instanceOf a).φ) ∧
    (forall cellAction : PUnit -> Real,
      ¬ (forall a : Assignment 1,
        weightedOrientationAction ((truthFlatFoolingFamily 1).label a) =
          cellAction
            (composedPositiveProjection flatHolographicStage
              flatAmplituhedronStage
              (flatRawObserver ((truthFlatFoolingFamily 1).instanceOf a))))) := by
  constructor
  · exact constantTrue_correct_on_truthFlat 1
  · intro cellAction
    exact no_polynomial_amplituhedron_conserves_orientedAction (m := 1) (k := 0)
      flatRawObserver flatHolographicStage flatAmplituhedronStage
      (truthFlatFoolingFamily 1) cellAction
      (by norm_num) (by norm_num)

/-! ## Exact global calibration -/

/-- The proposed solver-induced conservation package for one correct SAT
decider.  Its fields are precisely the complete-charge conservation law,
polynomial positive-cell boundary, and exponential gap. -/
structure SolverInducedOrientedConservationFor
    (U : MachineModel) (D : DecisionMachine U) (hD : DecidesSAT U D) where
  m : Nat
  k : Nat
  raw : Type
  screen : Type
  cell : Type
  fintypeCell : Fintype cell
  rawObserver : TranscriptObserver raw
  holographic : HolographicProjectionStage raw screen
  amplituhedron : AmplituhedronPositiveCellStage screen cell
  fam : FoolingResidualFamily m
  cellAction : cell -> Real
  conserves : forall a : Assignment m,
    weightedOrientationAction (fam.label a) =
      cellAction
        (composedPositiveProjection holographic amplituhedron
          (rawObserver (fam.instanceOf a)))
  polyCells : @Fintype.card cell fintypeCell <= m ^ k
  expGap : m ^ k < 2 ^ m

namespace SolverInducedOrientedConservationFor

variable {U : MachineModel} {D : DecisionMachine U} {hD : DecidesSAT U D}

/-- Every individual proposed package is contradictory, without using any
additional property of the solver. -/
theorem impossible (E : SolverInducedOrientedConservationFor U D hD) : False := by
  letI : Fintype E.cell := E.fintypeCell
  exact no_polynomial_amplituhedron_conserves_orientedAction
    E.rawObserver E.holographic E.amplituhedron E.fam E.cellAction
    E.polyCells E.expGap E.conserves

end SolverInducedOrientedConservationFor

/-- Global assertion that SAT correctness itself supplies the full conserved
orientation package. -/
def EverySATDeciderInducesOrientedConservation (U : MachineModel) : Prop :=
  forall (D : DecisionMachine U) (hD : DecidesSAT U D),
    Nonempty (SolverInducedOrientedConservationFor U D hD)

/-- Exact calibration: the proposed universal solver-to-conservation theorem
is equivalent to the SAT lower bound.  The reverse construction contains no
geometry; it eliminates the impossible correctness premise. -/
theorem everySATDeciderInducesOrientedConservation_iff
    (U : MachineModel) :
    EverySATDeciderInducesOrientedConservation U ↔ ¬ SATDecisionInP U := by
  constructor
  · intro H hSAT
    obtain ⟨D, hD⟩ := hSAT
    obtain ⟨E⟩ := H D hD
    exact E.impossible
  · intro hNo D hD
    exact False.elim (hNo ⟨D, hD⟩)

end PallLean.Paper93.DeepMath.PathB.NFrameSolverOrientedConservationNoGo

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameSolverOrientedConservationNoGo.truthFlat_correct_but_no_orientedConservation
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameSolverOrientedConservationNoGo.SolverInducedOrientedConservationFor.impossible
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameSolverOrientedConservationNoGo.everySATDeciderInducesOrientedConservation_iff
