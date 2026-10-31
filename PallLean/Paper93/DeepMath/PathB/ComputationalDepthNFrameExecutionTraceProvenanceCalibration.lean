import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameDecisionDerivedResidualBarrier

/-!
# Execution-trace provenance calibration

The abstract `MachineModel` exposes a solver's final result and step count but
no internal execution object.  This file adds the minimal trace extension: a
trace-producing run together with a certified projection from traces back to
the original Boolean decision.

A residual has trace provenance when it is obtained by postprocessing this
execution trace.  Two extreme trace disciplines are then calibrated.

* An input-retaining trace `(formula, decision)` is a valid trace extension.
  Whenever the continuation encoding can be decoded, it yields the complete
  semantic residual, input-blind factorization, and the four-label law without
  using SAT correctness.
* A trace carrying no information beyond the final decision makes every
  trace-derived residual decision-derived.  It therefore collapses exactly to
  the previous Boolean-output no-go.

This isolates the missing mathematical object: a nontrivial internal trace
discipline lying strictly between copied-input transcripts and final-answer
postprocessing.  Merely adding a trace field does not provide such a theorem.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameExecutionTraceProvenanceCalibration

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPObserverSwitchToy
open PallLean.Paper93.DeepMath.PathB.NFrameRedundantExpanderCodeEndpoint
open PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneDistanceBarrier
open PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneLocalityThreshold
open PallLean.Paper93.DeepMath.PathB.NFrameBooleanObservationBarrier
open PallLean.Paper93.DeepMath.PathB.NFrameTraceLengthThreshold
open PallLean.Paper93.DeepMath.PathB.NFrameInputBlindResidualTraceBarrier
open PallLean.Paper93.DeepMath.PathB.NFramePolynomialResidualTraceCompatibility
open PallLean.Paper93.DeepMath.PathB.NFrameDecisionDerivedResidualBarrier

/-! ## A certified execution-trace extension -/

/-- A trace surface extending an existing machine model.  Its observable
output is certified to agree with the model's original decision semantics. -/
structure DecisionTraceExtension (U : MachineModel) where
  Trace : Type
  traceRun : Nat -> CNF -> Trace
  decisionOfTrace : Trace -> Bool
  decisionOfTrace_traceRun :
    ∀ (code : Nat) (formula : CNF),
      decisionOfTrace (traceRun code formula) = U.decisionRun code formula

/-- The execution trace observed on a continuation-indexed formula family. -/
def solverExecutionTrace
    {U : MachineModel} (E : DecisionTraceExtension U)
    (D : DecisionMachine U) {m : Nat}
    (formulaOf : Assignment m -> CNF) : Assignment m -> E.Trace :=
  fun a => E.traceRun D.code (formulaOf a)

/-- A residual has trace provenance when it is obtained solely by
postprocessing the certified execution trace. -/
def ResidualDerivedFromExecutionTrace
    {U : MachineModel} (E : DecisionTraceExtension U)
    (D : DecisionMachine U) {m : Nat}
    (formulaOf : Assignment m -> CNF)
    {Residual : Type} (residual : Assignment m -> Residual) : Prop :=
  ∃ postprocess : E.Trace -> Residual,
    ∀ a, residual a = postprocess (solverExecutionTrace E D formulaOf a)

/-- The certified final decision is always trace-derived. -/
theorem solverDecision_traceDerived
    {U : MachineModel} (E : DecisionTraceExtension U)
    (D : DecisionMachine U) {m : Nat}
    (formulaOf : Assignment m -> CNF) :
    ResidualDerivedFromExecutionTrace E D formulaOf
      (fun a => U.decisionRun D.code (formulaOf a)) := by
  refine ⟨E.decisionOfTrace, ?_⟩
  intro a
  exact (E.decisionOfTrace_traceRun D.code (formulaOf a)).symm

/-! ## The input-retaining extreme -/

/-- A valid trace extension that simply retains the complete formula beside
the final solver answer. -/
def inputRetainingTraceExtension (U : MachineModel) :
    DecisionTraceExtension U where
  Trace := CNF × Bool
  traceRun := fun code formula => (formula, U.decisionRun code formula)
  decisionOfTrace := Prod.snd
  decisionOfTrace_traceRun := by
    intro _ _
    rfl

/-- If the continuation encoding has a left inverse, the full continuation
label is derived from the input-retaining trace by decoding its formula. -/
theorem fullLabelResidual_traceDerived_inputRetaining
    {U : MachineModel} (D : DecisionMachine U) {m : Nat}
    (formulaOf : Assignment m -> CNF)
    (recover : CNF -> Assignment m)
    (hrecover : Function.LeftInverse recover formulaOf) :
    ResidualDerivedFromExecutionTrace (inputRetainingTraceExtension U)
      D formulaOf (fullLabelTrace m) := by
  refine ⟨fun trace => recover trace.1, ?_⟩
  intro a
  exact (hrecover a).symm

/-- Merely adding a certified trace surface does not help: every solver and
every decodable continuation encoding admits an input-retaining trace carrying
the complete residual and satisfying the four-label law. -/
theorem exists_inputRetainingTrace_fullLabel_package
    {U : MachineModel} (D : DecisionMachine U) {m N : Nat}
    (formulaOf : Assignment m -> CNF)
    (recover : CNF -> Assignment m)
    (hrecover : Function.LeftInverse recover formulaOf)
    (C : RedundantContinuationCode m N) :
    ∃ E : DecisionTraceExtension U,
      ResidualDerivedFromExecutionTrace E D formulaOf (fullLabelTrace m) ∧
      CellMapFactorsThroughInputBlindResidual (fullLabelTrace m)
        (id : Assignment m -> Assignment m) ∧
      CellFourwiseRadiusCompatible C
        (id : Assignment m -> Assignment m) (R := 1) := by
  exact ⟨inputRetainingTraceExtension U,
    fullLabelResidual_traceDerived_inputRetaining D formulaOf recover hrecover,
    fullLabelCell_inputBlind_factorization m,
    fullLabelCell_fourwise C⟩

/-! ## The final-decision-only extreme -/

/-- A trace carries no information beyond the final solver decision when the
whole trace can itself be reconstructed from that Boolean result. -/
def TraceCarriesOnlyDecisionInformation
    {U : MachineModel} (E : DecisionTraceExtension U)
    (D : DecisionMachine U) {m : Nat}
    (formulaOf : Assignment m -> CNF) : Prop :=
  ∃ reconstruct : Bool -> E.Trace,
    ∀ a, solverExecutionTrace E D formulaOf a =
      reconstruct (U.decisionRun D.code (formulaOf a))

/-- Under the decision-only discipline, every trace-derived residual is
already decision-derived. -/
theorem traceDerived_of_decisionOnly_is_decisionDerived
    {U : MachineModel} (E : DecisionTraceExtension U)
    (D : DecisionMachine U) {m : Nat}
    (formulaOf : Assignment m -> CNF)
    {Residual : Type} (residual : Assignment m -> Residual)
    (htrace : ResidualDerivedFromExecutionTrace E D formulaOf residual)
    (honly : TraceCarriesOnlyDecisionInformation E D formulaOf) :
    ResidualDeterminedBySolverDecision D formulaOf residual := by
  obtain ⟨postprocess, hpost⟩ := htrace
  obtain ⟨reconstruct, hreconstruct⟩ := honly
  refine ⟨fun bit => postprocess (reconstruct bit), ?_⟩
  intro a
  calc
    residual a = postprocess (solverExecutionTrace E D formulaOf a) := hpost a
    _ = postprocess (reconstruct
        (U.decisionRun D.code (formulaOf a))) :=
      congrArg postprocess (hreconstruct a)

/-- A decodable input-retaining trace cannot carry only the final-decision
information on the two-bit continuation cube. -/
theorem inputRetainingTrace_not_decisionOnly_twoBits
    {U : MachineModel} (D : DecisionMachine U)
    (formulaOf : Assignment 2 -> CNF)
    (recover : CNF -> Assignment 2)
    (hrecover : Function.LeftInverse recover formulaOf) :
    ¬ TraceCarriesOnlyDecisionInformation
      (inputRetainingTraceExtension U) D formulaOf := by
  intro honly
  have hderived : ResidualDeterminedBySolverDecision D formulaOf
      (fullLabelTrace 2) :=
    traceDerived_of_decisionOnly_is_decisionDerived
      (inputRetainingTraceExtension U) D formulaOf (fullLabelTrace 2)
      (fullLabelResidual_traceDerived_inputRetaining
        D formulaOf recover hrecover) honly
  exact decisionDerived_not_inputBlind_fullLabel
    D formulaOf (fullLabelTrace 2) hderived
    (fullLabelCell_inputBlind_factorization 2)

/-- At the decision-only extreme, trace provenance cannot support the
distance-three four-label law. -/
theorem decisionOnlyTrace_not_fourwise_distanceThree
    {U : MachineModel} (E : DecisionTraceExtension U)
    (D : DecisionMachine U)
    (formulaOf : Assignment 2 -> CNF)
    {N : Nat} (C : RedundantContinuationCode 2 N)
    {Residual Cell : Type} [DecidableEq Cell]
    (residual : Assignment 2 -> Residual)
    (cellOf : Assignment 2 -> Cell)
    (htrace : ResidualDerivedFromExecutionTrace E D formulaOf residual)
    (honly : TraceCarriesOnlyDecisionInformation E D formulaOf)
    (hfactor : CellMapFactorsThroughInputBlindResidual residual cellOf)
    (hsep : MinimumDistanceAtLeastThree C) :
    ¬ CellFourwiseRadiusCompatible C cellOf (R := 1) := by
  have hderived := traceDerived_of_decisionOnly_is_decisionDerived
    E D formulaOf residual htrace honly
  exact decisionDerived_not_fourwise_distanceThree
    D formulaOf C residual cellOf hderived hfactor hsep

/-- Consequently, correctness forcing the four-label law at the
decision-only trace extreme is again equivalent to solver incorrectness. -/
theorem correctnessForces_decisionOnlyTrace_fourwise_iff_not_decidesSAT
    {U : MachineModel} (E : DecisionTraceExtension U)
    (D : DecisionMachine U)
    (formulaOf : Assignment 2 -> CNF)
    {N : Nat} (C : RedundantContinuationCode 2 N)
    {Residual Cell : Type} [DecidableEq Cell]
    (residual : Assignment 2 -> Residual)
    (cellOf : Assignment 2 -> Cell)
    (htrace : ResidualDerivedFromExecutionTrace E D formulaOf residual)
    (honly : TraceCarriesOnlyDecisionInformation E D formulaOf)
    (hfactor : CellMapFactorsThroughInputBlindResidual residual cellOf)
    (hsep : MinimumDistanceAtLeastThree C) :
    (DecidesSAT U D ->
      CellFourwiseRadiusCompatible C cellOf (R := 1)) ↔
      ¬ DecidesSAT U D := by
  have hnot := decisionOnlyTrace_not_fourwise_distanceThree
    E D formulaOf C residual cellOf htrace honly hfactor hsep
  constructor
  · intro hforce hD
    exact hnot (hforce hD)
  · intro hnotD hD
    exact (hnotD hD).elim

end PallLean.Paper93.DeepMath.PathB.NFrameExecutionTraceProvenanceCalibration

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameExecutionTraceProvenanceCalibration.solverDecision_traceDerived
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameExecutionTraceProvenanceCalibration.fullLabelResidual_traceDerived_inputRetaining
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameExecutionTraceProvenanceCalibration.exists_inputRetainingTrace_fullLabel_package
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameExecutionTraceProvenanceCalibration.traceDerived_of_decisionOnly_is_decisionDerived
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameExecutionTraceProvenanceCalibration.inputRetainingTrace_not_decisionOnly_twoBits
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameExecutionTraceProvenanceCalibration.decisionOnlyTrace_not_fourwise_distanceThree
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameExecutionTraceProvenanceCalibration.correctnessForces_decisionOnlyTrace_fourwise_iff_not_decidesSAT
