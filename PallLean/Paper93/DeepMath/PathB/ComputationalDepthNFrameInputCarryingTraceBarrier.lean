import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameTraceLengthThreshold

/-!
# Input-carrying traces do not yield a solver lower bound

The exact trace-length threshold says that a factored, separated continuation
cell needs at least `m` bits of trace information.  A literal execution
transcript, however, normally contains or can retain its input.  It therefore
meets this threshold for free, independently of the solver's decision logic.

This file makes that limitation explicit.  We pair the complete continuation
label with the solver's final Boolean answer.  The resulting observation is
injective for every alleged solver and every continuation-indexed formula
family.  Every continuation-to-cell map factors through it, and the identity
cell map satisfies the radius-one four-label law for every code, with no SAT
correctness hypothesis.

Projecting away the copied input recovers the previous Boolean observation and
its two-bit noninjectivity obstruction.  Thus the useful quantity cannot be
raw transcript length.  It must be continuation-distinguishing information
created by solver execution after discounting information merely copied from
the input; obtaining a lower bound on that quantity is a new semantic theorem.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameInputCarryingTraceBarrier

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPObserverSwitchToy
open PallLean.Paper93.DeepMath.PathB.NFrameRedundantExpanderCodeEndpoint
open PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneLocalityThreshold
open PallLean.Paper93.DeepMath.PathB.NFrameSeparatedFourwiseInjectivityEndpoint
open PallLean.Paper93.DeepMath.PathB.NFrameBooleanObservationBarrier
open PallLean.Paper93.DeepMath.PathB.NFrameTraceLengthThreshold

/-! ## A solver-correlated trace that retains its input -/

/-- The complete continuation label paired with the alleged solver's final
decision bit.  This is genuinely solver-correlated, but its injectivity comes
entirely from retaining the input label. -/
def inputDecisionTrace
    {U : MachineModel} (D : DecisionMachine U) {m : Nat}
    (formulaOf : Assignment m -> CNF) : Assignment m -> Assignment m × Bool :=
  fun a => (a, U.decisionRun D.code (formulaOf a))

/-- The input-carrying trace is injective for every solver, whether correct or
incorrect. -/
theorem inputDecisionTrace_injective
    {U : MachineModel} (D : DecisionMachine U) {m : Nat}
    (formulaOf : Assignment m -> CNF) :
    Function.Injective (inputDecisionTrace D formulaOf) := by
  intro a b hab
  exact congrArg Prod.fst hab

/-- Every continuation-to-cell map factors through the input-carrying trace:
the decoder simply reads the retained input and ignores the decision bit. -/
theorem every_cellMap_factorsThrough_inputDecisionTrace
    {U : MachineModel} (D : DecisionMachine U) {m : Nat}
    (formulaOf : Assignment m -> CNF)
    {Cell : Type} (cellOf : Assignment m -> Cell) :
    CellMapFactorsThrough (inputDecisionTrace D formulaOf) cellOf := by
  refine ⟨fun t => cellOf t.1, ?_⟩
  intro a
  rfl

/-- In particular, the full semantic cell factors through a trace that is
literally correlated with the solver's execution. -/
theorem fullLabelCell_factorsThrough_inputDecisionTrace
    {U : MachineModel} (D : DecisionMachine U) {m : Nat}
    (formulaOf : Assignment m -> CNF) :
    CellMapFactorsThrough (inputDecisionTrace D formulaOf)
      (id : Assignment m -> Assignment m) :=
  every_cellMap_factorsThrough_inputDecisionTrace D formulaOf id

/-! ## The separated four-label law is automatic -/

/-- Because the identity cell is injective, it satisfies fourwise radius-one
compatibility for every code.  Neither the solver output nor SAT correctness
is used. -/
theorem inputDecisionTrace_fullLabelCell_fourwise
    {U : MachineModel} (_D : DecisionMachine U) {m N : Nat}
    (_formulaOf : Assignment m -> CNF)
    (C : RedundantContinuationCode m N) :
    CellFourwiseRadiusCompatible C
      (id : Assignment m -> Assignment m) (R := 1) := by
  exact fourwise_of_cellOf_injective C id Function.injective_id

/-- Consequently, the statement that SAT correctness forces the four-label
law for this solver-correlated trace is true for every alleged solver. -/
theorem correctnessForces_inputDecisionTrace_fourwise
    {U : MachineModel} (D : DecisionMachine U) {m N : Nat}
    (formulaOf : Assignment m -> CNF)
    (C : RedundantContinuationCode m N) :
    DecidesSAT U D ->
      CellFourwiseRadiusCompatible C
        (id : Assignment m -> Assignment m) (R := 1) := by
  intro _
  exact inputDecisionTrace_fullLabelCell_fourwise D formulaOf C

/-- The complete limitation in one package: for every alleged solver there is
a solver-correlated injective trace through which the identity cell factors
and for which the four-label law holds, without assuming solver correctness. -/
theorem exists_inputCarryingTrace_package
    {U : MachineModel} (D : DecisionMachine U) {m N : Nat}
    (formulaOf : Assignment m -> CNF)
    (C : RedundantContinuationCode m N) :
    ∃ trace : Assignment m -> Assignment m × Bool,
      Function.Injective trace ∧
      CellMapFactorsThrough trace (id : Assignment m -> Assignment m) ∧
      CellFourwiseRadiusCompatible C
        (id : Assignment m -> Assignment m) (R := 1) := by
  refine ⟨inputDecisionTrace D formulaOf,
    inputDecisionTrace_injective D formulaOf,
    fullLabelCell_factorsThrough_inputDecisionTrace D formulaOf, ?_⟩
  exact inputDecisionTrace_fullLabelCell_fourwise D formulaOf C

/-! ## Erasing the copied input recovers the Boolean bottleneck -/

/-- The decision-only projection of the input-carrying trace is exactly the
literal solver decision bit. -/
theorem inputDecisionTrace_snd
    {U : MachineModel} (D : DecisionMachine U) {m : Nat}
    (formulaOf : Assignment m -> CNF) (a : Assignment m) :
    (inputDecisionTrace D formulaOf a).2 =
      U.decisionRun D.code (formulaOf a) := rfl

/-- On the two-bit continuation cube, erasing the copied input destroys
injectivity.  The extra distinguishability of the full trace is therefore not
supplied by the solver's Boolean answer. -/
theorem decisionProjection_not_injective_twoBits
    {U : MachineModel} (D : DecisionMachine U)
    (formulaOf : Assignment 2 -> CNF) :
    ¬ Function.Injective
      (fun a => (inputDecisionTrace D formulaOf a).2) := by
  simpa [inputDecisionTrace] using
    (no_injective_boolean_observation
      (solverDecisionBit D formulaOf))

end PallLean.Paper93.DeepMath.PathB.NFrameInputCarryingTraceBarrier

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameInputCarryingTraceBarrier.inputDecisionTrace_injective
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameInputCarryingTraceBarrier.every_cellMap_factorsThrough_inputDecisionTrace
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameInputCarryingTraceBarrier.inputDecisionTrace_fullLabelCell_fourwise
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameInputCarryingTraceBarrier.correctnessForces_inputDecisionTrace_fourwise
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameInputCarryingTraceBarrier.exists_inputCarryingTrace_package
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameInputCarryingTraceBarrier.decisionProjection_not_injective_twoBits
