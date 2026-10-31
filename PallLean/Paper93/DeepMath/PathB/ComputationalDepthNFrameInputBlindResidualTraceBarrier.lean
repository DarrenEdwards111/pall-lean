import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameInputCarryingTraceBarrier

/-!
# Input-blind residual traces recover the full information threshold

An input-carrying execution transcript can preserve every continuation label
without learning anything: its cell decoder may simply read the copied input.
To discount that vacuous information, the natural exact condition is that the
decoder ignore the input component and use only a residual execution trace.

This file formalizes that condition and proves it is equivalent to ordinary
factorization through the residual trace alone.  Consequently, if a
distance-three code satisfies the radius-one four-label law, the residual
must itself distinguish all `2^m` continuation labels.  A `k`-bit residual
therefore still requires `m <= k`.

For a solver's Boolean final answer on the two-bit continuation cube, the
identity semantic cell factors through the unrestricted input-carrying trace
but cannot factor through any decoder that ignores the copied input.  Asking
SAT correctness to supply such an input-blind factorization is again exactly
asking the alleged solver to be incorrect.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameInputBlindResidualTraceBarrier

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPObserverSwitchToy
open PallLean.Paper93.DeepMath.PathB.NFrameRedundantExpanderCodeEndpoint
open PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneDistanceBarrier
open PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneLocalityThreshold
open PallLean.Paper93.DeepMath.PathB.NFrameSeparatedFourwiseInjectivityEndpoint
open PallLean.Paper93.DeepMath.PathB.NFrameBooleanObservationBarrier
open PallLean.Paper93.DeepMath.PathB.NFrameTraceLengthThreshold
open PallLean.Paper93.DeepMath.PathB.NFrameInputCarryingTraceBarrier

/-! ## Discounting the copied input -/

/-- A decoder on an input-residual pair is input-blind when its value depends
only on the residual component. -/
def DecoderIgnoresInput
    {m : Nat} {Residual Cell : Type}
    (decode : Assignment m × Residual -> Cell) : Prop :=
  ∃ residualDecode : Residual -> Cell,
    ∀ a r, decode (a, r) = residualDecode r

/-- The cell map factors through an input-carrying trace via a decoder that is
forbidden to use the copied input. -/
def CellMapFactorsThroughInputBlindResidual
    {m : Nat} {Residual Cell : Type}
    (residual : Assignment m -> Residual)
    (cellOf : Assignment m -> Cell) : Prop :=
  ∃ decode : Assignment m × Residual -> Cell,
    DecoderIgnoresInput decode ∧
    ∀ a, cellOf a = decode (a, residual a)

/-- Discounting copied input is exact: input-blind factorization through the
paired trace is equivalent to factorization through the residual alone. -/
theorem inputBlindResidual_iff_residual_factorization
    {m : Nat} {Residual Cell : Type}
    (residual : Assignment m -> Residual)
    (cellOf : Assignment m -> Cell) :
    CellMapFactorsThroughInputBlindResidual residual cellOf ↔
      CellMapFactorsThrough residual cellOf := by
  constructor
  · rintro ⟨decode, ⟨residualDecode, hignore⟩, hdecode⟩
    refine ⟨residualDecode, ?_⟩
    intro a
    calc
      cellOf a = decode (a, residual a) := hdecode a
      _ = residualDecode (residual a) := hignore a (residual a)
  · rintro ⟨residualDecode, hdecode⟩
    refine ⟨fun t => residualDecode t.2, ?_, ?_⟩
    · exact ⟨residualDecode, fun _ _ => rfl⟩
    · intro a
      exact hdecode a

/-! ## The residual must retain the full continuation label -/

/-- If an injective cell map admits an input-blind factorization, the residual
trace itself is injective. -/
theorem residual_injective_of_inputBlind_injective_cellMap
    {m : Nat} {Residual Cell : Type}
    (residual : Assignment m -> Residual)
    (cellOf : Assignment m -> Cell)
    (hfactor : CellMapFactorsThroughInputBlindResidual residual cellOf)
    (hcell : Function.Injective cellOf) :
    Function.Injective residual := by
  apply observation_injective_of_cellMap_injective residual cellOf
  · exact (inputBlindResidual_iff_residual_factorization residual cellOf).mp hfactor
  · exact hcell

/-- A finite input-blind residual alphabet needs at least `2^m` values. -/
theorem two_pow_le_residual_card_of_inputBlind_injective_cellMap
    {m : Nat} {Residual Cell : Type} [Fintype Residual]
    (residual : Assignment m -> Residual)
    (cellOf : Assignment m -> Cell)
    (hfactor : CellMapFactorsThroughInputBlindResidual residual cellOf)
    (hcell : Function.Injective cellOf) :
    2 ^ m <= Fintype.card Residual := by
  exact two_pow_le_observation_card_of_factored_injective_cellMap
    residual cellOf
    ((inputBlindResidual_iff_residual_factorization residual cellOf).mp hfactor)
    hcell

/-- In the bit-vector specialization, an input-blind `k`-bit residual must
have length at least `m`. -/
theorem residual_length_ge_of_inputBlind_injective_cellMap
    {m k : Nat} {Cell : Type}
    (residual : Assignment m -> Assignment k)
    (cellOf : Assignment m -> Cell)
    (hfactor : CellMapFactorsThroughInputBlindResidual residual cellOf)
    (hcell : Function.Injective cellOf) :
    m <= k := by
  exact trace_length_ge_of_factored_injective_cellMap residual cellOf
    ((inputBlindResidual_iff_residual_factorization residual cellOf).mp hfactor)
    hcell

/-- With a distance-three code, the four-label law transfers the same sharp
length lower bound to the input-blind residual. -/
theorem residual_length_ge_of_inputBlind_fourwise_distanceThree
    {m k N : Nat} {Cell : Type} [DecidableEq Cell]
    (C : RedundantContinuationCode m N)
    (residual : Assignment m -> Assignment k)
    (cellOf : Assignment m -> Cell)
    (hfactor : CellMapFactorsThroughInputBlindResidual residual cellOf)
    (hfour : CellFourwiseRadiusCompatible C cellOf (R := 1))
    (hsep : MinimumDistanceAtLeastThree C) :
    m <= k := by
  have hcell :=
    (fourwise_iff_cellOf_injective_of_distanceThree C cellOf hsep).mp hfour
  exact residual_length_ge_of_inputBlind_injective_cellMap
    residual cellOf hfactor hcell

/-- Therefore a residual shorter than the continuation label cannot both
factor input-blindly and support the separated four-label law. -/
theorem shortResidual_not_inputBlind_and_fourwise_distanceThree
    {m k N : Nat} {Cell : Type} [DecidableEq Cell]
    (C : RedundantContinuationCode m N)
    (residual : Assignment m -> Assignment k)
    (cellOf : Assignment m -> Cell)
    (hshort : k < m)
    (hsep : MinimumDistanceAtLeastThree C) :
    ¬ (CellMapFactorsThroughInputBlindResidual residual cellOf ∧
      CellFourwiseRadiusCompatible C cellOf (R := 1)) := by
  rintro ⟨hfactor, hfour⟩
  have hmk := residual_length_ge_of_inputBlind_fourwise_distanceThree
    C residual cellOf hfactor hfour hsep
  omega

/-! ## Exact solver-decision separation -/

/-- The identity semantic cell does not factor input-blindly through a Boolean
solver decision on the two-bit continuation cube. -/
theorem decisionBit_not_inputBlind_fullLabel_factorization
    {U : MachineModel} (D : DecisionMachine U)
    (formulaOf : Assignment 2 -> CNF) :
    ¬ CellMapFactorsThroughInputBlindResidual
      (solverDecisionBit D formulaOf)
      (id : Assignment 2 -> Assignment 2) := by
  intro hfactor
  have hres : Function.Injective (solverDecisionBit D formulaOf) :=
    residual_injective_of_inputBlind_injective_cellMap
      (solverDecisionBit D formulaOf) id hfactor Function.injective_id
  exact no_injective_boolean_observation
    (solverDecisionBit D formulaOf) hres

/-- The exact contrast: the identity cell factors through the full
input-carrying solver trace, but not through an input-blind decoder of that
same trace's Boolean residual. -/
theorem unrestricted_vs_inputBlind_decisionTrace
    {U : MachineModel} (D : DecisionMachine U)
    (formulaOf : Assignment 2 -> CNF) :
    CellMapFactorsThrough (inputDecisionTrace D formulaOf)
      (id : Assignment 2 -> Assignment 2) ∧
    ¬ CellMapFactorsThroughInputBlindResidual
      (solverDecisionBit D formulaOf)
      (id : Assignment 2 -> Assignment 2) := by
  exact ⟨fullLabelCell_factorsThrough_inputDecisionTrace D formulaOf,
    decisionBit_not_inputBlind_fullLabel_factorization D formulaOf⟩

/-- Asking correctness to turn the solver's one-bit residual into an
input-blind full-label factorization is exactly asking that solver not to
decide SAT. -/
theorem correctnessForces_inputBlind_decisionFactorization_iff_not_decidesSAT
    {U : MachineModel} (D : DecisionMachine U)
    (formulaOf : Assignment 2 -> CNF) :
    (DecidesSAT U D ->
      CellMapFactorsThroughInputBlindResidual
        (solverDecisionBit D formulaOf)
        (id : Assignment 2 -> Assignment 2)) ↔
      ¬ DecidesSAT U D := by
  have hnot := decisionBit_not_inputBlind_fullLabel_factorization D formulaOf
  constructor
  · intro hforce hD
    exact hnot (hforce hD)
  · intro hnotD hD
    exact (hnotD hD).elim

end PallLean.Paper93.DeepMath.PathB.NFrameInputBlindResidualTraceBarrier

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameInputBlindResidualTraceBarrier.inputBlindResidual_iff_residual_factorization
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameInputBlindResidualTraceBarrier.residual_injective_of_inputBlind_injective_cellMap
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameInputBlindResidualTraceBarrier.two_pow_le_residual_card_of_inputBlind_injective_cellMap
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameInputBlindResidualTraceBarrier.residual_length_ge_of_inputBlind_fourwise_distanceThree
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameInputBlindResidualTraceBarrier.shortResidual_not_inputBlind_and_fourwise_distanceThree
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameInputBlindResidualTraceBarrier.unrestricted_vs_inputBlind_decisionTrace
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameInputBlindResidualTraceBarrier.correctnessForces_inputBlind_decisionFactorization_iff_not_decidesSAT
