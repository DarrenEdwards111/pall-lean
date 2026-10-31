import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameCorrectnessInjectivityNoGo

/-!
# A final Boolean answer cannot carry the continuation cell

The previous endpoint shows that, for a distance-three code, the radius-one
four-label law is exactly injectivity of the continuation-to-cell map.  One
natural attempt to make that map genuinely solver-correlated is to derive it
from the solver's final accept/reject bit.

This file proves the resulting information barrier.  If a cell map factors
through an observation alphabet, injectivity of the cell map forces the
observation itself to be injective, hence the alphabet must contain at least
`2^m` values.  A Boolean final answer has only two values, so it already fails
on the two-bit continuation cube.  The obstruction remains when the Boolean
observation is literally the alleged machine's decision output on a family of
CNFs.

Consequently, with a distance-three code, a correctness-to-fourwise bridge for
such a decision-bit-factored cell map is again equivalent to the alleged
solver not deciding SAT.  A useful solver-to-cell correspondence must expose a
richer execution object, not merely the final answer.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBooleanObservationBarrier

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPObserverSwitchToy
open PallLean.Paper93.DeepMath.PathB.NFrameRedundantExpanderCodeEndpoint
open PallLean.Paper93.DeepMath.PathB.NFrameReceivedWordRadiusBarrier
open PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneDistanceBarrier
open PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneLocalityThreshold
open PallLean.Paper93.DeepMath.PathB.NFrameSeparatedFourwiseInjectivityEndpoint

/-! ## Observation factorization -/

/-- The continuation-to-cell map uses no information beyond `observe`. -/
def CellMapFactorsThrough
    {m : Nat} {Obs Cell : Type}
    (observe : Assignment m -> Obs)
    (cellOf : Assignment m -> Cell) : Prop :=
  ∃ decode : Obs -> Cell, ∀ a, cellOf a = decode (observe a)

/-- If an injective cell map factors through an observation, then the
observation must already distinguish every continuation label. -/
theorem observation_injective_of_cellMap_injective
    {m : Nat} {Obs Cell : Type}
    (observe : Assignment m -> Obs)
    (cellOf : Assignment m -> Cell)
    (hfactor : CellMapFactorsThrough observe cellOf)
    (hcell : Function.Injective cellOf) :
    Function.Injective observe := by
  obtain ⟨decode, hdecode⟩ := hfactor
  intro a b hab
  apply hcell
  rw [hdecode a, hdecode b, hab]

/-- Therefore any finite observation alphabet supporting an injective factored
cell map has at least `2^m` values. -/
theorem two_pow_le_observation_card_of_factored_injective_cellMap
    {m : Nat} {Obs Cell : Type} [Fintype Obs]
    (observe : Assignment m -> Obs)
    (cellOf : Assignment m -> Cell)
    (hfactor : CellMapFactorsThrough observe cellOf)
    (hcell : Function.Injective cellOf) :
    2 ^ m <= Fintype.card Obs := by
  have hinj := observation_injective_of_cellMap_injective
    observe cellOf hfactor hcell
  have hcard := Fintype.card_le_of_injective observe hinj
  simpa using hcard

/-! ## The Boolean bottleneck -/

/-- No Boolean observation can injectively encode the two-bit continuation
cube. -/
theorem no_injective_boolean_observation
    (observe : Assignment 2 -> Bool) :
    ¬ Function.Injective observe := by
  intro hinj
  have hcard := Fintype.card_le_of_injective observe hinj
  norm_num at hcard

/-- Hence no cell map derived solely from a Boolean observation can be
injective on the two-bit continuation cube. -/
theorem factoredThroughBool_cellMap_not_injective
    {Cell : Type}
    (observe : Assignment 2 -> Bool)
    (cellOf : Assignment 2 -> Cell)
    (hfactor : CellMapFactorsThrough observe cellOf) :
    ¬ Function.Injective cellOf := by
  intro hcell
  exact no_injective_boolean_observation observe
    (observation_injective_of_cellMap_injective
      observe cellOf hfactor hcell)

/-- Under distance three, a Boolean-factored cell map cannot satisfy the
radius-one four-label law. -/
theorem factoredThroughBool_not_fourwise_distanceThree
    {N : Nat} {Cell : Type} [DecidableEq Cell]
    (C : RedundantContinuationCode 2 N)
    (observe : Assignment 2 -> Bool)
    (cellOf : Assignment 2 -> Cell)
    (hfactor : CellMapFactorsThrough observe cellOf)
    (hsep : MinimumDistanceAtLeastThree C) :
    ¬ CellFourwiseRadiusCompatible C cellOf (R := 1) := by
  intro hfour
  have hcell :=
    (fourwise_iff_cellOf_injective_of_distanceThree C cellOf hsep).mp hfour
  exact factoredThroughBool_cellMap_not_injective observe cellOf hfactor hcell

/-! ## Literal solver-output specialization -/

/-- The final decision bit of an alleged machine on a continuation-indexed
family of formulas. -/
def solverDecisionBit
    {U : MachineModel} (D : DecisionMachine U)
    (formulaOf : Assignment 2 -> CNF) : Assignment 2 -> Bool :=
  fun a => U.decisionRun D.code (formulaOf a)

/-- A cell map factored through the solver's literal final decision bit is not
injective, independently of whether that decision is correct. -/
theorem solverDecisionBit_factored_cellMap_not_injective
    {U : MachineModel} (D : DecisionMachine U)
    (formulaOf : Assignment 2 -> CNF)
    {Cell : Type} (cellOf : Assignment 2 -> Cell)
    (hfactor : CellMapFactorsThrough
      (solverDecisionBit D formulaOf) cellOf) :
    ¬ Function.Injective cellOf :=
  factoredThroughBool_cellMap_not_injective
    (solverDecisionBit D formulaOf) cellOf hfactor

/-- For a distance-three code, saying solver correctness forces the four-label
law for a decision-bit-factored cell map is exactly saying that this alleged
solver is not SAT-correct. -/
theorem correctnessForces_decisionBitFactored_fourwise_iff_not_decidesSAT
    {U : MachineModel} (D : DecisionMachine U)
    (formulaOf : Assignment 2 -> CNF)
    {N : Nat} (C : RedundantContinuationCode 2 N)
    {Cell : Type} [DecidableEq Cell]
    (cellOf : Assignment 2 -> Cell)
    (hfactor : CellMapFactorsThrough
      (solverDecisionBit D formulaOf) cellOf)
    (hsep : MinimumDistanceAtLeastThree C) :
    (DecidesSAT U D ->
      CellFourwiseRadiusCompatible C cellOf (R := 1)) ↔
      ¬ DecidesSAT U D := by
  have hnotfour : ¬ CellFourwiseRadiusCompatible C cellOf (R := 1) :=
    factoredThroughBool_not_fourwise_distanceThree
      C (solverDecisionBit D formulaOf) cellOf hfactor hsep
  constructor
  · intro hforce hD
    exact hnotfour (hforce hD)
  · intro hnotD hD
    exact (hnotD hD).elim

end PallLean.Paper93.DeepMath.PathB.NFrameBooleanObservationBarrier

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBooleanObservationBarrier.observation_injective_of_cellMap_injective
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBooleanObservationBarrier.two_pow_le_observation_card_of_factored_injective_cellMap
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBooleanObservationBarrier.no_injective_boolean_observation
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBooleanObservationBarrier.factoredThroughBool_not_fourwise_distanceThree
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBooleanObservationBarrier.solverDecisionBit_factored_cellMap_not_injective
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBooleanObservationBarrier.correctnessForces_decisionBitFactored_fourwise_iff_not_decidesSAT
