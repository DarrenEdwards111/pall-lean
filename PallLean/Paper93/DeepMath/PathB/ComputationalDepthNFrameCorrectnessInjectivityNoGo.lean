import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSeparatedFourwiseInjectivityEndpoint

/-!
# Correctness-to-injectivity is already the SAT lower bound

The separated-code endpoint reduces the radius-one four-label law to
injectivity of the solver-cell map.  This file calibrates the remaining logical
content on the smallest nontrivial continuation cube.

Map both one-bit continuation labels to the unique element of `Unit`.  This
cell map is visibly noninjective.  For any alleged SAT decider, the statement
that correctness forces this map to be injective is therefore equivalent to
the statement that the machine does not decide SAT.  With any distance-three
code, the same is true of the four-label radius-one law.  Quantifying over all
polynomial machines makes the proposed semantic bridge exactly `SAT ∉ P`.

Thus correctness alone cannot manufacture the missing cell correspondence:
for an unconstrained cell map, adding that implication simply restates the
desired lower bound.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameCorrectnessInjectivityNoGo

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPObserverSwitchToy
open PallLean.Paper93.DeepMath.PathB.NFrameRedundantExpanderCodeEndpoint
open PallLean.Paper93.DeepMath.PathB.NFrameReceivedWordRadiusBarrier
open PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneDistanceBarrier
open PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneLocalityThreshold
open PallLean.Paper93.DeepMath.PathB.NFrameSeparatedFourwiseInjectivityEndpoint

/-! ## The smallest collapsed continuation cell -/

/-- The false one-bit continuation label. -/
def falseMessage : Assignment 1 := fun _ => false

/-- The true one-bit continuation label. -/
def trueMessage : Assignment 1 := fun _ => true

/-- The two one-bit continuation labels are distinct. -/
theorem falseMessage_ne_trueMessage : falseMessage ≠ trueMessage := by
  intro h
  have h0 := congrFun h (0 : Fin 1)
  simp [falseMessage, trueMessage] at h0

/-- A cell decomposition that forgets the continuation label completely. -/
def constantCell (_ : Assignment 1) : Unit := ()

/-- The constant one-cell decomposition is not injective. -/
theorem constantCell_not_injective : ¬ Function.Injective constantCell := by
  intro hinj
  exact falseMessage_ne_trueMessage (hinj rfl)

/-! ## Exact logical calibration for one alleged solver -/

/-- For a noninjective cell map, saying that SAT correctness forces cell
injectivity is exactly saying that the alleged machine is not SAT-correct. -/
theorem correctnessForcesInjectivity_iff_not_decidesSAT_of_not_injective
    {U : MachineModel} {D : DecisionMachine U}
    {m : Nat} {Cell : Type} (cellOf : Assignment m -> Cell)
    (hnot : ¬ Function.Injective cellOf) :
    (DecidesSAT U D -> Function.Injective cellOf) ↔ ¬ DecidesSAT U D := by
  constructor
  · intro hforce hD
    exact hnot (hforce hD)
  · intro hnotD hD
    exact (hnotD hD).elim

/-- On the collapsed one-bit cell, the correctness-to-injectivity bridge is
literally the negation of correctness of the alleged solver. -/
theorem correctnessForces_constantCell_injective_iff_not_decidesSAT
    {U : MachineModel} {D : DecisionMachine U} :
    (DecidesSAT U D -> Function.Injective constantCell) ↔
      ¬ DecidesSAT U D :=
  correctnessForcesInjectivity_iff_not_decidesSAT_of_not_injective
    constantCell constantCell_not_injective

/-- For every distance-three encoding of the one-bit cube, the corresponding
four-label semantic law on the collapsed cell is likewise exactly the claim
that the alleged solver is incorrect. -/
theorem correctnessForces_constantCell_fourwise_iff_not_decidesSAT
    {U : MachineModel} {D : DecisionMachine U} {N : Nat}
    (C : RedundantContinuationCode 1 N)
    (hsep : MinimumDistanceAtLeastThree C) :
    (DecidesSAT U D ->
      CellFourwiseRadiusCompatible C constantCell (R := 1)) ↔
      ¬ DecidesSAT U D := by
  rw [decides_fourwise_iff_decides_cellInjective C constantCell hsep]
  exact correctnessForces_constantCell_injective_iff_not_decidesSAT

/-! ## Universal calibration -/

/-- Requiring the injectivity bridge for every alleged polynomial SAT solver,
even just for the constant one-bit cell map, is exactly `SAT ∉ P`. -/
theorem allMachines_constantCell_injective_iff_not_SATDecisionInP
    (U : MachineModel) :
    (∀ D : DecisionMachine U,
      DecidesSAT U D -> Function.Injective constantCell) ↔
      ¬ SATDecisionInP U := by
  constructor
  · intro hforce hP
    obtain ⟨D, hD⟩ := hP
    exact constantCell_not_injective (hforce D hD)
  · intro hnotP D hD
    exact (hnotP ⟨D, hD⟩).elim

/-- With any fixed distance-three code, requiring the four-label bridge for
every alleged polynomial SAT solver is also exactly `SAT ∉ P`. -/
theorem allMachines_constantCell_fourwise_iff_not_SATDecisionInP
    (U : MachineModel) {N : Nat}
    (C : RedundantContinuationCode 1 N)
    (hsep : MinimumDistanceAtLeastThree C) :
    (∀ D : DecisionMachine U, DecidesSAT U D ->
      CellFourwiseRadiusCompatible C constantCell (R := 1)) ↔
      ¬ SATDecisionInP U := by
  constructor
  · intro hforce hP
    obtain ⟨D, hD⟩ := hP
    have hfour := hforce D hD
    have hinj :=
      (fourwise_iff_cellOf_injective_of_distanceThree
        C constantCell hsep).mp hfour
    exact constantCell_not_injective hinj
  · intro hnotP D hD
    exact (hnotP ⟨D, hD⟩).elim

end PallLean.Paper93.DeepMath.PathB.NFrameCorrectnessInjectivityNoGo

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameCorrectnessInjectivityNoGo.falseMessage_ne_trueMessage
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameCorrectnessInjectivityNoGo.constantCell_not_injective
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameCorrectnessInjectivityNoGo.correctnessForcesInjectivity_iff_not_decidesSAT_of_not_injective
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameCorrectnessInjectivityNoGo.correctnessForces_constantCell_fourwise_iff_not_decidesSAT
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameCorrectnessInjectivityNoGo.allMachines_constantCell_injective_iff_not_SATDecisionInP
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameCorrectnessInjectivityNoGo.allMachines_constantCell_fourwise_iff_not_SATDecisionInP
