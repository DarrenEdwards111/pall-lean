import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameLinearCircuitResidualWitness

/-!
# Decision-derived residuals collapse to the Boolean-output barrier

The linear circuit witness shows that an unrestricted residual may preserve
the complete continuation label at linear cost.  The first genuinely
solver-relative restriction one can impose in the present machine interface
is that the residual be derived solely from the alleged solver's final
decision bit.

This file calibrates that restriction exactly.  Even if the residual alphabet
is arbitrarily large, postprocessing a Boolean answer adds no distinguishing
information.  Factorization through such a residual is equivalent to direct
factorization through the decision bit.  Consequently it cannot input-blindly
recover the two-bit continuation label, cannot support a separated four-label
law, and cannot contain the coordinate-projection residual.

Thus the restriction successfully excludes copied semantic input, but only by
returning to the previous one-bit bottleneck.  A useful next model must expose
an independently defined internal execution object; the current
`DecisionMachine` surface contains no such trace.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameDecisionDerivedResidualBarrier

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPObserverSwitchToy
open PallLean.Paper93.DeepMath.PathB.NFrameRedundantExpanderCodeEndpoint
open PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneDistanceBarrier
open PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneLocalityThreshold
open PallLean.Paper93.DeepMath.PathB.NFrameBooleanObservationBarrier
open PallLean.Paper93.DeepMath.PathB.NFrameInputBlindResidualTraceBarrier
open PallLean.Paper93.DeepMath.PathB.NFrameLinearCircuitResidualWitness

/-! ## Residuals determined solely by the final solver answer -/

/-- A residual is decision-derived when it is only a postprocessing of the
alleged solver's final Boolean answer. -/
def ResidualDeterminedBySolverDecision
    {U : MachineModel} (D : DecisionMachine U) {m : Nat}
    (formulaOf : Assignment m -> CNF)
    {Residual : Type} (residual : Assignment m -> Residual) : Prop :=
  ∃ postprocess : Bool -> Residual,
    ∀ a, residual a = postprocess (U.decisionRun D.code (formulaOf a))

/-- A cell map that factors through a decision-derived residual already
factors directly through the Boolean solver answer. -/
theorem decisionDerived_factorization_collapses
    {U : MachineModel} (D : DecisionMachine U) {m : Nat}
    (formulaOf : Assignment m -> CNF)
    {Residual Cell : Type}
    (residual : Assignment m -> Residual)
    (cellOf : Assignment m -> Cell)
    (hderived : ResidualDeterminedBySolverDecision D formulaOf residual)
    (hfactor : CellMapFactorsThrough residual cellOf) :
    CellMapFactorsThrough
      (fun a => U.decisionRun D.code (formulaOf a)) cellOf := by
  obtain ⟨postprocess, hpost⟩ := hderived
  obtain ⟨decode, hdecode⟩ := hfactor
  refine ⟨fun bit => decode (postprocess bit), ?_⟩
  intro a
  calc
    cellOf a = decode (residual a) := hdecode a
    _ = decode (postprocess (U.decisionRun D.code (formulaOf a))) :=
      congrArg decode (hpost a)

/-- Exact calibration: allowing an arbitrary intermediate residual derived
from the decision bit gives precisely the same factorizations as using the
decision bit directly. -/
theorem exists_decisionDerived_inputBlind_factorization_iff
    {U : MachineModel} (D : DecisionMachine U) {m : Nat}
    (formulaOf : Assignment m -> CNF)
    {Cell : Type} (cellOf : Assignment m -> Cell) :
    (∃ (Residual : Type) (residual : Assignment m -> Residual),
      ResidualDeterminedBySolverDecision D formulaOf residual ∧
      CellMapFactorsThroughInputBlindResidual residual cellOf) ↔
      CellMapFactorsThrough
        (fun a => U.decisionRun D.code (formulaOf a)) cellOf := by
  constructor
  · rintro ⟨Residual, residual, hderived, hblind⟩
    exact decisionDerived_factorization_collapses D formulaOf residual cellOf
      hderived
      ((inputBlindResidual_iff_residual_factorization residual cellOf).mp hblind)
  · intro hfactor
    let decision : Assignment m -> Bool :=
      fun a => U.decisionRun D.code (formulaOf a)
    refine ⟨Bool, decision, ?_, ?_⟩
    · exact ⟨id, fun _ => rfl⟩
    · exact (inputBlindResidual_iff_residual_factorization decision cellOf).mpr
        hfactor

/-! ## The coordinate-copy witness is genuinely excluded -/

/-- No decision-derived residual can input-blindly recover the complete
two-bit continuation label. -/
theorem decisionDerived_not_inputBlind_fullLabel
    {U : MachineModel} (D : DecisionMachine U)
    (formulaOf : Assignment 2 -> CNF)
    {Residual : Type} (residual : Assignment 2 -> Residual)
    (hderived : ResidualDeterminedBySolverDecision D formulaOf residual) :
    ¬ CellMapFactorsThroughInputBlindResidual residual
      (id : Assignment 2 -> Assignment 2) := by
  intro hblind
  have hfactor : CellMapFactorsThrough residual
      (id : Assignment 2 -> Assignment 2) :=
    (inputBlindResidual_iff_residual_factorization residual id).mp hblind
  have hdecision := decisionDerived_factorization_collapses
    D formulaOf residual id hderived hfactor
  exact solverDecisionBit_factored_cellMap_not_injective
    D formulaOf id hdecision Function.injective_id

/-- In particular, the explicit coordinate-projection circuit residual cannot
be obtained by postprocessing the alleged solver's final answer. -/
theorem coordinateResidual_not_decisionDerived_twoBits
    {U : MachineModel} (D : DecisionMachine U)
    (formulaOf : Assignment 2 -> CNF) :
    ¬ ResidualDeterminedBySolverDecision D formulaOf
      (evalResidualCircuitFamily (coordinateResidualCircuits 2)) := by
  intro hderived
  exact decisionDerived_not_inputBlind_fullLabel
    D formulaOf _ hderived (coordinateResidualCircuits_inputBlind 2)

/-! ## The separated four-label endpoint -/

/-- With minimum distance three, no cell map factored through a
decision-derived residual can satisfy the radius-one four-label law. -/
theorem decisionDerived_not_fourwise_distanceThree
    {U : MachineModel} (D : DecisionMachine U)
    (formulaOf : Assignment 2 -> CNF)
    {N : Nat} (C : RedundantContinuationCode 2 N)
    {Residual Cell : Type} [DecidableEq Cell]
    (residual : Assignment 2 -> Residual)
    (cellOf : Assignment 2 -> Cell)
    (hderived : ResidualDeterminedBySolverDecision D formulaOf residual)
    (hfactor : CellMapFactorsThroughInputBlindResidual residual cellOf)
    (hsep : MinimumDistanceAtLeastThree C) :
    ¬ CellFourwiseRadiusCompatible C cellOf (R := 1) := by
  have hresidual : CellMapFactorsThrough residual cellOf :=
    (inputBlindResidual_iff_residual_factorization residual cellOf).mp hfactor
  have hdecision := decisionDerived_factorization_collapses
    D formulaOf residual cellOf hderived hresidual
  exact factoredThroughBool_not_fourwise_distanceThree
    C (solverDecisionBit D formulaOf) cellOf hdecision hsep

/-- Asking SAT correctness to force the separated four-label law through a
fixed decision-derived residual is again exactly asking that the alleged
solver be incorrect. -/
theorem correctnessForces_decisionDerived_fourwise_iff_not_decidesSAT
    {U : MachineModel} (D : DecisionMachine U)
    (formulaOf : Assignment 2 -> CNF)
    {N : Nat} (C : RedundantContinuationCode 2 N)
    {Residual Cell : Type} [DecidableEq Cell]
    (residual : Assignment 2 -> Residual)
    (cellOf : Assignment 2 -> Cell)
    (hderived : ResidualDeterminedBySolverDecision D formulaOf residual)
    (hfactor : CellMapFactorsThroughInputBlindResidual residual cellOf)
    (hsep : MinimumDistanceAtLeastThree C) :
    (DecidesSAT U D ->
      CellFourwiseRadiusCompatible C cellOf (R := 1)) ↔
      ¬ DecidesSAT U D := by
  have hnot := decisionDerived_not_fourwise_distanceThree
    D formulaOf C residual cellOf hderived hfactor hsep
  constructor
  · intro hforce hD
    exact hnot (hforce hD)
  · intro hnotD hD
    exact (hnotD hD).elim

end PallLean.Paper93.DeepMath.PathB.NFrameDecisionDerivedResidualBarrier

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameDecisionDerivedResidualBarrier.decisionDerived_factorization_collapses
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameDecisionDerivedResidualBarrier.exists_decisionDerived_inputBlind_factorization_iff
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameDecisionDerivedResidualBarrier.decisionDerived_not_inputBlind_fullLabel
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameDecisionDerivedResidualBarrier.coordinateResidual_not_decisionDerived_twoBits
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameDecisionDerivedResidualBarrier.decisionDerived_not_fourwise_distanceThree
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameDecisionDerivedResidualBarrier.correctnessForces_decisionDerived_fourwise_iff_not_decidesSAT
