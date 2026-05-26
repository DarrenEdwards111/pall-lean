import PallLean.Paper93.DeepMath.PathB.ComputationalDepthGodMoveUpperBoundNoGo

/-
# God-Move mass with a separate solver-capacity invariant

`ComputationalDepthGodMoveUpperBoundNoGo` shows that the concrete semantic
God-Move mass cannot itself be polynomially upper-bounded: a correct SAT search
machine transports every certified satisfiable challenge, so super-polynomial
frame mass becomes super-polynomial transported mass.

This file records the viable replacement.  The P-side upper bound must be on a
separate live resource/compression/capacity profile, not on transported mass
itself.  The remaining hard theorem is then an amplification statement:

  transported semantic mass <= solver capacity.

Together with a polynomial capacity upper bound and a super-polynomial
God-Move frame, this still closes the canonical SAT route.  The file does not
prove the amplification theorem for a concrete N-frame capacity; it isolates it
as the non-circular target that would have to be supplied by the geometry.
-/

namespace SATDepthMachine

/-! ## A separate solver-capacity profile -/

/-- A capacity model for a concrete God-Move frame.

`solverCapacity M n` is intended to be a live/compressed N-frame resource used
by `M` on layer `n`: observation budget, live context, compressed boundary
description, or another genuine capacity.  It is deliberately separate from
`GodMoveFrame.transportedMass F M n`. -/
structure GodMoveSolverCapacity
    (C : CanonicalMachineSurface)
    (F : GodMoveFrame) where
  solverCapacity : SearchMachine C.toMachineModel -> Nat -> Nat

/-- P-side capacity calibration: every correct canonical polynomial SAT search
machine has polynomially bounded solver capacity. -/
def GodMovePolynomialSolverCapacityUpperBound
    {C : CanonicalMachineSurface}
    {F : GodMoveFrame}
    (K : GodMoveSolverCapacity C F) : Prop :=
  ∀ M : SearchMachine C.toMachineModel,
    SearchCorrect C.toMachineModel M ->
      PolynomialTransportCapacity (K.solverCapacity M)

/-- The load-bearing capacity theorem: transporting semantic God-Move mass
forces at least that much live capacity.

This is the theorem the N-frame/God-Move geometry would need to prove.  It is
not the already-refuted direct upper bound on transported mass. -/
def GodMoveTransportedMassConsumesCapacity
    {C : CanonicalMachineSurface}
    {F : GodMoveFrame}
    (K : GodMoveSolverCapacity C F) : Prop :=
  ∀ M : SearchMachine C.toMachineModel,
    SearchCorrect C.toMachineModel M ->
      ∀ n : Nat,
        GodMoveFrame.transportedMass F M n <= K.solverCapacity M n

/-! ## The amplification contradiction -/

/-- If a frame has super-polynomial mass and a correct searcher must pay
capacity for transported mass, then that searcher's capacity is itself
super-polynomial. -/
theorem godMove_solverCapacity_superPolynomial_of_searchCorrect
    {C : CanonicalMachineSurface}
    (F : GodMoveFrame)
    (K : GodMoveSolverCapacity C F)
    (hlower : GodMoveFamilyMassLowerBound F)
    (hconsume : GodMoveTransportedMassConsumesCapacity K)
    (M : SearchMachine C.toMachineModel)
    (hM : SearchCorrect C.toMachineModel M) :
    SuperPolynomialMass (K.solverCapacity M) := by
  intro B hBpoly
  rcases godMove_transportedMass_superPolynomial_of_searchCorrect
      F hlower M hM B hBpoly with ⟨n, htransport_gt_B⟩
  exact ⟨n, Nat.lt_of_lt_of_le htransport_gt_B (hconsume M hM n)⟩

/-- Therefore a correct searcher cannot have polynomial capacity when both the
frame lower bound and the mass-to-capacity theorem hold. -/
theorem not_polynomialSolverCapacity_of_godMoveLowerBound_and_consumption
    {C : CanonicalMachineSurface}
    (F : GodMoveFrame)
    (K : GodMoveSolverCapacity C F)
    (hlower : GodMoveFamilyMassLowerBound F)
    (hconsume : GodMoveTransportedMassConsumesCapacity K)
    (M : SearchMachine C.toMachineModel)
    (hM : SearchCorrect C.toMachineModel M) :
    ¬ PolynomialTransportCapacity (K.solverCapacity M) := by
  intro hcap
  rcases hcap with ⟨B, hBpoly, hcapacity_le_B⟩
  rcases godMove_solverCapacity_superPolynomial_of_searchCorrect
      F K hlower hconsume M hM B hBpoly with ⟨n, hcapacity_gt_B⟩
  exact (Nat.not_lt_of_ge (hcapacity_le_B n)) hcapacity_gt_B

/-- P-side polynomial capacity plus mass-consumption and a super-polynomial
God-Move frame rules out shallow SAT search. -/
theorem deepSATSearch_of_godMoveSeparateCapacity
    (C : CanonicalMachineSurface)
    (F : GodMoveFrame)
    (K : GodMoveSolverCapacity C F)
    (hlower : GodMoveFamilyMassLowerBound F)
    (hupper : GodMovePolynomialSolverCapacityUpperBound K)
    (hconsume : GodMoveTransportedMassConsumesCapacity K) :
    DeepSATSearch C.toMachineModel := by
  intro hshallow
  rcases hshallow with ⟨M, hM⟩
  exact not_polynomialSolverCapacity_of_godMoveLowerBound_and_consumption
    F K hlower hconsume M hM (hupper M hM)

/-- Concrete package for the viable God-Move route.

Unlike `ConcreteGodMoveGravityObstruction`, the P-side bound is not placed on
`transportedMass`; it is placed on a separate solver-capacity profile.  The hard
SAT-side geometry is the `consumesCapacity` field. -/
structure GodMoveSeparateCapacityObstruction
    (C : CanonicalMachineSurface) where
  frame : GodMoveFrame
  capacity : GodMoveSolverCapacity C frame
  lowerBound : GodMoveFamilyMassLowerBound frame
  pSideCapacity : GodMovePolynomialSolverCapacityUpperBound capacity
  consumesCapacity : GodMoveTransportedMassConsumesCapacity capacity

/-- Main closure from the separated-capacity route. -/
theorem noCanonicalSATDecisionInP_of_godMoveSeparateCapacityObstruction
    (C : CanonicalMachineSurface)
    (H : GodMoveSeparateCapacityObstruction C) :
    ¬ CanonicalSATDecisionInP C :=
  canonicalNoDecider_of_deepSATSearch C
    (deepSATSearch_of_godMoveSeparateCapacity
      C H.frame H.capacity H.lowerBound H.pSideCapacity H.consumesCapacity)

/-- Described-surface version: the separated-capacity obstruction also feeds the
existing K^t/metacomplexity route closure. -/
theorem ktRoute_finalClosure_of_godMoveSeparateCapacityObstruction
    (D : DescribedCanonicalSurface)
    (H : GodMoveSeparateCapacityObstruction D.surface) :
    (¬ CanonicalSATDecisionInP D.surface) ∧
      NoPolynomialLengthScheduledCompleteGenerators D :=
  ktRoute_finalClosure D
    (hardMetacomplexitySocket_of_noCanonicalSATDecisionInP D
      (noCanonicalSATDecisionInP_of_godMoveSeparateCapacityObstruction
        D.surface H))

/-! ## Guard: the separated route is not the direct transported-mass upper bound -/

/-- The separated route uses capacity as a lower recipient of transported mass.
This theorem is the exact load-bearing inequality: once a correct searcher
exists, the no-go theorem pushes super-polynomial transported mass into
super-polynomial capacity. -/
theorem godMove_separateCapacity_exposes_remaining_gap
    {C : CanonicalMachineSurface}
    (F : GodMoveFrame)
    (K : GodMoveSolverCapacity C F)
    (hlower : GodMoveFamilyMassLowerBound F)
    (hconsume : GodMoveTransportedMassConsumesCapacity K)
    (M : SearchMachine C.toMachineModel)
    (hM : SearchCorrect C.toMachineModel M) :
    SuperPolynomialMass (K.solverCapacity M) :=
  godMove_solverCapacity_superPolynomial_of_searchCorrect
    F K hlower hconsume M hM

/-! ## Axiom trace -/

#print axioms godMove_solverCapacity_superPolynomial_of_searchCorrect
#print axioms not_polynomialSolverCapacity_of_godMoveLowerBound_and_consumption
#print axioms deepSATSearch_of_godMoveSeparateCapacity
#print axioms noCanonicalSATDecisionInP_of_godMoveSeparateCapacityObstruction
#print axioms ktRoute_finalClosure_of_godMoveSeparateCapacityObstruction
#print axioms godMove_separateCapacity_exposes_remaining_gap

end SATDepthMachine
