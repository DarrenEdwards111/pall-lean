import PallLean.Paper93.DeepMath.PathB.ComputationalDepthConcreteGodMoveMass

/-
# No-go audit for the concrete God-Move transported-mass upper bound

This file answers the immediate question:

  Can we now prove a non-circular polynomial transport upper bound for the
  concrete semantic God-Move mass?

For the concrete mass in `ComputationalDepthConcreteGodMoveMass`, the answer is
no in the strong sense: if the frame has super-polynomial family mass, then any
correct SAT searcher faithfully transports all of it, so its transported-mass
profile is also super-polynomial.  Therefore a polynomial upper bound on that
same transported-mass profile is incompatible with correctness.

This is not a failure of Lean plumbing; it identifies the mathematical boundary.
To get a viable N-frame/God-Move proof, the P-side upper bound must be on a
separate *resource/capacity/compression* invariant, together with a lower theorem
saying faithful transport of irreducible mass consumes that capacity.  It cannot
be a direct polynomial bound on the amount of semantic solved-mass transported.
-/

namespace SATDepthMachine

/-- If a God-Move frame has super-polynomial family mass, then every correct
search machine has super-polynomial transported mass. -/
theorem godMove_transportedMass_superPolynomial_of_searchCorrect
    {C : CanonicalMachineSurface}
    (F : GodMoveFrame)
    (hlower : GodMoveFamilyMassLowerBound F)
    (M : SearchMachine C.toMachineModel)
    (hM : SearchCorrect C.toMachineModel M) :
    SuperPolynomialMass (GodMoveFrame.transportedMass F M) := by
  intro B hBpoly
  rcases hlower B hBpoly with ⟨n, hlt⟩
  refine ⟨n, Nat.lt_of_lt_of_le hlt ?_⟩
  exact godMove_faithfulTransport_of_searchCorrect F M hM n

/-- Consequently, for a super-polynomial God-Move frame, no correct search
machine has polynomial transport capacity for the concrete transported-mass
profile. -/
theorem no_polynomialTransportCapacity_for_correctSolver_on_superPolynomialGodMoveFrame
    {C : CanonicalMachineSurface}
    (F : GodMoveFrame)
    (hlower : GodMoveFamilyMassLowerBound F)
    (M : SearchMachine C.toMachineModel)
    (hM : SearchCorrect C.toMachineModel M) :
    ¬ PolynomialTransportCapacity (GodMoveFrame.transportedMass F M) := by
  exact not_polynomialTransportCapacity_of_godMoveLowerBound_and_searchCorrect
    F hlower M hM

/-- If a correct search machine exists for a super-polynomial God-Move frame,
then the concrete P-side upper-bound predicate is false. -/
theorem not_godMovePolynomialTransportUpperBound_of_shallowSearch
    {C : CanonicalMachineSurface}
    (F : GodMoveFrame)
    (hlower : GodMoveFamilyMassLowerBound F)
    (hshallow : ShallowSATSearch C.toMachineModel) :
    ¬ GodMovePolynomialTransportUpperBound C F := by
  intro hupper
  rcases hshallow with ⟨M, hM⟩
  exact no_polynomialTransportCapacity_for_correctSolver_on_superPolynomialGodMoveFrame
    F hlower M hM (hupper M hM)

/-- Equivalently, for the concrete semantic transported-mass profile, the P-side
upper-bound predicate plus a super-polynomial lower bound already implies deep
SAT search.  Thus this upper-bound predicate is P-vs-NP-strength for this mass;
it is not a separately easy polynomial-time fact. -/
theorem deepSATSearch_of_godMoveLowerBound_and_polynomialTransportUpperBound
    (C : CanonicalMachineSurface)
    (F : GodMoveFrame)
    (hlower : GodMoveFamilyMassLowerBound F)
    (hupper : GodMovePolynomialTransportUpperBound C F) :
    DeepSATSearch C.toMachineModel := by
  intro hshallow
  exact not_godMovePolynomialTransportUpperBound_of_shallowSearch
    F hlower hshallow hupper

/-- The no-go packaged as canonical non-decision: if someone supplies the direct
polynomial transported-mass upper bound for a super-polynomial God-Move frame,
then the existing route closes immediately.  Hence proving that upper bound is
exactly the hard lower-bound step, not a harmless complexity estimate. -/
theorem noCanonicalSATDecisionInP_of_godMoveLowerBound_and_polynomialTransportUpperBound
    (C : CanonicalMachineSurface)
    (F : GodMoveFrame)
    (hlower : GodMoveFamilyMassLowerBound F)
    (hupper : GodMovePolynomialTransportUpperBound C F) :
    ¬ CanonicalSATDecisionInP C :=
  canonicalNoDecider_of_deepSATSearch C
    (deepSATSearch_of_godMoveLowerBound_and_polynomialTransportUpperBound
      C F hlower hupper)

/-! ## Axiom trace -/

#print axioms godMove_transportedMass_superPolynomial_of_searchCorrect
#print axioms no_polynomialTransportCapacity_for_correctSolver_on_superPolynomialGodMoveFrame
#print axioms not_godMovePolynomialTransportUpperBound_of_shallowSearch
#print axioms deepSATSearch_of_godMoveLowerBound_and_polynomialTransportUpperBound
#print axioms noCanonicalSATDecisionInP_of_godMoveLowerBound_and_polynomialTransportUpperBound

end SATDepthMachine
