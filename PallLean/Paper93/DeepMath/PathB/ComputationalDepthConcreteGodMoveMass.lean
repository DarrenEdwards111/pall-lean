import PallLean.Paper93.DeepMath.PathB.ComputationalDepthIrreducibleMassGravity

/-
# Concrete God-Move mass: semantic satisfiable-challenge layers

This file instantiates the abstract irreducible-mass route with a concrete
semantic N-frame/God-Move mass.

A `GodMoveChallenge` is a CNF formula together with an actual satisfying
witness.  A `GodMoveFrame` is a length-indexed list of such challenges.  Its
mass at index `n` is simply the number of certified satisfiable challenges in
layer `n`.

A search machine transports one challenge when its returned output verifies as a
satisfying assignment.  Therefore every correct SAT search machine faithfully
transports every certified God-Move layer.  This is the concrete faithful
transport theorem we wanted.

What is still not proved here:

* that any particular God-Move frame has super-polynomial irreducible mass;
* that every polynomial SAT solver has polynomial transport capacity for this
  concrete transported-mass profile.

Those two statements are now explicit, concrete obligations rather than hidden
uses of `P ≠ NP`.
-/

namespace SATDepthMachine

/-! ## Certified satisfiable God-Move layers -/

/-- One semantic God-Move challenge: a CNF formula plus a known satisfying
witness.  The witness makes the layer semantic rather than syntactic; every
challenge is genuinely satisfiable by construction. -/
structure GodMoveChallenge where
  formula : CNF
  witness : RawAssignment
  witness_sat : Satisfies formula witness

/-- A concrete N-frame/God-Move family: each index has a finite layer of
certified satisfiable challenges. -/
structure GodMoveFrame where
  layer : Nat -> List GodMoveChallenge

/-- A challenge is transported by a search machine when the machine's output
passes the ordinary SAT witness checker. -/
def GodMoveChallenge.isTransportedBy
    {U : MachineModel}
    (M : SearchMachine U) (χ : GodMoveChallenge) : Bool :=
  checkSearchOutput χ.formula (U.searchRun M.code χ.formula)

/-- Concrete God-Move family mass: number of certified satisfiable challenges in
layer `n`. -/
def GodMoveFrame.familyMass (F : GodMoveFrame) (n : Nat) : Nat :=
  (F.layer n).length

/-- Concrete transported mass: number of layer-`n` challenges whose witness is
successfully produced by `M` and verified. -/
def GodMoveFrame.transportedMass
    {C : CanonicalMachineSurface}
    (F : GodMoveFrame) (M : SearchMachine C.toMachineModel) (n : Nat) : Nat :=
  ((F.layer n).filter (fun χ => χ.isTransportedBy M)).length

/-- The concrete God-Move frame as an abstract irreducible-mass model. -/
def GodMoveFrame.toIrreducibleMassModel
    (C : CanonicalMachineSurface)
    (F : GodMoveFrame) : IrreducibleMassModel C where
  familyMass := F.familyMass
  transportedMass := fun M n => GodMoveFrame.transportedMass F M n

/-! ## Basic sanity bounds -/

/-- Transported mass never exceeds the available challenge mass in a layer. -/
theorem godMove_transportedMass_le_familyMass
    {C : CanonicalMachineSurface}
    (F : GodMoveFrame) (M : SearchMachine C.toMachineModel) (n : Nat) :
    GodMoveFrame.transportedMass F M n ≤ F.familyMass n := by
  unfold GodMoveFrame.transportedMass GodMoveFrame.familyMass
  exact List.length_filter_le _ _

/-- If a search machine is correct, every certified challenge in every layer is
transported. -/
theorem godMove_filter_eq_self_of_searchCorrect
    {C : CanonicalMachineSurface}
    (F : GodMoveFrame)
    (M : SearchMachine C.toMachineModel)
    (hM : SearchCorrect C.toMachineModel M)
    (n : Nat) :
    (F.layer n).filter (fun χ => χ.isTransportedBy M) = F.layer n := by
  apply List.filter_eq_self.mpr
  intro χ _hmem
  unfold GodMoveChallenge.isTransportedBy
  rw [checkSearchOutput_true_iff]
  exact hM χ.formula ⟨χ.witness, χ.witness_sat⟩

/-- Concrete faithful transport theorem: every correct polynomial SAT search
machine faithfully transports the God-Move mass. -/
theorem godMove_faithfulTransport_of_searchCorrect
    {C : CanonicalMachineSurface}
    (F : GodMoveFrame)
    (M : SearchMachine C.toMachineModel)
    (hM : SearchCorrect C.toMachineModel M) :
    FaithfullyTransportsMass (GodMoveFrame.toIrreducibleMassModel C F) M := by
  intro n
  change F.familyMass n ≤ GodMoveFrame.transportedMass F M n
  unfold GodMoveFrame.familyMass GodMoveFrame.transportedMass
  have hfilter := godMove_filter_eq_self_of_searchCorrect F M hM n
  rw [hfilter]

/-- Packaged bridge obligation for the concrete God-Move mass model. -/
theorem godMove_correctSolverFaithfulMassTransport
    (C : CanonicalMachineSurface)
    (F : GodMoveFrame) :
    CorrectSolverFaithfulMassTransport
      (GodMoveFrame.toIrreducibleMassModel C F) := by
  intro M hM
  exact godMove_faithfulTransport_of_searchCorrect F M hM

/-! ## Concrete route surface -/

/-- Diagnostic boundary: if a God-Move frame has super-polynomial family mass,
then no correct search machine can have polynomial transport capacity for this
semantic transported-mass profile.

This is the honest pressure point.  For this concrete mass, faithful transport is
fully proved, but the P-side polynomial-capacity theorem is exactly the hard
structural lower-bound content: it cannot be obtained merely from correctness. -/
theorem not_polynomialTransportCapacity_of_godMoveLowerBound_and_searchCorrect
    {C : CanonicalMachineSurface}
    (F : GodMoveFrame)
    (hlower : SuperPolynomialMass F.familyMass)
    (M : SearchMachine C.toMachineModel)
    (hM : SearchCorrect C.toMachineModel M) :
    ¬ PolynomialTransportCapacity (GodMoveFrame.transportedMass F M) := by
  intro hcap
  rcases hcap with ⟨B, hBpoly, htransport_le_B⟩
  rcases hlower B hBpoly with ⟨n, hlt⟩
  have hfamily_le_transport : F.familyMass n ≤ GodMoveFrame.transportedMass F M n :=
    godMove_faithfulTransport_of_searchCorrect F M hM n
  have hfamily_le_B : F.familyMass n ≤ B n :=
    Nat.le_trans hfamily_le_transport (htransport_le_B n)
  exact (Nat.not_lt_of_ge hfamily_le_B) hlt

/-- Concrete lower-bound obligation for a God-Move frame: its certified
satisfiable layers have super-polynomial mass. -/
def GodMoveFamilyMassLowerBound (F : GodMoveFrame) : Prop :=
  SuperPolynomialMass F.familyMass

/-- Concrete P-side capacity obligation: every correct polynomial searcher
transports only polynomially much God-Move mass. -/
def GodMovePolynomialTransportUpperBound
    (C : CanonicalMachineSurface) (F : GodMoveFrame) : Prop :=
  PolynomialSolverMassUpperBound (GodMoveFrame.toIrreducibleMassModel C F)

/-- A fully concrete God-Move/gravity obstruction package.  The faithful
transport field is no longer an assumption: it is supplied by
`godMove_correctSolverFaithfulMassTransport`. -/
structure ConcreteGodMoveGravityObstruction
    (C : CanonicalMachineSurface) where
  frame : GodMoveFrame
  lowerBound : GodMoveFamilyMassLowerBound frame
  upperBound : GodMovePolynomialTransportUpperBound C frame

/-- Convert the concrete God-Move obstruction into the abstract irreducible-mass
obstruction from the previous file. -/
def ConcreteGodMoveGravityObstruction.toIrreducible
    {C : CanonicalMachineSurface}
    (H : ConcreteGodMoveGravityObstruction C) :
    IrreducibleMassGravityObstruction C where
  model := GodMoveFrame.toIrreducibleMassModel C H.frame
  lowerBound := H.lowerBound
  upperBound := H.upperBound
  faithfulTransport := godMove_correctSolverFaithfulMassTransport C H.frame

/-- Main concrete closure theorem: a God-Move frame with super-polynomial
certified challenge mass and polynomial transport upper bounds for all correct
searchers rules out canonical polynomial SAT decision. -/
theorem noCanonicalSATDecisionInP_of_concreteGodMoveGravityObstruction
    (C : CanonicalMachineSurface)
    (H : ConcreteGodMoveGravityObstruction C) :
    ¬ CanonicalSATDecisionInP C :=
  noCanonicalSATDecisionInP_of_irreducibleMassGravityObstruction C
    H.toIrreducible

/-- Described-surface closure: the concrete God-Move obstruction also implies
the existing K^t/metacomplexity route closure. -/
theorem ktRoute_finalClosure_of_concreteGodMoveGravityObstruction
    (D : DescribedCanonicalSurface)
    (H : ConcreteGodMoveGravityObstruction D.surface) :
    (¬ CanonicalSATDecisionInP D.surface) ∧
      NoPolynomialLengthScheduledCompleteGenerators D :=
  ktRoute_finalClosure_of_irreducibleMassGravityObstruction D
    H.toIrreducible

/-! ## Axiom trace -/

#print axioms godMove_transportedMass_le_familyMass
#print axioms godMove_filter_eq_self_of_searchCorrect
#print axioms godMove_faithfulTransport_of_searchCorrect
#print axioms godMove_correctSolverFaithfulMassTransport
#print axioms not_polynomialTransportCapacity_of_godMoveLowerBound_and_searchCorrect
#print axioms noCanonicalSATDecisionInP_of_concreteGodMoveGravityObstruction
#print axioms ktRoute_finalClosure_of_concreteGodMoveGravityObstruction

end SATDepthMachine
