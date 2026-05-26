import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKtRouteTheorem

/-
# Irreducible mass / gravity route surface

This file formalizes the non-circular version of the "large mass creates
separation" idea.

The important distinction is that raw largeness of a mass invariant is not
load-bearing: easy SAT fragments can have large syntactic/Möbius mass.  The
usable target must be an **irreducible transport obstruction**:

* the SAT family carries super-polynomial irreducible mass;
* any correct polynomial SAT search machine must faithfully transport that mass;
* every polynomial SAT search machine has only polynomial transport capacity.

Those three statements are independent lower/upper-bound obligations.  Together
they imply every canonical SAT search machine fails, hence no canonical SAT
decider, without assuming `¬ CanonicalSATDecisionInP` or an equivalent
`HardMetacomplexitySocket` as a hypothesis.
-/

namespace SATDepthMachine

/-! ## Polynomial domination and super-polynomial mass -/

/-- A numeric profile is polynomially bounded using the same simple polynomial
schedule predicate as the K^t route surface. -/
def PolynomiallyBoundedProfile (p : Nat -> Nat) : Prop :=
  IsPolynomialLengthBound p

/-- A mass profile eventually beats every polynomial schedule somewhere.  This
is deliberately stated as an unbounded obstruction rather than an asymptotic
limit, avoiding any real-analysis imports. -/
def SuperPolynomialMass (mass : Nat -> Nat) : Prop :=
  ∀ B : Nat -> Nat,
    PolynomiallyBoundedProfile B -> ∃ n : Nat, B n < mass n

/-- A transported profile is polynomially capacity-bounded if it is pointwise
below some polynomial schedule. -/
def PolynomialTransportCapacity (transport : Nat -> Nat) : Prop :=
  ∃ B : Nat -> Nat,
    PolynomiallyBoundedProfile B ∧ ∀ n : Nat, transport n ≤ B n

/-! ## Irreducible gravitational mass model -/

/-- A gravitational mass model for a canonical machine surface.

`familyMass n` is the irreducible mass carried by the chosen SAT family at size
index `n`.  `transportedMass M n` is the amount of that mass visible/transported
through candidate search machine `M`.

The structure intentionally does not define the concrete invariant.  Later files
can instantiate it with Möbius interaction mass, SPDP width-rank mass,
communication rectangle mass, holonomy/curvature flux, or another N-frame
quantity. -/
structure IrreducibleMassModel (C : CanonicalMachineSurface) where
  familyMass : Nat -> Nat
  transportedMass : SearchMachine C.toMachineModel -> Nat -> Nat

/-- A search machine faithfully transports the family mass if it covers the
irreducible family mass pointwise. -/
def FaithfullyTransportsMass
    {C : CanonicalMachineSurface}
    (G : IrreducibleMassModel C)
    (M : SearchMachine C.toMachineModel) : Prop :=
  ∀ n : Nat, G.familyMass n ≤ G.transportedMass M n

/-- The NP-side obligation: the selected SAT family has irreducible mass too
large for any polynomial schedule. -/
def IrreducibleFamilyMassLowerBound
    {C : CanonicalMachineSurface}
    (G : IrreducibleMassModel C) : Prop :=
  SuperPolynomialMass G.familyMass

/-- The P-side capacity obligation: every correct canonical SAT search machine
has only polynomial mass-transport capacity. -/
def PolynomialSolverMassUpperBound
    {C : CanonicalMachineSurface}
    (G : IrreducibleMassModel C) : Prop :=
  ∀ M : SearchMachine C.toMachineModel,
    SearchCorrect C.toMachineModel M ->
      PolynomialTransportCapacity (G.transportedMass M)

/-- The bridge obligation: correctness forces faithful transport of the selected
irreducible SAT-family mass.  This is where a concrete invariant must connect
semantic SAT search to the N-frame/gravity quantity. -/
def CorrectSolverFaithfulMassTransport
    {C : CanonicalMachineSurface}
    (G : IrreducibleMassModel C) : Prop :=
  ∀ M : SearchMachine C.toMachineModel,
    SearchCorrect C.toMachineModel M -> FaithfullyTransportsMass G M

/-- Non-circular gravitational obstruction package.

Unlike `HardMetacomplexitySocket`, this package does not contain
`¬ CanonicalSATDecisionInP`, `DeepSATSearch`, or `NoShortFastCompleteGenerator`.
It contains only the three mass-theoretic obligations that would make the
"gravity" route genuinely load-bearing. -/
structure IrreducibleMassGravityObstruction
    (C : CanonicalMachineSurface) where
  model : IrreducibleMassModel C
  lowerBound : IrreducibleFamilyMassLowerBound model
  upperBound : PolynomialSolverMassUpperBound model
  faithfulTransport : CorrectSolverFaithfulMassTransport model

/-! ## Core contradiction: faithful super-polynomial mass cannot pass through
polynomial transport capacity. -/

/-- A single correct search machine cannot simultaneously faithfully transport a
super-polynomial family mass and have polynomial transport capacity. -/
theorem not_searchCorrect_of_irreducibleMassBounds
    {C : CanonicalMachineSurface}
    (G : IrreducibleMassModel C)
    (hlower : IrreducibleFamilyMassLowerBound G)
    (hupper : PolynomialSolverMassUpperBound G)
    (hfaithful : CorrectSolverFaithfulMassTransport G)
    (M : SearchMachine C.toMachineModel) :
    ¬ SearchCorrect C.toMachineModel M := by
  intro hcorrect
  rcases hupper M hcorrect with ⟨B, hBpoly, hcap⟩
  rcases hlower B hBpoly with ⟨n, hlt⟩
  have hfamily_le_transport : G.familyMass n ≤ G.transportedMass M n :=
    hfaithful M hcorrect n
  have htransport_le_B : G.transportedMass M n ≤ B n := hcap n
  have hfamily_le_B : G.familyMass n ≤ B n :=
    Nat.le_trans hfamily_le_transport htransport_le_B
  exact (Nat.not_lt_of_ge hfamily_le_B) hlt

/-- The obstruction gives canonical deep SAT search: every canonical search
machine fails on some satisfiable CNF. -/
theorem canonicalDeepSATSearch_of_irreducibleMassGravityObstruction
    (C : CanonicalMachineSurface)
    (H : IrreducibleMassGravityObstruction C) :
    CanonicalDeepSATSearch C := by
  exact (canonicalDeepSATSearch_iff_forall_not_searchCorrect C).mpr
    (not_searchCorrect_of_irreducibleMassBounds H.model
      H.lowerBound H.upperBound H.faithfulTransport)

/-- Main closure: irreducible mass/gravity obstruction rules out canonical
polynomial SAT decision. -/
theorem noCanonicalSATDecisionInP_of_irreducibleMassGravityObstruction
    (C : CanonicalMachineSurface)
    (H : IrreducibleMassGravityObstruction C) :
    ¬ CanonicalSATDecisionInP C :=
  canonicalNoDecider_of_deepSATSearch C
    (canonicalDeepSATSearch_of_irreducibleMassGravityObstruction C H)

/-- Described-surface version: the same obstruction implies the existing
metacomplexity hard socket as a consequence, not as an assumption. -/
theorem hardMetacomplexitySocket_of_irreducibleMassGravityObstruction
    (D : DescribedCanonicalSurface)
    (H : IrreducibleMassGravityObstruction D.surface) :
    HardMetacomplexitySocket D :=
  hardMetacomplexitySocket_of_noCanonicalSATDecisionInP D
    (noCanonicalSATDecisionInP_of_irreducibleMassGravityObstruction
      D.surface H)

/-- Final route closure from mass/gravity obligations: no canonical SAT decider
and every polynomial length-scheduled generator fails. -/
theorem ktRoute_finalClosure_of_irreducibleMassGravityObstruction
    (D : DescribedCanonicalSurface)
    (H : IrreducibleMassGravityObstruction D.surface) :
    (¬ CanonicalSATDecisionInP D.surface) ∧
      NoPolynomialLengthScheduledCompleteGenerators D :=
  ktRoute_finalClosure D
    (hardMetacomplexitySocket_of_irreducibleMassGravityObstruction D H)

/-! ## Axiom trace -/

#print axioms not_searchCorrect_of_irreducibleMassBounds
#print axioms canonicalDeepSATSearch_of_irreducibleMassGravityObstruction
#print axioms noCanonicalSATDecisionInP_of_irreducibleMassGravityObstruction
#print axioms hardMetacomplexitySocket_of_irreducibleMassGravityObstruction
#print axioms ktRoute_finalClosure_of_irreducibleMassGravityObstruction

end SATDepthMachine
