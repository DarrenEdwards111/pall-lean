import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMetacomplexityFrontier

/-!
# Combination-basis frontier

**STATUS: FRONTIER / GUARDRAIL, NOT A P-vs-NP PROOF.**

This file records the sharper lesson from the failed direct 2-SAT-to-3-SAT
transfer.

* 2-SAT closes over unary literal implications.
* 3-SAT forces higher-order literal combinations to become the state.
* A polynomial-size compressed basis for all such combinations would be a
  worst-case SAT compression/decision mechanism.
* Ruling out every such worst-case basis is therefore the same lower-bound
  target as ruling out polynomial-time signed SAT deciders.

The analytic-combinatorics / generating-function intuition is still useful, but
on the honest axis: average-case signals feed MCSP / `K^t` / metacomplexity.
For worst-case SAT, coefficient extraction or partition-function summaries
inherit the same obstruction; the bridge is endpoint-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB

open TuringMachine

/-! ## Polynomial combination-basis profiles -/

/-- A symbolic profile for a compressed basis of higher-order literal
combinations.

`stateCount n` is the number of combination states retained at length/scale `n`.
The field `stateCount_le_polynomial` is the polynomial-size side condition.  It
does not say the basis is correct for SAT; it only records that the proposed
basis avoids the exponential subset-lattice blow-up. -/
structure LiteralCombinationBasisProfile : Type where
  maxCombinationOrder : Nat
  stateCount : Nat -> Nat
  polynomialDegree : Nat
  stateCount_le_polynomial :
    forall n : Nat, stateCount n <= (n + 1) ^ polynomialDegree

/-- The trivial zero-state profile, useful for showing that the abstract
"successful basis" interface is equivalent to the decider it compiles to. -/
def zeroCombinationBasisProfile : LiteralCombinationBasisProfile where
  maxCombinationOrder := 0
  stateCount := fun _ => 0
  polynomialDegree := 0
  stateCount_le_polynomial := by
    intro _n
    exact Nat.zero_le _

/-! ## Worst-case SAT-preserving bases -/

/-- A successful worst-case polynomial combination basis for signed SAT.

The important field is `compiledDecider_correct`: once a basis is strong enough
to preserve satisfiability for all signed 3-CNF instances and can be evaluated
inside the supplied P-time class, it yields a P-time signed SAT decider.  The
file keeps the SAT-preservation predicate explicit rather than pretending to
prove it from generating functions or circle-method asymptotics. -/
structure WorstCaseSATCombinationBasisCompression
    (enc : SignedFormulaEncoding)
    (PT : PTimeSATPolynomialTime enc) : Type where
  profile : LiteralCombinationBasisProfile
  preservationPredicate : Prop
  preservation_holds : preservationPredicate
  compiledDecider : DTM
  compiledDecider_correct : PTimeSignedSATDecider enc PT compiledDecider

/-- A successful worst-case combination basis is exactly a P-time signed SAT
decider, at the level of this honest interface.

The reverse direction is deliberately bookkeeping: given a decider, one can
package a vacuous profile around it.  This is the guardrail: a worst-case
polynomial combination-basis bridge is not a smaller lemma unless the
SAT-preservation/evaluation mechanism is independently constructed. -/
theorem combinationBasisCompression_iff_pTimeSignedSATDecider
    {enc : SignedFormulaEncoding}
    (PT : PTimeSATPolynomialTime enc) :
    Nonempty (WorstCaseSATCombinationBasisCompression enc PT) <->
      exists M : DTM, PTimeSignedSATDecider enc PT M := by
  constructor
  · rintro ⟨B⟩
    exact ⟨B.compiledDecider, B.compiledDecider_correct⟩
  · rintro ⟨M, hM⟩
    exact ⟨{
      profile := zeroCombinationBasisProfile
      preservationPredicate := True
      preservation_holds := trivial
      compiledDecider := M
      compiledDecider_correct := hM
    }⟩

/-- No worst-case polynomial combination basis exists. -/
def NoPolynomialCombinationBasisForSignedSAT
    (enc : SignedFormulaEncoding)
    (PT : PTimeSATPolynomialTime enc) : Prop :=
  Not (Nonempty (WorstCaseSATCombinationBasisCompression enc PT))

/-- Ruling out all worst-case polynomial combination bases is exactly the
metacomplexity/SAT-in-P obstruction.

This theorem is the formal version of the fork:

* construct such a basis -> SAT is in the supplied P-time class;
* rule out all such bases -> the no-decider target.
-/
theorem noPolynomialCombinationBasis_iff_metacomplexityObstruction
    {enc : SignedFormulaEncoding}
    (PT : PTimeSATPolynomialTime enc) :
    NoPolynomialCombinationBasisForSignedSAT enc PT <->
      MetacomplexityNoPTimeDecider enc PT := by
  constructor
  · intro hno hdec
    exact hno
      ((combinationBasisCompression_iff_pTimeSignedSATDecider PT).mpr hdec)
  · intro hmeta hbasis
    exact hmeta
      ((combinationBasisCompression_iff_pTimeSignedSATDecider PT).mp hbasis)

/-- At an observer channel gap, the absence of polynomial combination bases is
equivalent to the N-frame observer boundary. -/
theorem observerBoundary_iff_noPolynomialCombinationBasis
    {enc : SignedFormulaEncoding}
    (PT : PTimeSATPolynomialTime enc)
    (O : DimensionalObserver)
    (B : HighDimensionalBoundary)
    (hgap : O.channelCapacity < B.independentDirections) :
    Nonempty (PTimeDeciderDimensionalForce PT O B) <->
      NoPolynomialCombinationBasisForSignedSAT enc PT := by
  exact
    (observerBoundary_iff_metacomplexityObstruction PT O B hgap).trans
      (noPolynomialCombinationBasis_iff_metacomplexityObstruction PT).symm

/-! ## Generating-function / average-case route into metacomplexity -/

/-- A generating-function or circle-method program, stated on the honest
average-case/metacomplexity axis.

`averageCaseSignal` may be a partition-function cancellation theorem, a
coefficient-extraction hardness statement, a K^t lower bound, or an MCSP-style
compression obstruction.  The key field is `signal_to_metacomplexity`: the
program only affects the worst-case observer boundary if the signal amplifies
to the SAT-in-P face of the metacomplexity obstruction. -/
structure GeneratingFunctionMetacomplexityProgram
    (enc : SignedFormulaEncoding)
    (PT : PTimeSATPolynomialTime enc) : Type 1 where
  summaryObject : Type
  averageCaseSignal : Prop
  signal_to_metacomplexity :
    averageCaseSignal -> MetacomplexityNoPTimeDecider enc PT

/-- An average-case generating-function signal yields the metacomplexity
obstruction only through its explicit amplification map. -/
theorem metacomplexityObstruction_of_generatingFunctionSignal
    {enc : SignedFormulaEncoding}
    {PT : PTimeSATPolynomialTime enc}
    (P : GeneratingFunctionMetacomplexityProgram enc PT)
    (hsignal : P.averageCaseSignal) :
    MetacomplexityNoPTimeDecider enc PT :=
  P.signal_to_metacomplexity hsignal

/-- The same signal yields the observer boundary at a channel gap, but only
after the explicit metacomplexity amplification step. -/
theorem observerBoundary_of_generatingFunctionSignal
    {enc : SignedFormulaEncoding}
    (PT : PTimeSATPolynomialTime enc)
    (O : DimensionalObserver)
    (B : HighDimensionalBoundary)
    (hgap : O.channelCapacity < B.independentDirections)
    (P : GeneratingFunctionMetacomplexityProgram enc PT)
    (hsignal : P.averageCaseSignal) :
    Nonempty (PTimeDeciderDimensionalForce PT O B) :=
  (observerBoundary_iff_metacomplexityObstruction PT O B hgap).mpr
    (metacomplexityObstruction_of_generatingFunctionSignal P hsignal)

/-! ## Kernel-only axiom trace -/

#print axioms combinationBasisCompression_iff_pTimeSignedSATDecider
#print axioms noPolynomialCombinationBasis_iff_metacomplexityObstruction
#print axioms observerBoundary_iff_noPolynomialCombinationBasis
#print axioms metacomplexityObstruction_of_generatingFunctionSignal
#print axioms observerBoundary_of_generatingFunctionSignal

end PallLean.Paper93.DeepMath.PathB
