import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMultiplicativeHolonomyBoundaryCapacity

/-!
# Decision-generator lower-bound barrier

The multiplicative-capacity audit changed the lower-bound unit from the number of
realized signatures to the number of independent observer-visible Boolean generators.
This file tests whether ordinary decision correctness can force many such generators.

It cannot.  Every actual deterministic decision run has a canonical one-generator
observer: expose the final decision bit.  That generator is sufficient to decode the
complete decision on every input.  Consequently any lower bound quantified over all
decision-sufficient observer banks is at most one.

For the concrete decision-relevant SAT-query family, recovering an `n`-bit batch uses
exactly the obvious `n` coordinate generators.  SAT correctness identifies those
coordinates with the semantic holonomy label, but does not make their generator count
superlinear.  Thus a Route G generator lower bound must constrain the operational
observer architecture more strongly than decision sufficiency.  Proving that every P
machine admits the restriction while SAT does not is precisely the missing circuit /
algebraic lower bound; it is not implied by correctness or polynomial time.
-/

namespace PallLean.Paper93.DeepMath.PathB.DecisionGeneratorLowerBoundBarrier

open SATDepthMachine
open PvsNPRunIndexedFaithfulTPhi
open PvsNPRunIndexedFaithfulTPhi.ActualDecisionRun
open PvsNPDynamicHolonomyDecisionRelevance
open PvsNPDynamicHolonomyQueryTranscriptBridge
open MultiplicativeHolonomyBoundaryCapacity
open MultiplicativeHolonomyBoundaryCapacity.DynamicGeneratorBank

variable {Input State : Type*}

/-- An observer bank is decision-sufficient when its final dynamic signature decodes
the actual run's final Boolean answer. -/
structure DecisionSufficientBank
    (R : ActualDecisionRun Input State) (g : ℕ)
    extends DynamicGeneratorBank R g where
  decode : (Fin g → Bool) → Bool
  correct : ∀ x, decode (toDynamicGeneratorBank.signature R.steps x) = R.finalAnswer x

namespace DecisionSufficientBank

/-- Every decision computation has a canonical one-generator sufficient observer:
the generator is the machine's own final Boolean observation. -/
def finalDecision (R : ActualDecisionRun Input State) :
    DecisionSufficientBank R 1 where
  generator := fun _ state => R.observe state
  decode := fun bits => bits ⟨0, by omega⟩
  correct := by
    intro x
    rfl

/-- Therefore one observer generator always suffices for ordinary decision recovery. -/
theorem exists_one_generator (R : ActualDecisionRun Input State) :
    Nonempty (DecisionSufficientBank R 1) :=
  ⟨finalDecision R⟩

/-- A proposed lower bound quantified over every decision-sufficient bank. -/
def ForcesAtLeast (R : ActualDecisionRun Input State) (k : ℕ) : Prop :=
  ∀ g, DecisionSufficientBank R g → k ≤ g

/-- Universal decision-sufficient generator lower bounds are at most one. -/
theorem forcesAtLeast_le_one (R : ActualDecisionRun Input State) {k : ℕ}
    (h : ForcesAtLeast R k) :
    k ≤ 1 :=
  h 1 (finalDecision R)

/-- In particular no actual Boolean decision problem can force two generators under
decision sufficiency alone. -/
theorem not_forcesAtLeast_two (R : ActualDecisionRun Input State) :
    ¬ ForcesAtLeast R 2 := by
  intro h
  have := forcesAtLeast_le_one R h
  omega

end DecisionSufficientBank

/-! ## Coordinatewise batch answers use exactly the obvious coordinates -/

/-- A zero-clock actual run whose state is an `n`-bit answer vector.  This is not a
claim that the answers are cheap to compute; it isolates the observer capacity once
the vector has been produced. -/
def answerVectorRun {Instance : Type*} (n : ℕ)
    (answer : Instance → HolonomySignature n) :
    ActualDecisionRun Instance (HolonomySignature n) where
  encode := answer
  step := fun _ state => state
  steps := 0
  observe := fun _ => false

/-- The coordinate observer bank exposes one generator per answer bit. -/
def answerCoordinateBank {Instance : Type*} (n : ℕ)
    (answer : Instance → HolonomySignature n) :
    DynamicGeneratorBank (answerVectorRun n answer) n where
  generator := fun i state => state i

@[simp] theorem answerCoordinateBank_signature
    {Instance : Type*} (n : ℕ) (answer : Instance → HolonomySignature n)
    (x : Instance) :
    (answerCoordinateBank n answer).signature 0 x = answer x := by
  rfl

/-- Applying the coordinate bank to the concrete SAT-query answers returns the actual
`n`-query answer vector with exactly `n` Boolean generators. -/
theorem independentSAT_coordinateBank_exact
    {n : ℕ} {U : MachineModel} (D : DecisionMachine U)
    (batch : (independentSATQueryFamily n).Instance) :
    (answerCoordinateBank n ((independentSATQueryFamily n).answers D)).signature 0 batch =
      (independentSATQueryFamily n).answers D batch := by
  rfl

/-- SAT correctness makes those same `n` coordinates equal the semantic holonomy
label.  No exponential generator demand follows: there is one generator per output
coordinate. -/
theorem independentSAT_correct_label_with_n_generators
    {n : ℕ} {U : MachineModel} (D : DecisionMachine U) (hD : DecidesSAT U D)
    (batch : (independentSATQueryFamily n).Instance) :
    (answerCoordinateBank n ((independentSATQueryFamily n).answers D)).signature 0 batch =
      (independentSATQueryFamily n).label batch := by
  rw [independentSAT_coordinateBank_exact]
  exact (independentSATQueryFamily n).answers_eq_label D hD batch

/-!
## Audit verdict

There are now two non-circular calibrations:

1. For a single language decision, final-answer sufficiency admits one generator for
   every computation, hard or easy.
2. For an `n`-coordinate SAT batch, correctness exposes the label with `n` generators.

Hence a superpolynomial generator lower bound cannot be based on decision recovery or
coordinate-query recovery alone.  It needs a separately justified restricted class of
local/algebraic generators.  Showing all polynomial-time computations lie in that
class while a concrete NP-complete family requires superpolynomial rank is the actual
general lower-bound theorem.  The observer language does not remove that obligation.
-/

end PallLean.Paper93.DeepMath.PathB.DecisionGeneratorLowerBoundBarrier

#print axioms PallLean.Paper93.DeepMath.PathB.DecisionGeneratorLowerBoundBarrier.DecisionSufficientBank.forcesAtLeast_le_one
#print axioms PallLean.Paper93.DeepMath.PathB.DecisionGeneratorLowerBoundBarrier.DecisionSufficientBank.not_forcesAtLeast_two
#print axioms PallLean.Paper93.DeepMath.PathB.DecisionGeneratorLowerBoundBarrier.independentSAT_correct_label_with_n_generators
