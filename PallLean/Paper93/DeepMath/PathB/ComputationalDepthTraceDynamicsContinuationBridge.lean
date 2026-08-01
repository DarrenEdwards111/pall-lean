import PallLean.Paper93.DeepMath.PathB.ComputationalDepthContinuationCompleteDynamicHolonomy
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPNFrameDynamicMERAHolonomy

/-!
# Actual trace dynamics to continuation-complete holonomy

The repository has two complementary dynamical facts.

* `DynamicHolonomyMERADecoder.stateAt_injective` proves deterministic no-merging:
  if the final state exactly decodes a semantic signature, distinct signatures were
  already distinct at every earlier time.
* `ContinuationCompleteBank.separated_forces_generators` proves the residual lower
  bound once a prefix-stable boundary can answer every future continuation.

This file supplies the operational connector between them.  A
`TraceContinuationFactorization` is not an observer-supplied rank field: its exposed
bits are functions of the actual state of an `ActualDecisionRun` at a certified time.
The two substantive obligations are stated explicitly:

1. the exposed trace is independent of the not-yet-supplied suffix;
2. the exposed trace together with any suffix reconstructs the real final answer.

From those fields we construct a genuine `ContinuationCompleteBank`, so all existing
holonomy lower bounds apply directly.  The equality calibration then proves the
guardrail: bare deterministic trace dynamics plus the final decision bit do not supply
the connector.  Thus adaptive rereading has not been assumed away; it must be handled
by proving that an actual crossing history, conserved trace, or other physical boundary
satisfies the two factorization fields.

Nothing here assumes a SAT lower bound or proves `P != NP`.  It makes the exact
trace-to-holonomy socket executable and prevents final-answer correctness from being
silently substituted for continuation completeness.
-/

namespace PallLean.Paper93.DeepMath.PathB.TraceDynamicsContinuationBridge

open PvsNPRunIndexedFaithfulTPhi
open PvsNPRunIndexedFaithfulTPhi.ActualDecisionRun
open MultiplicativeHolonomyBoundaryCapacity
open MultiplicativeHolonomyBoundaryCapacity.DynamicGeneratorBank
open ContinuationObserver
open ContinuationCompleteDynamicHolonomy
open PvsNPNFrameDynamicMERAHolonomy

variable {Pre Suf State : Type*}

/-- A certified continuation factorization through bits exposed from one actual
trace state.  This is the operational datum needed to turn trace dynamics into
continuation-complete holonomy. -/
structure TraceContinuationFactorization
    (R : ActualDecisionRun (Pre × Suf) State) (g : Nat) where
  time : Nat
  time_le : time ≤ R.steps
  expose : State → (Fin g → Bool)
  prefixStable : ∀ p s t,
    expose (R.stateAt time (p, s)) = expose (R.stateAt time (p, t))
  finish : (Fin g → Bool) → Suf → Bool
  finishCorrect : ∀ p s,
    finish (expose (R.stateAt time (p, s))) s = R.finalAnswer (p, s)

namespace TraceContinuationFactorization

/-- The trace exposure is a real generator bank on the actual run state. -/
def toGeneratorBank
    {R : ActualDecisionRun (Pre × Suf) State} {g : Nat}
    (F : TraceContinuationFactorization R g) : DynamicGeneratorBank R g where
  generator := fun i state => F.expose state i

@[simp] theorem toGeneratorBank_signature
    {R : ActualDecisionRun (Pre × Suf) State} {g : Nat}
    (F : TraceContinuationFactorization R g) (p : Pre) (s : Suf) :
    F.toGeneratorBank.signature F.time (p, s) =
      F.expose (R.stateAt F.time (p, s)) := by
  rfl

/-- The operational trace factorization constructs the repository's
continuation-complete dynamic-holonomy boundary. -/
def toContinuationCompleteBank
    {R : ActualDecisionRun (Pre × Suf) State} {g : Nat}
    (F : TraceContinuationFactorization R g) : ContinuationCompleteBank R g where
  time := F.time
  time_le := F.time_le
  bank := F.toGeneratorBank
  prefixStable := by
    intro p s t
    exact F.prefixStable p s t
  finish := F.finish
  finishCorrect := by
    intro p s
    exact F.finishCorrect p s

/-- Hence any separated residual family crossing this actual trace boundary forces
the corresponding number of observer-visible Boolean generators. -/
theorem separated_forces_generators [Inhabited Suf]
    {R : ActualDecisionRun (Pre × Suf) State} {g : Nat}
    (F : TraceContinuationFactorization R g)
    {P : Finset Pre}
    (hsep : Separated (fun p s => R.finalAnswer (p, s)) P)
    {k : Nat} (hmany : 2 ^ k ≤ P.card) :
    k ≤ g := by
  exact F.toContinuationCompleteBank.separated_forces_generators hsep hmany

end TraceContinuationFactorization

/-! ## Dynamic no-merging is the conservation law, not the semantic forcing law -/

/-- Existing exact dynamic holonomy recovery really is conserved through every
intermediate trace slice.  This theorem records the precise dynamics lemma used by
the connector: a common deterministic future cannot recover signatures that merged
at an earlier boundary. -/
theorem exact_recovery_no_merging_at_every_cut
    {M : MERAFamily} {n : Nat}
    (D : DynamicHolonomyMERADecoder M n)
    (time : Nat) (htime : time ≤ M.layers n) :
    Function.Injective (D.stateAt time) :=
  D.stateAt_injective time htime

/-- Consequently every exact-recovery trace slice has at least `2^n` states. -/
theorem exact_recovery_two_pow_capacity_at_every_cut
    {M : MERAFamily} {n : Nat}
    (D : DynamicHolonomyMERADecoder M n)
    (time : Nat) (htime : time ≤ M.layers n) :
    2 ^ n ≤ @Fintype.card D.BoundaryState D.stateFintype :=
  D.two_pow_le_boundary_card_at_time time htime

/-! ## Guardrail: a final decision trace is not the connector -/

/-- Equality already refutes the claim that one exposed trace bit plus generic
determinism is continuation-complete.  Any construction of the connector must use
real prefix/suffix geometry (for example a complete crossing history), not merely
the final Boolean answer. -/
theorem no_one_bit_trace_factorization_for_equality
    {n : Nat} (hn : 2 ≤ n) :
    ¬ Nonempty
      (TraceContinuationFactorization
        (ContinuationCompleteDynamicHolonomy.equalityRun n) 1) := by
  rintro ⟨F⟩
  exact
    (ContinuationCompleteDynamicHolonomy.no_one_generator_equality hn)
      ⟨F.toContinuationCompleteBank⟩

end PallLean.Paper93.DeepMath.PathB.TraceDynamicsContinuationBridge

#print axioms PallLean.Paper93.DeepMath.PathB.TraceDynamicsContinuationBridge.TraceContinuationFactorization.toContinuationCompleteBank
#print axioms PallLean.Paper93.DeepMath.PathB.TraceDynamicsContinuationBridge.TraceContinuationFactorization.separated_forces_generators
#print axioms PallLean.Paper93.DeepMath.PathB.TraceDynamicsContinuationBridge.exact_recovery_no_merging_at_every_cut
#print axioms PallLean.Paper93.DeepMath.PathB.TraceDynamicsContinuationBridge.exact_recovery_two_pow_capacity_at_every_cut
#print axioms PallLean.Paper93.DeepMath.PathB.TraceDynamicsContinuationBridge.no_one_bit_trace_factorization_for_equality
