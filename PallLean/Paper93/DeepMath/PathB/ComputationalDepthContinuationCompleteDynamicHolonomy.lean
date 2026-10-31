import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDecisionGeneratorLowerBoundBarrier
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthContinuationObserver

/-!
# Continuation-complete dynamic holonomy

The final-decision generator barrier shows that ordinary decision sufficiency is too
weak for Route G: every deterministic decider has the one-bit quotient given by its
final answer.  This file isolates the stronger semantic property that a useful
dynamic boundary must have.

A boundary observed after a prefix is **continuation-complete** when

* its signature is independent of the not-yet-supplied suffix, and
* that signature, together with any suffix, reconstructs the final decision.

This is the dynamic trace version of continuation faithfulness.  It makes the
holonomy generators decision-relevant without confusing one final answer with the
whole residual function.  Pairwise-separated residual rows must have different
signatures, so `g` Boolean generators carry at most `2^g` rows.

The equality calibration proves the distinction exactly.  Every continuation-
complete dynamic boundary for `n`-bit equality needs `n` generators, whereas the
canonical one-bit final-decision bank is not prefix-stable for any nonempty input.
Thus the one-bit quotient does not refute continuation holonomy: it simply observes
too late, after the suffix has already entered the state.

## Honest scope

The theorem applies when a real trace has a certified prefix boundary through which
all future suffix behaviour factors (one-way / streaming / crossing-state access).
A general Turing machine may reread and reorganize the prefix after seeing the
suffix, so polynomial time alone does not supply `prefixStable` or `finishCorrect`.
Constructing such a continuation-complete cut, or proving an equivalent conserved
holonomy across every adaptive rereading trace, is the remaining Route G theorem.
-/

namespace PallLean.Paper93.DeepMath.PathB.ContinuationCompleteDynamicHolonomy

open PvsNPRunIndexedFaithfulTPhi
open PvsNPRunIndexedFaithfulTPhi.ActualDecisionRun
open MultiplicativeHolonomyBoundaryCapacity
open MultiplicativeHolonomyBoundaryCapacity.DynamicGeneratorBank
open DecisionGeneratorLowerBoundBarrier
open ContinuationObserver

variable {Pre Suf State : Type*}

/-- A dynamic generator boundary is prefix-stable at `time` when the signature
depends only on the prefix, not on the future suffix. -/
def PrefixStable
    (R : ActualDecisionRun (Pre × Suf) State) {g : ℕ}
    (B : DynamicGeneratorBank R g) (time : ℕ) : Prop :=
  ∀ p s t, B.signature time (p, s) = B.signature time (p, t)

/-- A continuation-complete dynamic boundary.  Its observed signature is a genuine
prefix boundary, and `finish` reconstructs the actual final decision for every
continuation. -/
structure ContinuationCompleteBank
    (R : ActualDecisionRun (Pre × Suf) State) (g : ℕ) where
  time : ℕ
  time_le : time ≤ R.steps
  bank : DynamicGeneratorBank R g
  prefixStable : PrefixStable R bank time
  finish : (Fin g → Bool) → Suf → Bool
  finishCorrect : ∀ p s, finish (bank.signature time (p, s)) s = R.finalAnswer (p, s)

namespace ContinuationCompleteBank

/-- The residual signature of a prefix, using an arbitrary reference suffix.  The
prefix-stability field makes the choice observationally irrelevant. -/
def prefixSignature [Inhabited Suf]
    {R : ActualDecisionRun (Pre × Suf) State} {g : ℕ}
    (C : ContinuationCompleteBank R g) (p : Pre) : Fin g → Bool :=
  C.bank.signature C.time (p, default)

/-- A continuation-complete trace boundary is faithful: equal prefix signatures
force equal decisions under every suffix. -/
theorem signatureFaithful [Inhabited Suf]
    {R : ActualDecisionRun (Pre × Suf) State} {g : ℕ}
    (C : ContinuationCompleteBank R g) :
    ∀ p q, C.prefixSignature p = C.prefixSignature q →
      ∀ s, R.finalAnswer (p, s) = R.finalAnswer (q, s) := by
  intro p q hsig s
  calc
    R.finalAnswer (p, s) = C.finish (C.bank.signature C.time (p, s)) s :=
      (C.finishCorrect p s).symm
    _ = C.finish (C.prefixSignature p) s := by
      rw [prefixSignature, C.prefixStable p s default]
    _ = C.finish (C.prefixSignature q) s := by rw [hsig]
    _ = C.finish (C.bank.signature C.time (q, s)) s := by
      rw [prefixSignature, C.prefixStable q s default]
    _ = R.finalAnswer (q, s) := C.finishCorrect q s

/-- Pairwise-separated prefix residuals force generator dimension.  This is the
dynamic-holonomy capacity theorem with the correct semantic unit: residual
functions, rather than final answers or raw states. -/
theorem separated_forces_generators [Inhabited Suf]
    {R : ActualDecisionRun (Pre × Suf) State} {g : ℕ}
    (C : ContinuationCompleteBank R g)
    {F : Finset Pre}
    (hsep : Separated (fun p s => R.finalAnswer (p, s)) F)
    {k : ℕ} (hmany : 2 ^ k ≤ F.card) :
    k ≤ g := by
  let encode : {p // p ∈ F} → (Fin g → Bool) :=
    fun p => C.prefixSignature p.1
  have hinj : Function.Injective encode := by
    intro p q heq
    apply Subtype.ext
    by_contra hpq
    obtain ⟨s, hs⟩ := hsep p.1 p.2 q.1 q.2 hpq
    exact hs (C.signatureFaithful p.1 q.1 heq s)
  have hcard : F.card ≤ Fintype.card (Fin g → Bool) := by
    simpa using Fintype.card_le_of_injective encode hinj
  have hpowers : 2 ^ k ≤ 2 ^ g := by
    exact le_trans hmany (by simpa using hcard)
  exact (Nat.pow_le_pow_iff_right (by omega)).mp hpowers

end ContinuationCompleteBank

/-! ## Exact equality calibration -/

/-- A zero-clock actual run for equality.  The state retains the pair solely to
make the late final-decision observer explicit. -/
def equalityRun (n : ℕ) :
    ActualDecisionRun ((Fin n → Bool) × (Fin n → Bool))
      ((Fin n → Bool) × (Fin n → Bool)) where
  encode := id
  step := fun _ state => state
  steps := 0
  observe := fun x => decide (x.1 = x.2)

@[simp] theorem equalityRun_finalAnswer (n : ℕ)
    (p s : Fin n → Bool) :
    (equalityRun n).finalAnswer (p, s) = eqDec n p s := by
  rfl

/-- Every continuation-complete dynamic boundary for `n`-bit equality needs at
least `n` Boolean holonomy generators. -/
theorem equality_forces_n_generators
    (n g : ℕ) (C : ContinuationCompleteBank (equalityRun n) g) :
    n ≤ g := by
  apply C.separated_forces_generators (F := Finset.univ) (k := n)
  · simpa only [equalityRun_finalAnswer] using eqDec_separated n
  · simp

/-- In particular, one continuation-complete generator cannot handle equality on
two or more bits. -/
theorem no_one_generator_equality {n : ℕ} (hn : 2 ≤ n) :
    ¬ Nonempty (ContinuationCompleteBank (equalityRun n) 1) := by
  rintro ⟨C⟩
  have := equality_forces_n_generators n 1 C
  omega

/-- The canonical final-answer bank is not a prefix boundary.  For any nonempty
equality input, changing only the suffix changes its observed one-bit signature.
This is the exact reason the universal one-bit decision quotient does not defeat
continuation-complete holonomy. -/
theorem finalDecisionBank_not_prefixStable {n : ℕ} (hn : 0 < n) :
    ¬ PrefixStable (equalityRun n)
      (finalDecisionBank (equalityRun n)) 0 := by
  intro hstable
  let i : Fin n := ⟨0, hn⟩
  let p : Fin n → Bool := fun _ => false
  let t : Fin n → Bool := fun j => decide (j = i)
  have hpt : p ≠ t := by
    intro h
    have hi := congrFun h i
    simp [p, t] at hi
  have h := hstable p p t
  have hcoord := congrFun h ⟨0, by omega⟩
  have htrue :
      (finalDecisionBank (equalityRun n)).signature 0 (p, p) ⟨0, by omega⟩ = true := by
    simp [DynamicGeneratorBank.signature, finalDecisionBank, equalityRun,
      ActualDecisionRun.stateAt, PvsNPNFrameDynamicMERAHolonomy.runFrom]
  have hfalse :
      (finalDecisionBank (equalityRun n)).signature 0 (p, t) ⟨0, by omega⟩ = false := by
    simp [DynamicGeneratorBank.signature, finalDecisionBank, equalityRun,
      ActualDecisionRun.stateAt, PvsNPNFrameDynamicMERAHolonomy.runFrom, hpt]
  rw [htrue, hfalse] at hcoord
  contradiction

end PallLean.Paper93.DeepMath.PathB.ContinuationCompleteDynamicHolonomy

#print axioms PallLean.Paper93.DeepMath.PathB.ContinuationCompleteDynamicHolonomy.ContinuationCompleteBank.signatureFaithful
#print axioms PallLean.Paper93.DeepMath.PathB.ContinuationCompleteDynamicHolonomy.ContinuationCompleteBank.separated_forces_generators
#print axioms PallLean.Paper93.DeepMath.PathB.ContinuationCompleteDynamicHolonomy.equality_forces_n_generators
#print axioms PallLean.Paper93.DeepMath.PathB.ContinuationCompleteDynamicHolonomy.no_one_generator_equality
#print axioms PallLean.Paper93.DeepMath.PathB.ContinuationCompleteDynamicHolonomy.finalDecisionBank_not_prefixStable
