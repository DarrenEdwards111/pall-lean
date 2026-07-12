import PallLean.Paper93.DeepMath.PathB.ComputationalDepthChargedLengthObserverCollapse
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthResidualInvariantNoGo

/-!
# Continuation/query sufficiency and the intrinsic observer quotient

Final-output sufficiency collapses every computation to a zero-innovation Boolean observer.  This file replaces
it by a query family.  A boundary point's observable meaning is its full response profile

`profile p : Query → Bool`.

Two points are observationally equivalent exactly when these profiles are equal.  The intrinsic quotient is
the finite range of `profile`, and `queryRank` is its cardinality.  `next_respects` is the load-bearing causal
condition: equivalent points remain equivalent after observer advancement, so `nextPoint` descends to the
quotient.

The construction blocks the two-state decision quotient whenever a query distinguishes two points with the
same final answer.  But the equality stress test proves the opposite danger: with the full suffix/equality query
family, the quotient already has `2^n` classes.  This recovers the earlier residual-rank no-go in the new query
language.

Therefore the query semantics is now the exact research socket: it must be rich enough to prevent final-bit
collapse but selective enough that all polynomial-time computations retain polynomial dynamic cost.  Neither
extreme works automatically.

## Honest scope

A concrete intrinsic quotient and a machine-checked equality stress test.  No all-`P` invariant and no SAT
lower bound are supplied.
-/

namespace PallLean.Paper93.DeepMath.PathB.ChargedContinuationQuotient

open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant (PolyBounded)
open PallLean.Paper93.DeepMath.PathB.ChargedHolographicMachine
open PallLean.Paper93.DeepMath.PathB.ChargedLengthObserver
open PallLean.Paper93.DeepMath.PathB.ResidualInvariantNoGo

/-- A finite family of admissible continuation queries on length-`n` bounded runs.  The distinguished output
query recovers the actual terminal decision, while `next_respects` makes observational equivalence causal. -/
structure ContinuationSemantics (M : ChargedMachine) (n : Nat) where
  Query : Type
  queryFintype : Fintype Query
  queryDecEq : DecidableEq Query
  response : ReachablePoint M n → Query → Bool
  outputQuery : Query
  output_correct : ∀ a,
    response (finalPoint M a) outputQuery = ChargedHolographicMachine.decide M (List.ofFn a)
  next_respects : ∀ p q,
    response p = response q → response (nextPoint p) = response (nextPoint q)

attribute [instance] ContinuationSemantics.queryFintype ContinuationSemantics.queryDecEq

/-- The full continuation-response profile of a boundary point. -/
def profile {M : ChargedMachine} {n : Nat} (S : ContinuationSemantics M n)
    (p : ReachablePoint M n) : S.Query → Bool :=
  S.response p

/-- Intrinsic observational equivalence: no admissible query distinguishes the points. -/
def ObsEq {M : ChargedMachine} {n : Nat} (S : ContinuationSemantics M n)
    (p q : ReachablePoint M n) : Prop :=
  profile S p = profile S q

theorem obsEq_equivalence {M : ChargedMachine} {n : Nat} (S : ContinuationSemantics M n) :
    Equivalence (ObsEq S) :=
  ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- Causal compatibility: observer advancement descends to observational equivalence classes. -/
theorem obsEq_next {M : ChargedMachine} {n : Nat} (S : ContinuationSemantics M n)
    {p q : ReachablePoint M n} (h : ObsEq S p q) :
    ObsEq S (nextPoint p) (nextPoint q) :=
  S.next_respects p q h

/-- The intrinsic quotient represented extensionally as the finite set of realised query profiles. -/
abbrev ProfileQuotient {M : ChargedMachine} {n : Nat} (S : ContinuationSemantics M n) :=
  Set.range (profile S)

/-- Cardinality of the intrinsic continuation quotient. -/
noncomputable def queryRank {M : ChargedMachine} {n : Nat} (S : ContinuationSemantics M n) : Nat :=
  Nat.card (ProfileQuotient S)

/-- Equal profiles are exactly equal points of the extensional quotient map. -/
theorem quotient_eq_iff_obsEq {M : ChargedMachine} {n : Nat} (S : ContinuationSemantics M n)
    (p q : ReachablePoint M n) :
    profile S p = profile S q ↔ ObsEq S p q :=
  Iff.rfl

/-- A distinguishing query prevents the final-answer collapse: points separated by one query occupy distinct
intrinsic quotient classes. -/
theorem profile_ne_of_query {M : ChargedMachine} {n : Nat} (S : ContinuationSemantics M n)
    (p q : ReachablePoint M n) (u : S.Query) (h : S.response p u ≠ S.response q u) :
    profile S p ≠ profile S q := by
  intro hp
  exact h (congrFun hp u)

/-! ## Equality stress test: full continuation profiles are exponential -/

/-- Equality-query profile: query `b` asks whether the stored prefix/input `a` equals `b`. -/
def eqProfile {n : Nat} (a : Fin n → Bool) : (Fin n → Bool) → Bool :=
  fun b => decide (a = b)

theorem eqProfile_injective (n : Nat) : Function.Injective (@eqProfile n) := by
  intro a b h
  have hc := congrFun h a
  simp only [eqProfile] at hc
  have hb : decide (b = a) = true := by simpa using hc.symm
  exact (of_decide_eq_true hb).symm

/-- The full equality continuation quotient has one class per input. -/
theorem eqProfile_rank (n : Nat) :
    Nat.card (Set.range (@eqProfile n)) = 2 ^ n := by
  rw [Nat.card_range_of_injective (eqProfile_injective n), Nat.card_eq_fintype_card,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- Consequently the full equality-query quotient size is not polynomially bounded. -/
theorem eqProfile_not_polyBounded :
    ¬ PolyBounded (fun n => Nat.card (Set.range (@eqProfile n))) := by
  have heq : (fun n => Nat.card (Set.range (@eqProfile n))) = fun n => 2 ^ n := by
    funext n
    exact eqProfile_rank n
  rw [heq]
  exact two_pow_not_polyBounded

end PallLean.Paper93.DeepMath.PathB.ChargedContinuationQuotient

#print axioms PallLean.Paper93.DeepMath.PathB.ChargedContinuationQuotient.obsEq_next
#print axioms PallLean.Paper93.DeepMath.PathB.ChargedContinuationQuotient.profile_ne_of_query
#print axioms PallLean.Paper93.DeepMath.PathB.ChargedContinuationQuotient.eqProfile_rank
#print axioms PallLean.Paper93.DeepMath.PathB.ChargedContinuationQuotient.eqProfile_not_polyBounded
