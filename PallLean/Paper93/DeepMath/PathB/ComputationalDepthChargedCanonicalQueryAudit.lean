import PallLean.Paper93.DeepMath.PathB.ComputationalDepthChargedDynamicQueryInnovation

/-!
# Canonical rich-query audit

The maximally canonical finite query family at input length `n` consists of every Boolean predicate on the
finite bounded-run carrier `ReachablePoint M n`.  Its response to query `q` at point `p` is simply `q p`.
This scheme is decision-sufficient, causal, and separates every pair of distinct bounded execution points, so
it cannot collapse to the final answer bit.

The audit also identifies its exact cost.  Because the carrier includes charged time, consecutive trace points
are always distinct before the clock boundary.  Hence the complete query profile changes at every charged
step: canonical dynamic query innovation is exactly the machine clock.  In particular, clock padding changes
the resource even when the decided language is unchanged.

Thus maximal canonical richness is a valid no-collapse query scheme, but not a new lower-bound mechanism: its
SAT lower bound is precisely a charged-time lower bound.  A simulation-invariant refinement would have to
quotient harmless padding while retaining enough continuation structure to avoid the final-bit collapse.
-/

namespace PallLean.Paper93.DeepMath.PathB.ChargedCanonicalQueryAudit

open PallLean.Paper93.DeepMath.PathB.ChargedHolographicMachine
open PallLean.Paper93.DeepMath.PathB.ChargedLengthObserver
open PallLean.Paper93.DeepMath.PathB.ChargedContinuationQuotient
open PallLean.Paper93.DeepMath.PathB.ChargedDynamicQueryInnovation

/-- The canonical rich scheme asks every Boolean predicate on the finite bounded execution carrier. -/
noncomputable def canonicalRichSemantics (M : ChargedMachine) (n : Nat) :
    ContinuationSemantics M n where
  Query := ReachablePoint M n → Bool
  queryFintype := inferInstance
  queryDecEq := Classical.decEq _
  response := fun p q => q p
  outputQuery := fun p => M.accept (boundary p).state
  output_correct := final_output_correct M
  next_respects := by
    intro p q h
    have hpq : p = q := by
      have htest := congrFun h (fun r => decide (r = p))
      change decide (p = p) = decide (q = p) at htest
      have : q = p := by simpa using htest.symm
      exact this.symm
    subst q
    rfl

/-- Full predicate profiles separate all bounded execution points. -/
theorem canonical_profile_injective (M : ChargedMachine) (n : Nat) :
    Function.Injective (profile (canonicalRichSemantics M n)) := by
  intro p q h
  have htest := congrFun h (fun r => decide (r = p))
  change decide (p = p) = decide (q = p) at htest
  have : q = p := by simpa using htest.symm
  exact this.symm

/-- Before the clock boundary, the next bounded point is genuinely different because its charged time grows. -/
theorem timePoint_ne_succTimePoint {M : ChargedMachine} {n : Nat}
    (a : Fin n → Bool) (t : Fin (M.clock n)) :
    timePoint a t ≠ succTimePoint a t := by
  intro h
  have ht := congrArg (fun p : ReachablePoint M n => p.time.val) h
  change t.val = t.val + 1 at ht
  omega

/-- Consequently every charged step changes the canonical complete query profile. -/
theorem canonical_profile_changes {M : ChargedMachine} {n : Nat}
    (a : Fin n → Bool) (t : Fin (M.clock n)) :
    profile (canonicalRichSemantics M n) (timePoint a t) ≠
      profile (canonicalRichSemantics M n) (succTimePoint a t) := by
  exact fun h => timePoint_ne_succTimePoint a t
    (canonical_profile_injective M n h)

/-- On every input, maximal rich-query innovation is exactly the charged clock. -/
theorem canonical_profileInnovation_eq_clock (M : ChargedMachine) {n : Nat}
    (a : Fin n → Bool) :
    profileInnovation (canonicalRichSemantics M n) a = M.clock n := by
  unfold profileInnovation
  calc
    (∑ t : Fin (M.clock n),
      if profile (canonicalRichSemantics M n) (timePoint a t) ≠
        profile (canonicalRichSemantics M n) (succTimePoint a t) then 1 else 0) =
        ∑ _t : Fin (M.clock n), 1 := by
          apply Finset.sum_congr rfl
          intro t _
          rw [if_pos (canonical_profile_changes a t)]
    _ = M.clock n := by simp

/-- Its worst-case length resource is therefore exactly the clock as well. -/
theorem canonical_dynamicQueryResource_eq_clock (M : ChargedMachine) (n : Nat) :
    dynamicQueryResource (canonicalRichSemantics M n) = M.clock n := by
  apply Nat.le_antisymm
  · exact dynamicQueryResource_le_clock _
  · let a : Fin n → Bool := fun _ => false
    calc
      M.clock n = profileInnovation (canonicalRichSemantics M n) a :=
        (canonical_profileInnovation_eq_clock M a).symm
      _ ≤ dynamicQueryResource (canonicalRichSemantics M n) := by
        unfold dynamicQueryResource
        exact Finset.le_sup (Finset.mem_univ a)

/-- The canonical rich query scheme for every input length. -/
noncomputable def canonicalRichScheme (M : ChargedMachine) : QueryScheme M :=
  fun n => canonicalRichSemantics M n

/-- The scheme resource is extensionally the charged clock. -/
theorem canonical_schemeResource_eq_clock (M : ChargedMachine) :
    schemeResource (canonicalRichScheme M) = M.clock := by
  funext n
  exact canonical_dynamicQueryResource_eq_clock M n

end PallLean.Paper93.DeepMath.PathB.ChargedCanonicalQueryAudit

#print axioms PallLean.Paper93.DeepMath.PathB.ChargedCanonicalQueryAudit.canonical_profile_injective
#print axioms PallLean.Paper93.DeepMath.PathB.ChargedCanonicalQueryAudit.canonical_profileInnovation_eq_clock
#print axioms PallLean.Paper93.DeepMath.PathB.ChargedCanonicalQueryAudit.canonical_dynamicQueryResource_eq_clock
#print axioms PallLean.Paper93.DeepMath.PathB.ChargedCanonicalQueryAudit.canonical_schemeResource_eq_clock
