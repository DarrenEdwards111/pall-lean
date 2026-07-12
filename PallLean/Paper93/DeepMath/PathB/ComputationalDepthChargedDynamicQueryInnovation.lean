import PallLean.Paper93.DeepMath.PathB.ComputationalDepthChargedContinuationQuotient

/-!
# Dynamic continuation-profile innovation

Raw continuation-quotient cardinality fails `PUpper`: equality already has `2^n` query profiles.  The dynamic
candidate instead counts only profile **changes along the actual charged trace**.

For a continuation semantics `S`, `profileInnovation S a` counts times `t < clock(n)` at which the complete
query profile at `(a,t)` differs from the profile at `(a,t+1)`.  Its worst-case length-`n` value is
`dynamicQueryResource`.

The central upper theorem is unconditional:

`dynamicQueryResource_le_clock`.

Hence every polynomial-time charged machine has polynomial dynamic query innovation for every query scheme
(`dynamicQueryResource_polyBounded`).  This includes equality and parity without needing their static profile
sets to be small.

The equality contrast is made explicit: `eqTraceProfile` ignores time, so it has `2^n` distinct static profiles
but zero dynamic innovation.  Thus dynamic change avoids the residual-rank false positive.

## Honest scope

The all-`P` upper side of the repaired dynamic measure.  A useful SAT lower bound still needs a canonical/rich
query scheme and a theorem that SAT forces super-polynomial cumulative profile innovation.  Neither is proved
here.
-/

namespace PallLean.Paper93.DeepMath.PathB.ChargedDynamicQueryInnovation

open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant (PolyBounded)
open PallLean.Paper93.DeepMath.PathB.ChargedHolographicMachine
open PallLean.Paper93.DeepMath.PathB.ChargedLengthObserver
open PallLean.Paper93.DeepMath.PathB.ChargedContinuationQuotient

/-- Embed a time `t < clock(n)` in the bounded observer time type. -/
def timePoint {M : ChargedMachine} {n : Nat} (a : Fin n → Bool) (t : Fin (M.clock n)) :
    ReachablePoint M n :=
  ⟨a, ⟨t.val, by omega⟩⟩

/-- The immediately following bounded execution point. -/
def succTimePoint {M : ChargedMachine} {n : Nat} (a : Fin n → Bool) (t : Fin (M.clock n)) :
    ReachablePoint M n :=
  ⟨a, ⟨t.val + 1, by omega⟩⟩

/-- Cumulative query-profile innovation on one charged run. -/
def profileInnovation {M : ChargedMachine} {n : Nat} (S : ContinuationSemantics M n)
    (a : Fin n → Bool) : Nat :=
  ∑ t : Fin (M.clock n),
    if profile S (timePoint a t) ≠ profile S (succTimePoint a t) then 1 else 0

/-- At most one profile-change unit is charged per actual machine transition. -/
theorem profileInnovation_le_clock {M : ChargedMachine} {n : Nat} (S : ContinuationSemantics M n)
    (a : Fin n → Bool) :
    profileInnovation S a ≤ M.clock n := by
  unfold profileInnovation
  calc
    (∑ t : Fin (M.clock n),
      if profile S (timePoint a t) ≠ profile S (succTimePoint a t) then 1 else 0)
        ≤ ∑ _t : Fin (M.clock n), 1 := by
          apply Finset.sum_le_sum
          intro t _
          split <;> omega
    _ = M.clock n := by simp

/-- Worst-case dynamic query innovation at one input length. -/
def dynamicQueryResource {M : ChargedMachine} {n : Nat} (S : ContinuationSemantics M n) : Nat :=
  (Finset.univ : Finset (Fin n → Bool)).sup (profileInnovation S)

theorem dynamicQueryResource_le_clock {M : ChargedMachine} {n : Nat}
    (S : ContinuationSemantics M n) :
    dynamicQueryResource S ≤ M.clock n := by
  apply Finset.sup_le
  intro a _
  exact profileInnovation_le_clock S a

/-- A length-indexed continuation/query scheme for one charged machine. -/
abbrev QueryScheme (M : ChargedMachine) := ∀ n, ContinuationSemantics M n

/-- Dynamic resource of a query scheme. -/
def schemeResource {M : ChargedMachine} (S : QueryScheme M) (n : Nat) : Nat :=
  dynamicQueryResource (S n)

/-- **All-P upper theorem.** Every polynomial-time charged machine has polynomial cumulative query-profile
innovation for every continuation/query scheme, regardless of static quotient size. -/
theorem dynamicQueryResource_polyBounded {M : ChargedMachine} (S : QueryScheme M)
    (hM : IsPolyTime M) : PolyBounded (schemeResource S) := by
  obtain ⟨c, k, hclock⟩ := hM
  exact ⟨c, k, fun n => (dynamicQueryResource_le_clock (S n)).trans (hclock n)⟩

/-! ## Equality contrast: exponential static profiles, zero dynamic innovation -/

/-- Lift the equality profile to bounded execution points; it is deliberately independent of time. -/
def eqTraceProfile {M : ChargedMachine} {n : Nat} (p : ReachablePoint M n) :
    (Fin n → Bool) → Bool :=
  eqProfile p.input

theorem eqTraceProfile_time_invariant {M : ChargedMachine} {n : Nat}
    (a : Fin n → Bool) (t : Fin (M.clock n)) :
    eqTraceProfile (timePoint a t) = eqTraceProfile (succTimePoint a t) :=
  rfl

/-- Although equality has exponentially many static profiles, its profile changes zero times along every
trace when the input is fixed. -/
theorem eqTrace_dynamic_zero {M : ChargedMachine} {n : Nat} (a : Fin n → Bool) :
    (∑ t : Fin (M.clock n),
      if eqTraceProfile (timePoint a t) ≠ eqTraceProfile (succTimePoint a t) then 1 else 0) = 0 := by
  simp [eqTraceProfile_time_invariant]

/-- Static and dynamic complexity separate on the equality profile: static quotient `2^n`, dynamic change `0`. -/
theorem equality_static_exponential_dynamic_zero (M : ChargedMachine) (n : Nat) :
    Nat.card (Set.range (@eqProfile n)) = 2 ^ n ∧
      ∀ a : Fin n → Bool,
        (∑ t : Fin (M.clock n),
          if eqTraceProfile (timePoint a t) ≠ eqTraceProfile (succTimePoint a t) then 1 else 0) = 0 :=
  ⟨eqProfile_rank n, fun a => eqTrace_dynamic_zero a⟩

end PallLean.Paper93.DeepMath.PathB.ChargedDynamicQueryInnovation

#print axioms PallLean.Paper93.DeepMath.PathB.ChargedDynamicQueryInnovation.profileInnovation_le_clock
#print axioms PallLean.Paper93.DeepMath.PathB.ChargedDynamicQueryInnovation.dynamicQueryResource_polyBounded
#print axioms PallLean.Paper93.DeepMath.PathB.ChargedDynamicQueryInnovation.eqTrace_dynamic_zero
#print axioms PallLean.Paper93.DeepMath.PathB.ChargedDynamicQueryInnovation.equality_static_exponential_dynamic_zero
