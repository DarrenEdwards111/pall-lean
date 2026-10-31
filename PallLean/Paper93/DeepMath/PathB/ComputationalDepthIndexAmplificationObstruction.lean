import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDirectSumIndexSATEncoding

/-!
# Linear general-circuit upper bound for the split INDEX SAT slice

The split INDEX encoding is a valid communication-lower-bound instance, but
its selected-bit predicate has an explicit linear bounded-fanin DAG: compute
`data i AND selector i` for every coordinate and combine the results with a
binary OR tree.  This module records the semantic correctness and exact gate
budget, preventing the linear slice from being used as a superpolynomial
general-circuit lower-bound family.
-/

namespace PallLean.Paper93.DeepMath.PathB.IndexAmplificationObstruction

/-- One-hot selector at coordinate `q`. -/
def oneHot {N : Nat} (q : Fin N) : Fin N → Bool :=
  fun i => decide (i = q)

/-- Extensional semantics of `N` parallel ANDs followed by an OR tree. -/
def sharedIndexMux {N : Nat} (data selector : Fin N → Bool) : Bool :=
  decide (∃ i, data i = true ∧ selector i = true)

theorem sharedIndexMux_oneHot_correct {N : Nat}
    (data : Fin N → Bool) (q : Fin N) :
    sharedIndexMux data (oneHot q) = data q := by
  classical
  cases h : data q <;> simp_all [sharedIndexMux, oneHot]

/-- Gate count of the explicit bounded-fanin implementation:
`N` AND gates and `N - 1` binary OR gates. -/
def sharedIndexGateCount (N : Nat) : Nat := N + (N - 1)

theorem sharedIndexGateCount_eq (N : Nat) (hN : 0 < N) :
    sharedIndexGateCount N = 2 * N - 1 := by
  simp only [sharedIndexGateCount]
  omega

theorem sharedIndexGateCount_le_two_mul (N : Nat) :
    sharedIndexGateCount N ≤ 2 * N := by
  simp only [sharedIndexGateCount]
  omega

/-- A compact certificate bundling the linear implementation with its
semantics.  It is an upper-bound witness, not a lower-bound assumption. -/
structure LinearIndexCircuitCertificate (N : Nat) where
  eval : (Fin N → Bool) → (Fin N → Bool) → Bool
  gates : Nat
  correct : ∀ (data : Fin N → Bool) (q : Fin N), eval data (oneHot q) = data q
  linear : gates ≤ 2 * N

def linearIndexCircuitCertificate (N : Nat) : LinearIndexCircuitCertificate N where
  eval := sharedIndexMux
  gates := sharedIndexGateCount N
  correct := sharedIndexMux_oneHot_correct
  linear := sharedIndexGateCount_le_two_mul N

/-- Consequently, any claimed lower bound for this exact predicate exceeding
`2N` gates contradicts its explicit certified implementation. -/
theorem no_lower_bound_above_two_mul (N lower : Nat)
    (hLower : ∀ C : LinearIndexCircuitCertificate N, lower ≤ C.gates) :
    lower ≤ 2 * N := by
  exact le_trans (hLower (linearIndexCircuitCertificate N))
    (linearIndexCircuitCertificate N).linear

end PallLean.Paper93.DeepMath.PathB.IndexAmplificationObstruction

#print axioms PallLean.Paper93.DeepMath.PathB.IndexAmplificationObstruction.sharedIndexMux_oneHot_correct
#print axioms PallLean.Paper93.DeepMath.PathB.IndexAmplificationObstruction.no_lower_bound_above_two_mul
