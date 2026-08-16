import PallLean.Paper93.DeepMath.PathB.ComputationalDepthFanoutAwareIncidencePotential

/-!
# Normalized separator ownership: exact laws and the zero-surplus obstruction

Raw live-incidence credit handles a wide `MOD` gate but can be as large as `#gates · #live`.  The natural
normalization is to charge each live variable once whenever at least one represented gate uses it.  This file carries
out the first three route-selected tasks:

1. define the normalized, separator-owned credit and prove it is at most `#live`;
2. prove restriction monotonicity and shared-gate/fanout neutrality;
3. stress-test wide parity, complete overlap, and arbitrary fully-covered support families (which include the support
   patterns of equality, multiplexers, and expander incidence).

The candidate passes all boundedness and monotonicity tests, but the final theorem exposes a decisive obstruction:
when every remaining variable is covered, fixing `k` variables reduces credit by exactly `k`, while creating `2^k`
binary branches.  Hence `2^k · 2^(n-k) = 2^n`: the potential has **zero surplus** and gives no SAT speedup by itself.

This identifies the next invariant requirement precisely.  A successful potential needs either super-unit expected
simplification (one queried bit destroys more than one unit of residual boundary), or separator factorization that
reduces the number of branches actually explored.  Merely normalizing incidence ownership cannot close the route.
-/

namespace PallLean.Paper93.DeepMath.PathB.NormalizedSeparatorPotential

open Finset

variable {Gate Var : Type} [DecidableEq Gate] [DecidableEq Var]

/-- Variables touched by at least one represented shared gate. -/
def coveredVars (gates : Finset Gate) (support : Gate → Finset Var) : Finset Var :=
  gates.biUnion support

/-- Separator-owned credit: each live variable is charged at most once, independent of its gate degree. -/
def normalizedCredit (gates : Finset Gate) (support : Gate → Finset Var) (live : Finset Var) : ℕ :=
  (live ∩ coveredVars gates support).card

/-- **Budget bound (proved).**  Normalization caps total credit by the live-variable budget. -/
theorem normalizedCredit_le_live_card (gates : Finset Gate) (support : Gate → Finset Var)
    (live : Finset Var) :
    normalizedCredit gates support live ≤ live.card := by
  exact card_le_card inter_subset_left

/-- Restricting the live set cannot increase normalized credit. -/
theorem normalizedCredit_mono_live (gates : Finset Gate) (support : Gate → Finset Var)
    {live' live : Finset Var} (hsub : live' ⊆ live) :
    normalizedCredit gates support live' ≤ normalizedCredit gates support live := by
  unfold normalizedCredit
  apply card_le_card
  exact inter_subset_inter hsub (Subset.rfl)

/-- A shared gate already owned by the gate set cannot be charged again. -/
theorem insert_owned_gate_neutral (gates : Finset Gate) (support : Gate → Finset Var)
    (live : Finset Var) (g : Gate) (hg : g ∈ gates) :
    normalizedCredit (insert g gates) support live = normalizedCredit gates support live := by
  rw [insert_eq_self.mpr hg]

/-- When every live variable is represented, normalized credit is exactly the number of live variables. -/
theorem normalizedCredit_eq_live_card_of_covered (gates : Finset Gate) (support : Gate → Finset Var)
    (live : Finset Var) (hcovered : live ⊆ coveredVars gates support) :
    normalizedCredit gates support live = live.card := by
  simp [normalizedCredit, inter_eq_left.mpr hcovered]

/-- Wide-parity/MOD stress test: one wide gate receives exactly one unit per live variable. -/
theorem single_wide_gate_credit (support : Gate → Finset Var) (live : Finset Var) (g : Gate)
    (hwide : live ⊆ support g) :
    normalizedCredit {g} support live = live.card := by
  apply normalizedCredit_eq_live_card_of_covered
  intro v hv
  simp [coveredVars, hv, hwide hv]

/-- Complete-overlap/expander stress test: arbitrarily many duplicate wide supports still receive only `#live`
credit, eliminating the raw `#gates · #live` blow-up. -/
theorem complete_overlap_credit (gates : Finset Gate) (support : Gate → Finset Var)
    (live : Finset Var) (hne : gates.Nonempty) (hwide : ∀ g ∈ gates, live ⊆ support g) :
    normalizedCredit gates support live = live.card := by
  apply normalizedCredit_eq_live_card_of_covered
  obtain ⟨g, hg⟩ := hne
  intro v hv
  simp only [coveredVars, mem_biUnion]
  exact ⟨g, hg, hwide g hg hv⟩

/-- **Exact one-step payment under full coverage.**  Deleting a covered live variable reduces normalized credit by
one—no more and no less. -/
theorem erase_credit_add_one (gates : Finset Gate) (support : Gate → Finset Var)
    (live : Finset Var) (v : Var) (hcovered : live ⊆ coveredVars gates support) (hv : v ∈ live) :
    normalizedCredit gates support (live.erase v) + 1
      = normalizedCredit gates support live := by
  rw [normalizedCredit_eq_live_card_of_covered gates support live hcovered]
  rw [normalizedCredit_eq_live_card_of_covered gates support (live.erase v)
    (Subset.trans (erase_subset _ _) hcovered)]
  rw [card_erase_of_mem hv]
  have hpos : 0 < live.card := card_pos.mpr ⟨v, hv⟩
  omega

/-- **Zero-surplus obstruction (exponent form).**  If branching fixes `fixed` variables and normalized residual
credit is merely the number `n-fixed` of remaining covered variables, the total exponent is still exactly `n`. -/
theorem normalized_payment_has_zero_surplus {n fixed residualCredit : ℕ}
    (hfixed : fixed ≤ n) (hcredit : residualCredit = n - fixed) :
    fixed + residualCredit = n := by
  omega

/-- **Zero-surplus obstruction (work form).**  Binary branching paid one-for-one by normalized credit gives exactly
brute-force work, not a strict improvement. -/
theorem normalized_branching_work_eq_bruteforce {n fixed residualCredit : ℕ}
    (hfixed : fixed ≤ n) (hcredit : residualCredit = n - fixed) :
    2 ^ fixed * 2 ^ residualCredit = 2 ^ n := by
  rw [← Nat.pow_add, normalized_payment_has_zero_surplus hfixed hcredit]

end PallLean.Paper93.DeepMath.PathB.NormalizedSeparatorPotential

#print axioms PallLean.Paper93.DeepMath.PathB.NormalizedSeparatorPotential.normalizedCredit_le_live_card
#print axioms PallLean.Paper93.DeepMath.PathB.NormalizedSeparatorPotential.erase_credit_add_one
#print axioms PallLean.Paper93.DeepMath.PathB.NormalizedSeparatorPotential.normalized_branching_work_eq_bruteforce
