import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCompleteUnitCNFSwitching

/-!
# Constructive width-two base case: variable-disjoint 2-CNF

A positive binary clause has three satisfying local assignments: `01`, `10`, and `11`.  If the clauses have disjoint
variable pairs, their local choices are independent.  Grouping three clauses at a time therefore gives `27` live
branches, whereas unrestricted search on the six variables has `64` branches and the switching-certificate budget
with one saved bit permits `32`.

This file proves the exact local count and constructs the resulting numerical switching certificate for `k` blocks
of three disjoint clauses.  It is a genuine width-two extension, but disjointness is essential; overlap is the next
structural obstacle.
-/

namespace PallLean.Paper93.DeepMath.PathB.Disjoint2CNFSwitching

open PallLean.Paper93.DeepMath.PathB.XorCNFSwitchingCashout

/-- The satisfying assignments of one positive binary clause. -/
abbrev SatisfyingPair := {p : Bool × Bool // p.1 || p.2 = true}

/-- Exactly three local states satisfy a positive binary clause. -/
theorem card_satisfyingPair : Fintype.card SatisfyingPair = 3 := by decide

/-- Independent local choices for `3*k` variable-disjoint binary clauses. -/
abbrev DisjointBranches (k : ℕ) := Fin (3 * k) → SatisfyingPair

/-- The complete residual branch family has exactly `27^k` members. -/
theorem card_disjointBranches (k : ℕ) : Fintype.card (DisjointBranches k) = 27 ^ k := by
  simp [DisjointBranches, card_satisfyingPair, pow_mul]

/-- Three disjoint width-two clauses cost `27` branches, fitting below the `32` branches allowed after saving one bit. -/
theorem disjoint_branch_bound (k : ℕ) : 27 ^ k ≤ 2 ^ (6 * k - k) := by
  rw [show 6 * k - k = 5 * k by omega, pow_mul]
  exact Nat.pow_le_pow_left (by norm_num) k

/-- Explicit switching certificate for `k` blocks of three variable-disjoint binary clauses. -/
def disjoint2CNFCertificate (k : ℕ) (hk : 1 ≤ k) : SwitchingCertificate where
  n := 6 * k
  leafCount := 27 ^ k
  targetsPerLeaf := 1
  saving := k
  npos := by omega
  savingPos := hk
  savingLe := by omega
  leafBound := disjoint_branch_bound k
  targetBound := one_le_pow₀ (by norm_num)

/-- Variable-disjoint 2-CNF obtains a strict saving over its `2^(6k)` assignment cube. -/
theorem disjoint2CNFLinearTests_beats_bruteforce (k : ℕ) (hk : 1 ≤ k) :
    switchingLinearTests (disjoint2CNFCertificate k hk) < 2 ^ (6 * k) := by
  simpa [PallLean.Paper93.DeepMath.PathB.ObserverAlgorithmic.bruteForceTime] using
    switchingLinearTests_beats_bruteforce (disjoint2CNFCertificate k hk)

end PallLean.Paper93.DeepMath.PathB.Disjoint2CNFSwitching

#print axioms PallLean.Paper93.DeepMath.PathB.Disjoint2CNFSwitching.card_satisfyingPair
#print axioms PallLean.Paper93.DeepMath.PathB.Disjoint2CNFSwitching.card_disjointBranches
#print axioms PallLean.Paper93.DeepMath.PathB.Disjoint2CNFSwitching.disjoint2CNFLinearTests_beats_bruteforce
