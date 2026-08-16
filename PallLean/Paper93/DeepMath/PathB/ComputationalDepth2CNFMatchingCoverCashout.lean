import PallLean.Paper93.DeepMath.PathB.ComputationalDepth2CNFMatchingCover

/-!
# 2-CNF matching/cover dichotomy: uniform work cash-out

Use threshold `3*k` in the matching-or-cover theorem.  If the matching is large, select `3*k` independent binary
clauses: their satisfying local assignments cost `27^k`, and all other variables may conservatively be searched.
If the matching is small, its endpoint cover has fewer than `6*k` variables; branch on that cover and solve the unit
residuals.

Provided `6*k ≤ n` and `k ≥ 1`, both arms cost at most `2^(n-1)`.  This file proves the exact arithmetic combination.
The semantic implementation of restriction and unit propagation is kept separate from this work bound.
-/

namespace PallLean.Paper93.DeepMath.PathB.TwoCNFMatchingCoverCashout

/-- Conservative work of the large-matching arm. -/
def matchingArmWork (n k : ℕ) : ℕ := 27 ^ k * 2 ^ (n - 6 * k)

/-- Conservative work of the small-cover arm (`cover.card < 6*k`). -/
def coverArmWork (k : ℕ) : ℕ := 2 ^ (6 * k - 1)

/-- Worst-case work after applying the matching-or-cover dichotomy at threshold `3*k`. -/
def combined2CNFWork (n k : ℕ) : ℕ := max (matchingArmWork n k) (coverArmWork k)

theorem twentySeven_pow_le_thirtyTwo_pow (k : ℕ) : 27 ^ k ≤ 2 ^ (5 * k) := by
  rw [pow_mul]
  exact Nat.pow_le_pow_left (by norm_num) k

/-- The independent-clause arm retains at least one full bit of surplus. -/
theorem matchingArmWork_le_half_cube (n k : ℕ) (hk : 1 ≤ k) (hkn : 6 * k ≤ n) :
    matchingArmWork n k ≤ 2 ^ (n - 1) := by
  unfold matchingArmWork
  calc
    27 ^ k * 2 ^ (n - 6 * k) ≤ 2 ^ (5 * k) * 2 ^ (n - 6 * k) :=
      Nat.mul_le_mul_right _ (twentySeven_pow_le_thirtyTwo_pow k)
    _ = 2 ^ (5 * k + (n - 6 * k)) := by rw [Nat.pow_add]
    _ = 2 ^ (n - k) := by congr 1 <;> omega
    _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- Branching on the small cover also retains at least one full bit of surplus. -/
theorem coverArmWork_le_half_cube (n k : ℕ) (hk : 1 ≤ k) (hkn : 6 * k ≤ n) :
    coverArmWork k ≤ 2 ^ (n - 1) := by
  unfold coverArmWork
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **Uniform matching/cover cash-out (proved): either structural arm stays below half the cube.** -/
theorem combined2CNFWork_le_half_cube (n k : ℕ) (hk : 1 ≤ k) (hkn : 6 * k ≤ n) :
    combined2CNFWork n k ≤ 2 ^ (n - 1) := by
  rw [combined2CNFWork, max_le_iff]
  exact ⟨matchingArmWork_le_half_cube n k hk hkn, coverArmWork_le_half_cube n k hk hkn⟩

/-- Hence the combined accounting is strictly below brute-force assignment search. -/
theorem combined2CNFWork_lt_cube (n k : ℕ) (hk : 1 ≤ k) (hkn : 6 * k ≤ n) :
    combined2CNFWork n k < 2 ^ n := by
  exact lt_of_le_of_lt (combined2CNFWork_le_half_cube n k hk hkn)
    (Nat.pow_lt_pow_right (by norm_num) (by omega))

end PallLean.Paper93.DeepMath.PathB.TwoCNFMatchingCoverCashout

#print axioms PallLean.Paper93.DeepMath.PathB.TwoCNFMatchingCoverCashout.matchingArmWork_le_half_cube
#print axioms PallLean.Paper93.DeepMath.PathB.TwoCNFMatchingCoverCashout.combined2CNFWork_lt_cube
