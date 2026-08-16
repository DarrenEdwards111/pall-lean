import PallLean.Paper93.DeepMath.PathB.ComputationalDepth3CNFMatchingCoverAccounting
import PallLean.Paper93.DeepMath.PathB.ComputationalDepth2CNFPipelineCapstone

/-!
# Width-three cover branches composed with the residual 2-CNF solver

The width-three matching/cover lemma leaves a 2-CNF instance after assigning the cover.  This file performs the
previously omitted composition with the verified width-two work bound.

The exact exponent law is diagnostic: `2^c` cover branches followed by residual work `2^(n-c-s)` cost exactly
`2^(n-s)`.  Branching pays precisely for the variables it removes and creates no new saving by itself.  Consequently,
the presently verified one-bit 2-CNF cash-out gives a one-bit composed saving, but recursive invocation alone does not
amplify it.  Any stronger result needs either a quantitatively stronger residual solver or reuse across cover branches.
-/

namespace PallLean.Paper93.DeepMath.PathB.ThreeCNFRecursiveCoverAccounting

open PallLean.Paper93.DeepMath.PathB.TwoCNFMatchingCoverCashout

/-- Abstract cover-branch work when the residual solver saves `s` exponent bits. -/
def exponentModelWork (n c s : ℕ) : ℕ := 2 ^ c * 2 ^ (n - c - s)

/-- **Exact composition law:** cover branching preserves, but does not amplify, residual exponent saving. -/
theorem exponentModelWork_eq (n c s : ℕ) (hcs : c + s ≤ n) :
    exponentModelWork n c s = 2 ^ (n - s) := by
  unfold exponentModelWork
  rw [← Nat.pow_add]
  congr 1
  omega

/-- With no residual saving, cover branching returns exactly exhaustive-search work. -/
theorem exponentModelWork_zero_saving (n c : ℕ) (hc : c ≤ n) :
    exponentModelWork n c 0 = 2 ^ n := by
  simpa using exponentModelWork_eq n c 0 (by omega)

/-- A one-bit residual saving remains exactly one bit after cover branching. -/
theorem exponentModelWork_one_saving (n c : ℕ) (hc : c + 1 ≤ n) :
    exponentModelWork n c 1 = 2 ^ (n - 1) := exponentModelWork_eq n c 1 hc

/-- Actual composed work using the verified width-two matching/cover solver at every width-three cover leaf. -/
def recursiveCoverWork (n c k : ℕ) : ℕ :=
  2 ^ c * combined2CNFWork (n - c) k

/-- The verified 2-CNF half-cube bound composes through all cover branches. -/
theorem recursiveCoverWork_le_half_cube
    (n c k : ℕ) (hk : 1 ≤ k) (hfit : 6 * k ≤ n - c) :
    recursiveCoverWork n c k ≤ 2 ^ (n - 1) := by
  unfold recursiveCoverWork
  calc
    2 ^ c * combined2CNFWork (n - c) k ≤ 2 ^ c * 2 ^ (n - c - 1) :=
      Nat.mul_le_mul_left _ (combined2CNFWork_le_half_cube (n - c) k hk hfit)
    _ = 2 ^ (c + (n - c - 1)) := by rw [Nat.pow_add]
    _ = 2 ^ (n - 1) := by congr 1 <;> omega

/-- Hence the fully composed cover arm remains strictly below the original assignment cube. -/
theorem recursiveCoverWork_lt_cube
    (n c k : ℕ) (hk : 1 ≤ k) (hfit : 6 * k ≤ n - c) :
    recursiveCoverWork n c k < 2 ^ n := by
  exact lt_of_le_of_lt (recursiveCoverWork_le_half_cube n c k hk hfit)
    (Nat.pow_lt_pow_right (by norm_num) (by omega))

end PallLean.Paper93.DeepMath.PathB.ThreeCNFRecursiveCoverAccounting

#print axioms PallLean.Paper93.DeepMath.PathB.ThreeCNFRecursiveCoverAccounting.exponentModelWork_eq
#print axioms PallLean.Paper93.DeepMath.PathB.ThreeCNFRecursiveCoverAccounting.exponentModelWork_zero_saving
#print axioms PallLean.Paper93.DeepMath.PathB.ThreeCNFRecursiveCoverAccounting.recursiveCoverWork_lt_cube
