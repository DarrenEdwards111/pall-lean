import PallLean.Paper93.DeepMath.PathB.ComputationalDepthXorCNFIdentityEmbedding
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthObserverRestrictionDecomposition

/-!
# XOR-CNF switching certificate: exact SAT cash-out

The identity embedding shows that the missing XOR-CNF step is a genuine CNF restriction/switching theorem.  This file
formalizes exactly what such a theorem must output.  A restriction tree has few leaves, and every leaf is represented
as an explicit XOR-DNF target list.  The preceding coset-collapse theorem solves each target by one span-membership
test.

If the leaf exponent and target-list exponent sum to at most `n-1`, the total number of linear tests is below `2^n`.
No switching theorem is assumed or smuggled in here: only the arithmetic cash-out of a supplied certificate is proved.
-/

namespace PallLean.Paper93.DeepMath.PathB.XorCNFSwitchingCashout

open PallLean.Paper93.DeepMath.PathB.ObserverAlgorithmic

/-- Numerical output required from an XOR-CNF-to-XOR-DNF restriction/switching theorem. -/
structure SwitchingCertificate where
  n : ℕ
  leafCount : ℕ
  targetsPerLeaf : ℕ
  saving : ℕ
  npos : 1 ≤ n
  savingPos : 1 ≤ saving
  savingLe : saving ≤ n
  leafBound : leafCount ≤ 2 ^ (n - saving)
  targetBound : targetsPerLeaf ≤ 2 ^ (saving - 1)

/-- Total span-membership tests: one per explicit target at every restriction leaf. -/
def switchingLinearTests (C : SwitchingCertificate) : ℕ := C.leafCount * C.targetsPerLeaf

theorem switching_exponent_budget_eq (C : SwitchingCertificate) :
    (C.n - C.saving) + (C.saving - 1) = C.n - 1 := by
  have hs := C.savingLe
  have hp := C.savingPos
  omega

/-- **Switching-certificate cash-out (proved): at most half-cube many linear tests.** -/
theorem switchingLinearTests_le_half_cube (C : SwitchingCertificate) :
    switchingLinearTests C ≤ 2 ^ (C.n - 1) := by
  unfold switchingLinearTests
  calc
    C.leafCount * C.targetsPerLeaf
        ≤ 2 ^ (C.n - C.saving) * C.targetsPerLeaf := Nat.mul_le_mul_right _ C.leafBound
    _ ≤ 2 ^ (C.n - C.saving) * 2 ^ (C.saving - 1) := Nat.mul_le_mul_left _ C.targetBound
    _ = 2 ^ ((C.n - C.saving) + (C.saving - 1)) := by rw [Nat.pow_add]
    _ = 2 ^ (C.n - 1) := by rw [switching_exponent_budget_eq C]

/-- Any valid switching certificate yields strictly fewer linear tests than brute-force assignments. -/
theorem switchingLinearTests_beats_bruteforce (C : SwitchingCertificate) :
    switchingLinearTests C < bruteForceTime C.n := by
  unfold bruteForceTime
  have hn := C.npos
  exact lt_of_le_of_lt (switchingLinearTests_le_half_cube C)
    (Nat.pow_lt_pow_right (by norm_num) (by omega))

end PallLean.Paper93.DeepMath.PathB.XorCNFSwitchingCashout

#print axioms PallLean.Paper93.DeepMath.PathB.XorCNFSwitchingCashout.switchingLinearTests_le_half_cube
#print axioms PallLean.Paper93.DeepMath.PathB.XorCNFSwitchingCashout.switchingLinearTests_beats_bruteforce
