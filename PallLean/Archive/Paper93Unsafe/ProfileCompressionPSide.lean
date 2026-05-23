/-
  Archive/Paper93Unsafe/ProfileCompressionPSide.lean

  UNSAFE — NOT part of the consistent default build target.

  The two UNCONDITIONAL ProfileCompression bounds that route through the false
  `spdp_profile_generators` axiom (via the archived
  `SymmetricPowerBound.profile_compression_rank_bound`):

    * `profile_compression_rank_bound` : SPDP rank ≤ totalProfileBound n
    * `p_side_rank_bound_for_cook_levin` : SPDP rank ≤ n^200   (FALSE)

  KEPT LIVE in ProfileCompression (NOT here): all the conditional
  `p_side_rank_bound_for_cook_levin_of_*` siblings, which take an explicit
  within-profile / template-collapse hypothesis and do NOT use the axiom.
-/
import PallLean.ProfileCompression
import PallLean.Archive.Paper93Unsafe.ProfileCompressionRankBound

namespace ProfileCompression

open SPDP MultilinearSPDP MvPolynomial TuringMachine PaperFaithfulSeparation

/-- Profile compression rank bound (archived; uses the false axiom). -/
theorem profile_compression_rank_bound (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    mlBlockedSpdpRank
      (cook_levin_compilation M n hn htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (compiledPoly (cook_levin_compilation M n hn htb hns)) ≤ totalProfileBound n := by
  have h := SymmetricPowerBound.profile_compression_rank_bound M n hn htb hns
  have heq : totalProfileBound n = (3 * Nat.log 2 n + 1) ^ 12 := totalProfileBound_eq n
  rw [heq]
  calc mlBlockedSpdpRank
        (cook_levin_compilation M n hn htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (compiledPoly (cook_levin_compilation M n hn htb hns))
      ≤ (3 * Nat.log 2 n + 1) ^ 12 := h
    _ = (3 * Nat.log 2 n + 1) ^ 12 := rfl

/-- FALSE unconditional P-side bound `SPDP rank ≤ n^200` (archived).
Refuted by the NP-side identity minor on the same compiled object. -/
theorem p_side_rank_bound_for_cook_levin (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    mlBlockedSpdpRank (cook_levin_compilation M n hn htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (compiledPoly (cook_levin_compilation M n hn htb hns)) ≤ n ^ 200 := by
  calc mlBlockedSpdpRank
        (cook_levin_compilation M n hn htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (compiledPoly (cook_levin_compilation M n hn htb hns))
      ≤ totalProfileBound n := profile_compression_rank_bound M n hn htb hns
    _ ≤ n ^ 200 := totalProfileBound_le_pow n hn

end ProfileCompression
