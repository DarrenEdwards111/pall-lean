/-
  Archive/Paper93Unsafe/ProfileCompressionRankBound.lean

  UNSAFE — NOT part of the consistent default build target.

  The Step-D "assembly" declarations from SymmetricPowerBound that transitively
  use the false `spdp_profile_generators` axiom (via
  `SymmetricPower.product_leibniz_profile_cover`). These produce the false
  P-side bound `SPDP rank ≤ (κ+1)^12 ≤ (3κ+1)^12` on the compiled polynomial.

  KEPT LIVE in SymmetricPowerBound (NOT here): the *conditional* siblings
  `rank_bound_from_honest_fixed_profile_factorization` and
  `profile_symmetric_power_factorization_of_honest_cover` (they take a
  `HasFixedProfileCoverFamily` hypothesis and do NOT use the axiom — the honest
  `_of_templateCollapse` path and Step4Compiler depend on them), plus the pure
  arithmetic `combinedBound_le_totalProfileBound`.
-/
import PallLean.SymmetricPowerBound
import PallLean.Archive.Paper93Unsafe.SpdpProfileGeneratorsAxiom

namespace SymmetricPowerBound

open SPDP MultilinearSPDP MvPolynomial TuringMachine PaperFaithfulSeparation

/-- Symmetric power descent bound re-export (archived; uses the false axiom). -/
theorem leibniz_symmetric_power_descent_bound
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    Module.finrank ℚ ↥(mlBlockedSpdpSubspace
      (cook_levin_compilation M n hn htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (compiledPoly (cook_levin_compilation M n hn htb hns)))
    ≤ combinedProfileBound (Nat.log 2 n) :=
  SymmetricPower.leibniz_symmetric_power_descent_bound M n hn htb hns

/-- `spdp_profile_generators` ⇒ `HasFiniteProfileCover` (archived; uses the false axiom). -/
theorem hasFiniteProfileCover_of_spdp_profile_generators
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    HasFiniteProfileCover
      (cook_levin_compilation M n hn htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (compiledPoly (cook_levin_compilation M n hn htb hns)) := by
  obtain ⟨numP, spaces, hnumP, hfin, hbound, hcover⟩ :=
    SymmetricPower.product_leibniz_profile_cover M n hn htb hns
  exact ⟨numP, spaces, le_trans hnumP (by unfold profileCount; rfl), hfin,
    fun i => le_trans (hbound i) (by unfold withinProfileBound; rfl), hcover⟩

/-- Unconditional rank bound from the axiom-derived profile cover (archived). -/
theorem rank_bound_from_fixed_profile_factorization
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    mlBlockedSpdpRank
      (cook_levin_compilation M n hn htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (compiledPoly (cook_levin_compilation M n hn htb hns))
    ≤ combinedProfileBound (Nat.log 2 n) :=
  rank_le_combinedBound_of_hasFiniteProfileCover _ _ _ _
    (hasFiniteProfileCover_of_spdp_profile_generators M n hn htb hns)

/-- Unconditional Step-B factorization (archived; uses the false axiom). -/
theorem profile_symmetric_power_factorization
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    mlBlockedSpdpRank
      (cook_levin_compilation M n hn htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (compiledPoly (cook_levin_compilation M n hn htb hns))
    ≤ combinedProfileBound (Nat.log 2 n) :=
  rank_bound_from_fixed_profile_factorization M n hn htb hns

/-- The FALSE P-side bound `SPDP rank ≤ (3κ+1)^12` (archived). Refuted by the
NP-side identity minor on the same compiled object. -/
theorem profile_compression_rank_bound (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    mlBlockedSpdpRank
      (cook_levin_compilation M n hn htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (compiledPoly (cook_levin_compilation M n hn htb hns))
    ≤ (3 * Nat.log 2 n + 1) ^ 12 := by
  have h1 := profile_symmetric_power_factorization M n hn htb hns
  have h2 : combinedProfileBound (Nat.log 2 n) = (Nat.log 2 n + 1) ^ 12 :=
    combinedProfileBound_eq (Nat.log 2 n)
  have h3 : (Nat.log 2 n + 1) ^ 12 ≤ (3 * Nat.log 2 n + 1) ^ 12 := by
    exact Nat.pow_le_pow_left (by omega) 12
  omega

end SymmetricPowerBound
