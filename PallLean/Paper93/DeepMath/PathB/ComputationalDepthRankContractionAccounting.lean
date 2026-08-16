import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSemanticProfileRankTransfer

/-!
# Exact accounting for restriction branching versus residual observer rank

The semantic-profile/rank bridge identifies `2^r` residual observer states at rank `r`.  Querying `q` Boolean
variables creates `2^q` branches, so treating branches independently costs exactly

`2^q · 2^r = 2^(q+r)`.

This file proves the resulting necessity theorem: a rank-based restriction method beats the original `2^R` state
space only if `q + r < R`.  Rank loss equal to query cost gives exact equality and no saving; rank loss smaller than
query cost is worse.  Thus the open contraction lemma really must deliver super-unit rank loss on sufficient Kraft
weight, or exploit cross-branch factorization.
-/

namespace PallLean.Paper93.DeepMath.PathB.RankContractionAccounting

/-- Work of independently exploring `q` binary restriction bits and then enumerating a rank-`r` observer. -/
def rankBranchWork (q r : ℕ) : ℕ := 2 ^ q * 2 ^ r

/-- Exact exponent accounting for restriction branching followed by rank-state enumeration. -/
theorem rankBranchWork_eq_pow_add (q r : ℕ) : rankBranchWork q r = 2 ^ (q + r) := by
  simp [rankBranchWork, pow_add]

/-- If residual rank loss does not exceed query cost (`R ≤ q+r`), independent branching cannot beat `2^R`. -/
theorem no_speedup_of_rank_loss_le_query {R q r : ℕ} (h : R ≤ q + r) :
    2 ^ R ≤ rankBranchWork q r := by
  rw [rankBranchWork_eq_pow_add]
  exact Nat.pow_le_pow_right (by norm_num) h

/-- Exact unit-for-unit rank contraction has zero surplus. -/
theorem zero_surplus_of_exact_rank_accounting {R q r : ℕ} (h : q + r = R) :
    rankBranchWork q r = 2 ^ R := by
  rw [rankBranchWork_eq_pow_add, h]

/-- A genuine speedup forces the strict surplus inequality `q+r<R`. -/
theorem speedup_forces_superunit_rank_loss {R q r : ℕ}
    (hfast : rankBranchWork q r < 2 ^ R) : q + r < R := by
  rw [rankBranchWork_eq_pow_add, Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)] at hfast
  exact hfast

/-- Conversely, strict rank surplus is sufficient for a strict state-enumeration saving. -/
theorem superunit_rank_loss_gives_speedup {R q r : ℕ} (hsurplus : q + r < R) :
    rankBranchWork q r < 2 ^ R := by
  rw [rankBranchWork_eq_pow_add, Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)]
  exact hsurplus

/-- Exact characterization of the rank-accounting target. -/
theorem rank_speedup_iff {R q r : ℕ} :
    rankBranchWork q r < 2 ^ R ↔ q + r < R := by
  constructor
  · exact speedup_forces_superunit_rank_loss
  · exact superunit_rank_loss_gives_speedup

end PallLean.Paper93.DeepMath.PathB.RankContractionAccounting

#print axioms PallLean.Paper93.DeepMath.PathB.RankContractionAccounting.no_speedup_of_rank_loss_le_query
#print axioms PallLean.Paper93.DeepMath.PathB.RankContractionAccounting.speedup_forces_superunit_rank_loss
#print axioms PallLean.Paper93.DeepMath.PathB.RankContractionAccounting.rank_speedup_iff
