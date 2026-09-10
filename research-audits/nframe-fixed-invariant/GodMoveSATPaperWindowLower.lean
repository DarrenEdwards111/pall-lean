import GodMoveSATSourceCanonicity
import GodMoveSATUnitExtraction

/-!
# SAT source lower bounds at the exact paper derivative window

The source uses `m = n / 3` unit-query assignment variables, while its
derivative order is exactly `log₂ n`. The existing binomial minor proves
a lower bound `n ^ (log₂ n / 4)` at this window, with arbitrary shift budget.
The actual encoded source length is at most quadratic in `n`, so no eventual
polynomial bound in that encoded length is possible either.

Only faithful SAT correctness is assumed. There is no runtime upper bound,
no polynomial-time assumption, and no separation theorem in this module.
-/

namespace GodMoveSATPaperWindowLower

open MvPolynomial SPDP MultilinearSPDP
open GodMoveBooleanInterpolation GodMoveMachineFaceExtraction GodMoveMachineSourceMinor
open GodMoveSATSourceCanonicity GodMoveUnitCharacteristic
open GodMoveSATUnitExtraction
open GodMoveMonomialMinor (discreteBlocks)
open PallLean.Paper93.DeepMath.PathB ComposableMachine SeparationTarget

/-- The actual normalized SAT source already has the full lower bound at
the paper's derivative order, rather than `log₂(n/3)` or `log₂(encoded length)`. -/
theorem paper_window_rank_ge_power
    (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T) (n ell : ℕ)
    (hn : 2 ^ 20 ≤ n) :
    n ^ (Nat.log 2 n / 4) ≤
      mlBlockedSpdpRank (discreteBlocks (unitSourceLength (n / 3)))
        (Nat.log 2 n) ell (machineSource M T (unitFormula (n / 3)) (n / 3)) :=
  (BinomialBound.binomial_lower_bound_concrete n hn).trans
    ((Nat.choose_mono (Nat.log 2 n) (by omega : n / 30 ≤ n / 3)).trans
      (choose_le_machineSource_strict_rank M T hD (n / 3) (Nat.log 2 n) ell))

theorem paper_window_inclusive_rank_ge_power
    (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T) (n ell : ℕ)
    (hn : 2 ^ 20 ≤ n) :
    n ^ (Nat.log 2 n / 4) ≤
      mlBlockedSpdpRankInc (discreteBlocks (unitSourceLength (n / 3)))
        (Nat.log 2 n) ell (machineSource M T (unitFormula (n / 3)) (n / 3)) :=
  (BinomialBound.binomial_lower_bound_concrete n hn).trans
    ((Nat.choose_mono (Nat.log 2 n) (by omega : n / 30 ≤ n / 3)).trans
      (choose_le_machineSource_inclusive_rank M T hD (n / 3) (Nat.log 2 n) ell))

theorem npow_lt_paper_window_rank
    (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T) (n d ell : ℕ)
    (hn : 2 ^ (max 20 (4 * (d + 1))) ≤ n) :
    n ^ d < mlBlockedSpdpRank (discreteBlocks (unitSourceLength (n / 3)))
      (Nat.log 2 n) ell (machineSource M T (unitFormula (n / 3)) (n / 3)) := by
  have hn20 : 2 ^ 20 ≤ n :=
    (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (le_max_left _ _)).trans hn
  have hnpow : 2 ^ (4 * (d + 1)) ≤ n :=
    (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (le_max_right _ _)).trans hn
  have hlog : 4 * (d + 1) ≤ Nat.log 2 n :=
    Nat.le_log_of_pow_le (by decide : 1 < 2) hnpow
  have hn1 : 1 < n := (by norm_num : 1 < (2 : ℕ) ^ 20).trans_le hn20
  exact (Nat.pow_lt_pow_right hn1 (by omega : d < Nat.log 2 n / 4)).trans_le
    (paper_window_rank_ge_power M T hD n ell hn20)

/-- No fixed degree and constant bound this source rank at the exact paper
derivative window. The shift allowance may vary arbitrarily with the scale. -/
theorem no_eventual_polynomial_paper_window_bound
    (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T) (ell : ℕ → ℕ) :
    ¬ ∃ C d n0 : ℕ, ∀ n ≥ n0,
      mlBlockedSpdpRank (discreteBlocks (unitSourceLength (n / 3)))
        (Nat.log 2 n) (ell n) (machineSource M T (unitFormula (n / 3)) (n / 3)) ≤
          C * n ^ d := by
  rintro ⟨C, d, n0, hbound⟩
  let n := max (max C n0) (2 ^ (max 20 (4 * (d + 1 + 1))))
  have hn0 : n0 ≤ n := (le_max_right C n0).trans (le_max_left _ _)
  have hnC : C ≤ n := (le_max_left C n0).trans (le_max_left _ _)
  have hnlarge : 2 ^ (max 20 (4 * (d + 1 + 1))) ≤ n := le_max_right _ _
  have hlow := npow_lt_paper_window_rank M T hD n (d + 1) (ell n) hnlarge
  have hup : C * n ^ d ≤ n ^ (d + 1) := by
    rw [pow_succ, mul_comm (n ^ d) n]
    exact Nat.mul_le_mul_right _ hnC
  exact (not_le_of_gt hlow) ((hbound n hn0).trans hup)

/-- The code-length estimate is derived for the actual floor-sized query,
with no external input-size assumption. -/
theorem paper_source_length_add_one_le (n : ℕ) (hn : 3 ≤ n) :
    unitSourceLength (n / 3) + 1 ≤ 96 * n ^ 2 := by
  exact (unitSourceLength_add_one_le (n / 3) (by omega)).trans
    (Nat.mul_le_mul_left 96 (Nat.pow_le_pow_left (Nat.div_le_self n 3) 2))

/-- Even a bound in the actual encoded source length fails at the exact
paper derivative window; this is still solely a rank lower bound. -/
theorem no_eventual_polynomial_encoded_paper_window_bound
    (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T) (ell : ℕ → ℕ) :
    ¬ ∃ C d n0 : ℕ, ∀ n ≥ n0,
      mlBlockedSpdpRank (discreteBlocks (unitSourceLength (n / 3)))
        (Nat.log 2 n) (ell n) (machineSource M T (unitFormula (n / 3)) (n / 3)) ≤
          C * (unitSourceLength (n / 3) + 1) ^ d := by
  rintro ⟨C, d, n0, hbound⟩
  apply no_eventual_polynomial_paper_window_bound M T hD ell
  refine ⟨C * 96 ^ d, 2 * d, max n0 3, ?_⟩
  intro n hn
  have hn0 : n0 ≤ n := (le_max_left _ _).trans hn
  have hn3 : 3 ≤ n := (le_max_right _ _).trans hn
  calc
    _ ≤ C * (unitSourceLength (n / 3) + 1) ^ d := hbound n hn0
    _ ≤ C * (96 * n ^ 2) ^ d :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (paper_source_length_add_one_le n hn3) _)
    _ = (C * 96 ^ d) * n ^ (2 * d) := by rw [mul_pow, ← pow_mul, mul_assoc]

theorem no_eventual_polynomial_encoded_paper_window_inclusive_bound
    (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T) (ell : ℕ → ℕ) :
    ¬ ∃ C d n0 : ℕ, ∀ n ≥ n0,
      mlBlockedSpdpRankInc (discreteBlocks (unitSourceLength (n / 3)))
        (Nat.log 2 n) (ell n) (machineSource M T (unitFormula (n / 3)) (n / 3)) ≤
          C * (unitSourceLength (n / 3) + 1) ^ d := by
  rintro ⟨C, d, n0, hbound⟩
  apply no_eventual_polynomial_encoded_paper_window_bound M T hD ell
  exact ⟨C, d, n0, fun n hn =>
    (Submodule.finrank_mono (mlBlockedSpdpSubspace_le_inc _ _ _ _)).trans (hbound n hn)⟩

/-- The exact log/log interface for the operational paper source. -/
theorem no_eventual_polynomial_paper_source_encoded_bound
    (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T) :
    ¬ ∃ C d n0 : ℕ, ∀ n ≥ n0,
      mlBlockedSpdpRank (discreteBlocks (unitInputLength (n / 3)))
        (Nat.log 2 n) (Nat.log 2 n)
        (machineSource M T (unitFormula (n / 3)) (n / 3)) ≤
          C * (unitInputLength (n / 3) + 1) ^ d :=
  no_eventual_polynomial_encoded_paper_window_bound M T hD (Nat.log 2)

end GodMoveSATPaperWindowLower

#print axioms GodMoveSATPaperWindowLower.paper_window_rank_ge_power
#print axioms GodMoveSATPaperWindowLower.paper_window_inclusive_rank_ge_power
#print axioms GodMoveSATPaperWindowLower.npow_lt_paper_window_rank
#print axioms GodMoveSATPaperWindowLower.no_eventual_polynomial_paper_window_bound
#print axioms GodMoveSATPaperWindowLower.paper_source_length_add_one_le
#print axioms GodMoveSATPaperWindowLower.no_eventual_polynomial_encoded_paper_window_bound
#print axioms GodMoveSATPaperWindowLower.no_eventual_polynomial_encoded_paper_window_inclusive_bound
#print axioms GodMoveSATPaperWindowLower.no_eventual_polynomial_paper_source_encoded_bound
