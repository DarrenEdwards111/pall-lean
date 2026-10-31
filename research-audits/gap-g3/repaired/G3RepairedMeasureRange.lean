import GodMoveSATUnitExtraction
import GodMoveShiftedRankUpper
import GodMoveLinearTimeRankObstruction

/-!
# G3 (refocused): the strict measure cannot separate the SAT MLE from linear-time functions

Against codex/godmove-gap-repairs @ 21921958 (objects 3bda8850 / d105443a), unchanged:
strict `mlBlockedSpdpRank`, `discreteBlocks`, `machineSource`, `unitInputLength`, the branch's
linear-time `scanner` / `scannerSource`, and the branch's row-count bound `strict_rank_le_shiftBudget`.

Main point (`rank_le_two_pow_mul_scanner`, `rank_le_two_pow_mul_and`): for EVERY polynomial `p` in
`L` variables (in particular the SAT multilinear extension = the repaired source of any correct
decider), at every partition and every `k, ell`,

    rank(p) ≤ 2^k · rank(scannerSource L)      and      rank(p) ≤ 2^k · rank(x₁⋯x_L),

where the scanner is a fixed 4-state machine deciding an `InP` language in `L+1` steps and
x₁⋯x_L is the AND function. At the paper window k = ⌊log₂ n⌋ the factor is ≤ n
(`sat_source_le_n_mul_scanner`). Hence any rank threshold met by a linear-time function's
source is exceeded by the SAT source by at most a factor n: no superpolynomial
separation of SAT from easy functions is expressible in this measure at these parameters
(`no_superpoly_gap_over_scanner`).
-/

namespace GapG3RepairedRange

open MvPolynomial MultilinearSPDP SPDP
open GodMoveBooleanInterpolation GodMoveMachineFaceExtraction GodMoveSATUnitExtraction
open GodMoveShiftedRankUpper GodMoveLinearTimeRankObstruction GodMoveUnitCharacteristic
open GodMoveMonomialMinor (fullMonomial discreteBlocks)
open PallLean.Paper93.DeepMath.PathB ComposableMachine

/-- Every polynomial is within factor `2^k` of the linear-time scanner's source. -/
theorem rank_le_two_pow_mul_scanner {L : ℕ} (B : BlockPartition L) (k ell : ℕ) (p : Poly L) :
    mlBlockedSpdpRank B k ell p ≤
      2 ^ k * mlBlockedSpdpRank (discreteBlocks L) k ell (scannerSource L) := by
  calc mlBlockedSpdpRank B k ell p ≤ Nat.choose L k * 2 ^ k :=
        strict_rank_le_choose_mul_two_pow B k ell p
    _ = 2 ^ k * Nat.choose L k := Nat.mul_comm _ _
    _ ≤ _ := Nat.mul_le_mul_left _ (choose_le_scannerSource_rank L k ell)

/-- Every polynomial is within factor `2^k` of the AND monomial x₁⋯x_L. -/
theorem rank_le_two_pow_mul_and {L : ℕ} (B : BlockPartition L) (k ell : ℕ) (p : Poly L) :
    mlBlockedSpdpRank B k ell p ≤
      2 ^ k * mlBlockedSpdpRank (discreteBlocks L) k ell (fullMonomial L) := by
  calc mlBlockedSpdpRank B k ell p ≤ Nat.choose L k * 2 ^ k :=
        strict_rank_le_choose_mul_two_pow B k ell p
    _ = 2 ^ k * Nat.choose L k := Nat.mul_comm _ _
    _ ≤ _ := Nat.mul_le_mul_left _ (GodMoveMonomialMinor.choose_le_strict_rank L k ell)

/-- Paper window: the repaired source of ANY machine (in particular every correct SAT decider,
whose source is the SAT MLE) has rank at most `n ·` the scanner's rank on the same `L_n` bits,
with the same strict measure, partition and `k = ell = ⌊log₂ n⌋`. -/
theorem sat_source_le_n_mul_scanner (n : ℕ) (hn : 1 ≤ n) (M : Machine) (T : ℕ → ℕ) :
    mlBlockedSpdpRank (discreteBlocks (unitInputLength (n / 3))) (Nat.log 2 n) (Nat.log 2 n)
        (machineSource M T (unitFormula (n / 3)) (n / 3)) ≤
      n * mlBlockedSpdpRank (discreteBlocks (unitInputLength (n / 3))) (Nat.log 2 n)
        (Nat.log 2 n) (scannerSource (unitInputLength (n / 3))) :=
  (rank_le_two_pow_mul_scanner _ _ _ _).trans
    (Nat.mul_le_mul_right _ (Nat.pow_log_le_self 2 (by omega)))

/-- Function-level form: if a bound `g` is satisfied by the linear-time scanner's sources at all
lengths (as any sound "P-side" bound for poly-time functions must be), then EVERY polynomial,
in particular the SAT MLE, satisfies `2^k · g`. -/
theorem no_superpoly_gap_over_scanner (k ell : ℕ) (g : ℕ → ℕ)
    (hg : ∀ L, mlBlockedSpdpRank (discreteBlocks L) k ell (scannerSource L) ≤ g L)
    (L : ℕ) (B : BlockPartition L) (p : Poly L) :
    mlBlockedSpdpRank B k ell p ≤ 2 ^ k * g L :=
  (rank_le_two_pow_mul_scanner B k ell p).trans (Nat.mul_le_mul_left _ (hg L))

end GapG3RepairedRange

#print axioms GapG3RepairedRange.rank_le_two_pow_mul_scanner
#print axioms GapG3RepairedRange.rank_le_two_pow_mul_and
#print axioms GapG3RepairedRange.sat_source_le_n_mul_scanner
#print axioms GapG3RepairedRange.no_superpoly_gap_over_scanner
