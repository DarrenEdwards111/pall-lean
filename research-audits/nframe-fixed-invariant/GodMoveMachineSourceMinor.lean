import GodMoveMachineFaceExtraction
import GodMoveUnitCharacteristic
import GodMoveInjectiveRankTransport

/-!
# An explicit minor in the normalized actual SAT-machine source

The canonical characteristic of the positive-unit CNF is a full monomial.
The proved Boolean-face extraction and injective parameter transport place
its binomial SPDP lower bound inside the normalized source of every correct
SAT machine. The derivative order is `log₂ n`, where `n` is the number of
pinned assignment variables, not the larger encoded machine input length.

This is an easy unit-query family. The source rank is superpolynomial in `n`,
but no bound relates this normalized SPDP rank polynomially to runtime.
Accordingly these results are not a SAT runtime lower bound and do not
identify the extracted verifier characteristic with the paper's hard sheet.
-/

namespace GodMoveMachineSourceMinor

open MvPolynomial SPDP MultilinearSPDP
open GodMoveBooleanInterpolation GodMoveFaithfulHandshake GodMovePinnedSATQueries
open GodMoveSymbolicPinnedInput GodMovePinnedFaceLayout GodMoveMachineFaceExtraction
open GodMoveInjectiveRankTransport GodMoveUnitCharacteristic
open GodMoveMonomialMinor (discreteBlocks)
open PallLean.Paper93.DeepMath.PathB
open ComposableMachine CookLevinReduction SeparationTarget

/-- The verifier's strict rank is retained at the identical derivative and
shift parameters despite its smaller assignment-variable ambient space. -/
theorem verifier_strict_rank_le_source
    (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T)
    (φ : Formula) (n : ℕ) (hvars : VariablesBelow n φ) (k ell : ℕ) :
    mlBlockedSpdpRank (discreteBlocks n) k ell (verifierCharacteristic n φ) ≤
      mlBlockedSpdpRank (discreteBlocks (inputTemplate φ n).length) k ell
        (machineSource M T φ n) := by
  have h := verifier_rank_le_machineSource M T hD φ n hvars
    (discreteBlocks (inputTemplate φ n).length) k ell
  rwa [strict_rank_discrete_rename _ (variablePosition_injective φ n)] at h

theorem verifier_inclusive_rank_le_source
    (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T)
    (φ : Formula) (n : ℕ) (hvars : VariablesBelow n φ) (k ell : ℕ) :
    mlBlockedSpdpRankInc (discreteBlocks n) k ell (verifierCharacteristic n φ) ≤
      mlBlockedSpdpRankInc (discreteBlocks (inputTemplate φ n).length) k ell
        (machineSource M T φ n) :=
  (inclusive_rank_discrete_le_rename _ (variablePosition_injective φ n) k ell _).trans
    (verifier_inclusive_rank_le_machineSource M T hD φ n hvars _ k ell)

/-- A concrete binomial lower bound for the normalized output of the actual
clocked machine, before the unit-query input bits are pinned. -/
theorem choose_le_machineSource_strict_rank
    (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T) (n k ell : ℕ) :
    Nat.choose n k ≤ mlBlockedSpdpRank
      (discreteBlocks (inputTemplate (unitFormula n) n).length) k ell
      (machineSource M T (unitFormula n) n) :=
  (choose_le_characteristic_strict_rank n k ell).trans
    (verifier_strict_rank_le_source M T hD _ n (unitFormula_variablesBelow n) k ell)

theorem choose_le_machineSource_inclusive_rank
    (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T) (n k ell : ℕ) :
    Nat.choose n k ≤ mlBlockedSpdpRankInc
      (discreteBlocks (inputTemplate (unitFormula n) n).length) k ell
      (machineSource M T (unitFormula n) n) :=
  (choose_le_characteristic_inclusive_rank n k ell).trans
    (verifier_inclusive_rank_le_source M T hD _ n (unitFormula_variablesBelow n) k ell)

theorem npow_lt_machineSource_strict_rank
    (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T) (n d ell : ℕ)
    (hn : 2 ^ (max 20 (4 * (d + 1))) ≤ n) :
    n ^ d < mlBlockedSpdpRank
      (discreteBlocks (inputTemplate (unitFormula n) n).length) (Nat.log 2 n) ell
      (machineSource M T (unitFormula n) n) :=
  (GodMoveMonomialMinor.npow_lt_choose_log n d hn).trans_le
    (choose_le_machineSource_strict_rank M T hD n (Nat.log 2 n) ell)

theorem npow_lt_machineSource_inclusive_rank
    (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T) (n d ell : ℕ)
    (hn : 2 ^ (max 20 (4 * (d + 1))) ≤ n) :
    n ^ d < mlBlockedSpdpRankInc
      (discreteBlocks (inputTemplate (unitFormula n) n).length) (Nat.log 2 n) ell
      (machineSource M T (unitFormula n) n) :=
  (GodMoveMonomialMinor.npow_lt_choose_log n d hn).trans_le
    (choose_le_machineSource_inclusive_rank M T hD n (Nat.log 2 n) ell)

/-- Correct SAT behavior forces superpolynomial normalized source rank on
these easy queries; converting this to runtime would require a new upper bound. -/
theorem no_eventual_polynomial_machineSource_strict_bound
    (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T) :
    ¬ ∃ C d n0 : ℕ, ∀ n ≥ n0,
      mlBlockedSpdpRank (discreteBlocks (inputTemplate (unitFormula n) n).length)
        (Nat.log 2 n) 0 (machineSource M T (unitFormula n) n) ≤ C * n ^ d := by
  rintro ⟨C, d, n0, hbound⟩
  apply no_eventual_polynomial_characteristic_strict_bound
  refine ⟨C, d, n0, fun n hn => ?_⟩
  exact (verifier_strict_rank_le_source M T hD _ n (unitFormula_variablesBelow n)
    (Nat.log 2 n) 0).trans (hbound n hn)

theorem no_eventual_polynomial_machineSource_inclusive_bound
    (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T) :
    ¬ ∃ C d n0 : ℕ, ∀ n ≥ n0,
      mlBlockedSpdpRankInc (discreteBlocks (inputTemplate (unitFormula n) n).length)
        (Nat.log 2 n) 0 (machineSource M T (unitFormula n) n) ≤ C * n ^ d := by
  rintro ⟨C, d, n0, hbound⟩
  apply no_eventual_polynomial_characteristic_inclusive_bound
  refine ⟨C, d, n0, fun n hn => ?_⟩
  exact (verifier_inclusive_rank_le_source M T hD _ n (unitFormula_variablesBelow n)
    (Nat.log 2 n) 0).trans (hbound n hn)

end GodMoveMachineSourceMinor

#print axioms GodMoveMachineSourceMinor.verifier_strict_rank_le_source
#print axioms GodMoveMachineSourceMinor.verifier_inclusive_rank_le_source
#print axioms GodMoveMachineSourceMinor.choose_le_machineSource_strict_rank
#print axioms GodMoveMachineSourceMinor.choose_le_machineSource_inclusive_rank
#print axioms GodMoveMachineSourceMinor.npow_lt_machineSource_strict_rank
#print axioms GodMoveMachineSourceMinor.npow_lt_machineSource_inclusive_rank
#print axioms GodMoveMachineSourceMinor.no_eventual_polynomial_machineSource_strict_bound
#print axioms GodMoveMachineSourceMinor.no_eventual_polynomial_machineSource_inclusive_bound
