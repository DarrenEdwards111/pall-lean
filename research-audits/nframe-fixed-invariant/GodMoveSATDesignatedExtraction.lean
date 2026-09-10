import GodMoveSATUnitExtraction
import GodMoveQuadraticSheetLift

/-!
# Faithful SAT output to the actual unnormalized designated sheet

The map first extracts the full monomial through the fixed unit-query face,
then substitutes the production booleanity factors. It is an explicit
algebra map, independent of any satisfying witness. Its rank inequality is
derived for the actual SAT-machine source at unchanged derivative/shift
parameters with sufficient shifts. It is not asserted to be rank monotone
on arbitrary source polynomials, or to be idempotent by itself.

The historical DTM indexes the production designated target; the operational
SAT decider is a separate ComposableMachine. No equivalence of those machine
models is assumed. Their connection here is the proved polynomial identity
for the target and faithful operational correctness for the source.

The source remains Boolean-normalized machine output. This construction
does not supply its polynomial runtime-derived rank upper bound.
-/

namespace GodMoveSATDesignatedExtraction

set_option exponentiation.threshold 1000

open MvPolynomial MultilinearSPDP SPDP
open GodMoveBooleanInterpolation GodMoveMachineFaceExtraction
open GodMoveSATUnitExtraction GodMoveQuadraticSheetLift GodMoveUnitCharacteristic
open GodMoveMonomialMinor (fullMonomial discreteBlocks)
open PallLean.Paper93.DeepMath.PathB ComposableMachine SeparationTarget
open Step4Compiler.Step252

/-- This map depends only on the sheet size and its fixed unit-query template. -/
noncomputable def sheetExtraction (n : ℕ) :
    GodMoveBooleanInterpolation.Poly (unitInputLength (n / 3)) →ₐ[ℚ]
      GodMoveBooleanInterpolation.Poly (n / 3) :=
  (quadraticLift (n / 3)).comp (unitExtraction (n / 3))

/-- SAT correctness yields the complete nonmultilinear designated target,
including the square terms that Boolean normalization would erase. -/
theorem sheetExtraction_correct
    (D : TuringMachine.DTM) (n : ℕ) (hn2 : 2 ≤ n)
    (htb : D.timeBound ≤ 4) (hns : D.numStates ≤ n)
    (B : BlockPartition (PaperFaithfulCompilation.cookLevinUVSplit D n).total)
    (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T) :
    sheetExtraction n (machineSource M T (unitFormula (n / 3)) (n / 3)) =
      (cookLevinStrictFOBTarget D n hn2 htb hns B).coupledPoly := by
  rw [sheetExtraction, AlgHom.comp_apply, unitExtraction_of_decides M T hD,
    quadraticLift_recovers_designated_sheet D n hn2 htb hns B]

/-- Rank transport is derived for this source, using the full shifted-product
space. The target may use any partition; the source uses discrete blocks. -/
theorem sheetExtraction_rank_le_source
    (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T)
    (n k ell : ℕ) (hk : k ≤ n / 3) (hell : k ≤ ell)
    (B : BlockPartition (n / 3)) :
    mlBlockedSpdpRank B k ell
        (sheetExtraction n (machineSource M T (unitFormula (n / 3)) (n / 3))) ≤
      mlBlockedSpdpRank (discreteBlocks (unitInputLength (n / 3))) k ell
        (machineSource M T (unitFormula (n / 3)) (n / 3)) := by
  rw [sheetExtraction, AlgHom.comp_apply, unitExtraction_of_decides M T hD,
    quadraticLift_fullMonomial]
  calc
    _ ≤ mlBlockedSpdpRank (discreteBlocks (n / 3)) k ell
        (SymmetricPower.boolFactorFullProd (n / 3)) :=
      mlBlockedSpdpRank_coarsen ℚ _ B k ell _ (fun i j hij => by
        change i = j at hij
        rw [hij])
    _ ≤ mlBlockedSpdpRank (discreteBlocks (n / 3)) k ell (fullMonomial (n / 3)) :=
      boolFactorFullProd_rank_le_fullMonomial (n / 3) k ell hk hell
    _ ≤ _ := by
      have h := unitExtraction_rank_le_source M T hD (n / 3) k ell
      rwa [unitExtraction_of_decides M T hD] at h

/-- The paper's logarithmic derivative order fits in its actual floor-sized sheet. -/
theorem log_le_sheetVars (n : ℕ) (hn : 2 ^ 20 ≤ n) : Nat.log 2 n ≤ n / 3 := by
  have hnpos : 0 < n := (by norm_num : 0 < (2 : ℕ) ^ 20).trans_le hn
  have hbin := BinomialBound.binomial_lower_bound_concrete n hn
  have hpos : 0 < Nat.choose (n / 30) (Nat.log 2 n) :=
    (Nat.pow_pos hnpos).trans_le hbin
  have hle : Nat.log 2 n ≤ n / 30 := by
    by_contra h
    rw [Nat.choose_eq_zero_of_lt (by omega : n / 30 < Nat.log 2 n)] at hpos
    omega
  omega

/-- The actual designated target retains the exact log/log paper window. -/
theorem designated_sheet_rank_le_source
    (D : TuringMachine.DTM) (n : ℕ) (hn : 2 ^ 20 ≤ n) (hn2 : 2 ≤ n)
    (htb : D.timeBound ≤ 4) (hns : D.numStates ≤ n)
    (B : BlockPartition (PaperFaithfulCompilation.cookLevinUVSplit D n).total)
    (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T) :
    mlBlockedSpdpRank (cookLevinStrictFOBTarget D n hn2 htb hns B).coupledPartition
        (Nat.log 2 n) (Nat.log 2 n)
        (cookLevinStrictFOBTarget D n hn2 htb hns B).coupledPoly ≤
      mlBlockedSpdpRank (discreteBlocks (unitInputLength (n / 3)))
        (Nat.log 2 n) (Nat.log 2 n)
        (machineSource M T (unitFormula (n / 3)) (n / 3)) := by
  rw [← sheetExtraction_correct D n hn2 htb hns B M T hD]
  exact sheetExtraction_rank_le_source M T hD n _ _ (log_le_sheetVars n hn) le_rfl _

/-- A specified operational source in the existing paper-source interface.
This fills the source object, not its separate polynomial-rank bound. -/
noncomputable def operationalPaperSource
    (D : TuringMachine.DTM) (n : ℕ) (hn : 2 ^ 804 ≤ n) (hn2 : 2 ≤ n)
    (htb : D.timeBound ≤ 4) (hns : D.numStates ≤ n)
    (M : Machine) (T : ℕ → ℕ) :
    GlobalGodMoveGauge.Theorem207PaperSource D n hn hn2 htb hns where
  sourceVars := unitInputLength (n / 3)
  sourcePartition := discreteBlocks (unitInputLength (n / 3))
  sourcePoly := machineSource M T (unitFormula (n / 3)) (n / 3)

/-- The named source-to-designated-target rank interface is populated by
the concrete extraction above, without assuming a rank bridge. -/
theorem operationalPaperSource_rank_bridge
    (D : TuringMachine.DTM) (n : ℕ) (hn : 2 ^ 804 ≤ n) (hn2 : 2 ≤ n)
    (htb : D.timeBound ≤ 4) (hns : D.numStates ≤ n)
    (B : BlockPartition (PaperFaithfulCompilation.cookLevinUVSplit D n).total)
    (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T) :
    GlobalGodMoveGauge.Theorem207PaperSourceToTargetRankBridge D n hn hn2 htb hns
      (operationalPaperSource D n hn hn2 htb hns M T)
      (cookLevinStrictFOBTarget D n hn2 htb hns B) := by
  constructor
  exact designated_sheet_rank_le_source D n
    ((Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 20 ≤ 804)).trans hn)
    hn2 htb hns B M T hD

end GodMoveSATDesignatedExtraction

#print axioms GodMoveSATDesignatedExtraction.sheetExtraction_correct
#print axioms GodMoveSATDesignatedExtraction.sheetExtraction_rank_le_source
#print axioms GodMoveSATDesignatedExtraction.log_le_sheetVars
#print axioms GodMoveSATDesignatedExtraction.designated_sheet_rank_le_source
#print axioms GodMoveSATDesignatedExtraction.operationalPaperSource_rank_bridge
