import GodMoveSATDesignatedExtraction
import GodMoveIdempotentExtractionExtension

/-!
# An idempotent witness-free projection recovering the designated sheet

Separate source and target coordinates turn the explicit algebra extraction
into an idempotent linear projection. On the embedded actual SAT-machine
source, its unchanged-parameter SPDP rank does not increase, and its output
is the embedded production designated sheet with all square terms retained.

The rank comparison is source-specific. The map's range contains the full
output-coordinate polynomial space, not a proved polynomial-dimensional
space. No runtime-derived source-rank bound is asserted.
-/

namespace GodMoveSATDesignatedProjection

set_option exponentiation.threshold 1000

open MvPolynomial MultilinearSPDP SPDP
open GodMoveBooleanInterpolation GodMoveMachineFaceExtraction
open GodMoveSATUnitExtraction GodMoveSATDesignatedExtraction GodMoveUnitCharacteristic
open GodMoveIdempotentExtractionExtension
open GodMoveMonomialMinor (discreteBlocks)
open GodMoveInjectiveRankTransport
open PallLean.Paper93.DeepMath.PathB ComposableMachine SeparationTarget
open Step4Compiler.Step252

noncomputable def augmentedSource (M : Machine) (T : ℕ → ℕ) (n : ℕ) :
    GodMoveBooleanInterpolation.Poly (unitInputLength (n / 3) + n / 3) :=
  embedSource (unitInputLength (n / 3)) (n / 3)
    (machineSource M T (unitFormula (n / 3)) (n / 3))

/-- A size-dependent linear projection; its definition contains no machine,
clock, SAT answer, or satisfying-assignment parameter. -/
noncomputable def designatedProjection (n : ℕ) :
    GodMoveBooleanInterpolation.Poly (unitInputLength (n / 3) + n / 3) →ₗ[ℚ]
      GodMoveBooleanInterpolation.Poly (unitInputLength (n / 3) + n / 3) :=
  projection (sheetExtraction n)

theorem designatedProjection_idempotent (n : ℕ) :
    designatedProjection n ∘ₗ designatedProjection n = designatedProjection n :=
  projection_idempotent _

theorem designatedProjection_isProjectionGauge (n : ℕ) :
    GaugeMonotonicity.IsProjectionGauge (designatedProjection n) :=
  projection_isProjectionGauge _

/-- Exact recovery of the actual nonmultilinear sheet in its dedicated copy. -/
theorem designatedProjection_correct
    (D : TuringMachine.DTM) (n : ℕ) (hn2 : 2 ≤ n)
    (htb : D.timeBound ≤ 4) (hns : D.numStates ≤ n)
    (B : BlockPartition (PaperFaithfulCompilation.cookLevinUVSplit D n).total)
    (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T) :
    designatedProjection n (augmentedSource M T n) =
      embedOutput (unitInputLength (n / 3)) (n / 3)
        (cookLevinStrictFOBTarget D n hn2 htb hns B).coupledPoly := by
  rw [designatedProjection, augmentedSource, projection_embedSource,
    sheetExtraction_correct D n hn2 htb hns B M T hD]

/-- Adding separate output coordinates preserves the source rank exactly. -/
theorem augmentedSource_rank (M : Machine) (T : ℕ → ℕ) (n k ell : ℕ) :
    mlBlockedSpdpRank (discreteBlocks (unitInputLength (n / 3) + n / 3)) k ell
        (augmentedSource M T n) =
      mlBlockedSpdpRank (discreteBlocks (unitInputLength (n / 3))) k ell
        (machineSource M T (unitFormula (n / 3)) (n / 3)) := by
  unfold augmentedSource embedSource
  apply strict_rank_discrete_rename
  intro i j hij
  apply Fin.ext
  have h := congrArg Fin.val hij
  exact h

/-- The production partition's rank survives the output embedding. This is
independent of the source-specific upper comparison below. -/
theorem designated_sheet_rank_le_projection
    (D : TuringMachine.DTM) (n : ℕ) (hn2 : 2 ≤ n)
    (htb : D.timeBound ≤ 4) (hns : D.numStates ≤ n)
    (B : BlockPartition (PaperFaithfulCompilation.cookLevinUVSplit D n).total)
    (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T) (k ell : ℕ) :
    mlBlockedSpdpRank (cookLevinStrictFOBTarget D n hn2 htb hns B).coupledPartition
        k ell (cookLevinStrictFOBTarget D n hn2 htb hns B).coupledPoly ≤
      mlBlockedSpdpRank (discreteBlocks (unitInputLength (n / 3) + n / 3)) k ell
        (designatedProjection n (augmentedSource M T n)) := by
  rw [designatedProjection_correct D n hn2 htb hns B M T hD]
  unfold embedOutput
  rw [strict_rank_discrete_rename _ (by
    intro i j hij
    apply Fin.ext
    have h := congrArg Fin.val hij
    change unitInputLength (n / 3) + i.val = unitInputLength (n / 3) + j.val at h
    omega)]
  exact mlBlockedSpdpRank_coarsen ℚ _ _ k ell _ (fun i j hij => by
    change i = j at hij
    rw [hij])

/-- The existing designated identity-minor bound survives this actual
idempotent extraction at the same log/log window. -/
theorem designatedProjection_rank_gt_npow200
    (D : TuringMachine.DTM) (n : ℕ) (hn : 2 ^ 804 ≤ n) (hn2 : 2 ≤ n)
    (htb : D.timeBound ≤ 4) (hns : D.numStates ≤ n)
    (B : BlockPartition (PaperFaithfulCompilation.cookLevinUVSplit D n).total)
    (hB : B = PaperFaithfulCompilation.extendedCookLevinPartition D n hn2)
    (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T) :
    n ^ 200 < mlBlockedSpdpRank
      (discreteBlocks (unitInputLength (n / 3) + n / 3))
      (Nat.log 2 n) (Nat.log 2 n)
      (designatedProjection n (augmentedSource M T n)) :=
  (GodMoveDesignatedSheetNormalization.designated_sheet_rank_gt_npow200
    D n hn hn2 htb hns B hB).trans_le
      (designated_sheet_rank_le_projection D n hn2 htb hns B M T hD _ _)

/-- The same-ambient idempotent map does not increase rank on the constructed
source, at the same discrete partition, derivative order and shift bound. -/
theorem designatedProjection_rank_le
    (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T)
    (n k ell : ℕ) (hk : k ≤ n / 3) (hell : k ≤ ell) :
    mlBlockedSpdpRank (discreteBlocks (unitInputLength (n / 3) + n / 3)) k ell
        (designatedProjection n (augmentedSource M T n)) ≤
      mlBlockedSpdpRank (discreteBlocks (unitInputLength (n / 3) + n / 3)) k ell
        (augmentedSource M T n) := by
  rw [augmentedSource_rank, designatedProjection, augmentedSource, projection_embedSource]
  unfold embedOutput
  rw [strict_rank_discrete_rename _ (by
    intro i j hij
    apply Fin.ext
    have h := congrArg Fin.val hij
    change unitInputLength (n / 3) + i.val = unitInputLength (n / 3) + j.val at h
    omega)]
  exact sheetExtraction_rank_le_source M T hD n k ell hk hell _

theorem designatedProjection_paper_window_rank_le
    (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T)
    (n : ℕ) (hn : 2 ^ 20 ≤ n) :
    mlBlockedSpdpRank (discreteBlocks (unitInputLength (n / 3) + n / 3))
        (Nat.log 2 n) (Nat.log 2 n) (designatedProjection n (augmentedSource M T n)) ≤
      mlBlockedSpdpRank (discreteBlocks (unitInputLength (n / 3) + n / 3))
        (Nat.log 2 n) (Nat.log 2 n) (augmentedSource M T n) :=
  designatedProjection_rank_le M T hD n _ _ (log_le_sheetVars n hn) le_rfl

end GodMoveSATDesignatedProjection

#print axioms GodMoveSATDesignatedProjection.designatedProjection_idempotent
#print axioms GodMoveSATDesignatedProjection.designatedProjection_isProjectionGauge
#print axioms GodMoveSATDesignatedProjection.designatedProjection_correct
#print axioms GodMoveSATDesignatedProjection.augmentedSource_rank
#print axioms GodMoveSATDesignatedProjection.designated_sheet_rank_le_projection
#print axioms GodMoveSATDesignatedProjection.designatedProjection_rank_gt_npow200
#print axioms GodMoveSATDesignatedProjection.designatedProjection_rank_le
#print axioms GodMoveSATDesignatedProjection.designatedProjection_paper_window_rank_le
