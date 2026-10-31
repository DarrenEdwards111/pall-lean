import GodMoveSATDesignatedExtraction

/-!
# Gap G3 against the repaired God-Move construction (codex/godmove-gap-repairs @ 21921958)

Built against the research-audit module chain of commit 21921958 (read-only worktree;
see `build_repaired.sh`). Objects are THAT branch's definitions, unchanged:
`machineSource`, `unitExtraction`, `sheetExtraction`, `operationalPaperSource`,
`cookLevinStrictFOBTarget`, `mlBlockedSpdpRank`, `discreteBlocks`.

Results.
* `acceptAll_source_eq_one`, `acceptAll_passesG3`, `acceptAll_passesG3_extracted`:
  the always-accept machine's repaired source is the constant 1, so G3 (rank < C(n/3, log n))
  HOLDS for it. The Phase-3 template obstruction does not apply: this source is not
  template-generated / M-blind (it is the interpolation of M's output on all words of length L).
* `extraction_depends_only_on_face`: the repaired extraction depends on M only through
  M's 2^m answers on the pinned unit queries (the "face").
* `designated_sheet_of_faceCorrect`, `choose_le_source_of_faceCorrect`,
  `designated_rank_le_source_of_faceCorrect`, `npow200_lt_source_of_faceCorrect`:
  everything the repaired route derives from SAT correctness (exact designated sheet, rank transport,
  the C(n/3, log n) > n^200 lower bound) already follows from correctness on the face alone.
  The face queries are unit-clause CNFs (an easy language), so this lower bound cannot
  separate SAT deciders from machines that are only correct on that easy family.
No theorem here proves or refutes P ≠ NP.
-/

namespace GapG3Repaired

set_option exponentiation.threshold 1000

open MvPolynomial MultilinearSPDP SPDP PiStarConcrete
open GodMoveBooleanInterpolation GodMoveMachineFaceExtraction GodMoveSATUnitExtraction
open GodMoveQuadraticSheetLift GodMoveUnitCharacteristic GodMoveSATDesignatedExtraction
open GodMoveCircuitConnection GodMoveFaithfulHandshake GodMovePinnedSATQueries
open GodMoveInjectiveRankTransport GodMoveSymbolicPinnedInput GodMovePinnedFaceLayout
open GodMoveMultilinearRestriction GodMoveCircuitNormalization
open GodMoveMonomialMinor (fullMonomial discreteBlocks)
open PallLean.Paper93.DeepMath.PathB ComposableMachine SeparationTarget
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open Step4Compiler.Step252

/-! ## Always-accept in the branch's `ComposableMachine` model -/

/-- One state, halted at start, accepting. -/
def acceptAll : Machine where
  State := Unit
  fin := inferInstance
  dec := inferInstance
  start := ()
  halt := fun _ => true
  δ := fun _ _ => ((), none, 2)
  accept := fun _ => true

theorem acceptAll_decideOut (x : List Bool) (t : ℕ) : decideOut acceptAll x t = true := rfl

theorem acceptAll_source_eq_one (T : ℕ → ℕ) (φ : Formula) (n : ℕ) :
    machineSource acceptAll T φ n = 1 := by
  classical
  apply multilinear_eq_of_boolean_eval
  · exact machineSource_multilinear acceptAll T φ n
  · intro m hm i
    have : m = 0 := by
      have h1 : (1 : Poly (inputTemplate φ n).length).support ⊆ {0} := by
        rw [← C_1]; exact support_C_subset
      simpa using h1 hm
    subst this; simp
  · intro a
    rw [machineSource, circuitTarget_eq_interpolate, eval_interpolate, circuitFor_output,
      acceptAll_decideOut]
    simp [bit]

/-- G3 (Lean measure) for the repaired source: the always-accept machine's source has
rank 0 < C(n/3, log n) whenever κ ≥ 1 — G3 does not fail here. -/
theorem acceptAll_source_rank_zero (T : ℕ → ℕ) (φ : Formula) (n : ℕ)
    (B : BlockPartition (inputTemplate φ n).length) (k ell : ℕ) (hk : 1 ≤ k) :
    mlBlockedSpdpRank B k ell (machineSource acceptAll T φ n) = 0 := by
  rw [acceptAll_source_eq_one, ← C_1, ← zero_add (C (1 : ℚ)),
    mlBlockedSpdpRank_add_const ℚ B k ell 0 1 hk]
  exact mlBlockedSpdpRank_zero B k ell

theorem acceptAll_passesG3 (n : ℕ) (hn : 2 ^ 804 ≤ n) (T : ℕ → ℕ) :
    mlBlockedSpdpRank (discreteBlocks (unitInputLength (n / 3))) (Nat.log 2 n) (Nat.log 2 n)
        (machineSource acceptAll T (unitFormula (n / 3)) (n / 3)) <
      Nat.choose (n / 3) (Nat.log 2 n) := by
  have hlog : 1 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num)
    ((Nat.pow_le_pow_right (by norm_num) (by norm_num : 1 ≤ 804)).trans hn)
  rw [acceptAll_source_rank_zero _ _ _ _ _ _ hlog]
  apply Nat.choose_pos
  exact log_le_sheetVars n ((Nat.pow_le_pow_right (by norm_num) (by norm_num)).trans hn)

/-- Same after the branch's own extraction `sheetExtraction` (an algebra map, so 1 ↦ 1). -/
theorem acceptAll_passesG3_extracted (n : ℕ) (hn : 2 ^ 804 ≤ n) (T : ℕ → ℕ)
    (B : BlockPartition (n / 3)) :
    mlBlockedSpdpRank B (Nat.log 2 n) (Nat.log 2 n)
        (sheetExtraction n (machineSource acceptAll T (unitFormula (n / 3)) (n / 3))) <
      Nat.choose (n / 3) (Nat.log 2 n) := by
  have hlog : 1 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num)
    ((Nat.pow_le_pow_right (by norm_num) (by norm_num : 1 ≤ 804)).trans hn)
  rw [acceptAll_source_eq_one, map_one, ← C_1, ← zero_add (C (1 : ℚ)),
    mlBlockedSpdpRank_add_const ℚ B _ _ 0 1 hlog, mlBlockedSpdpRank_zero]
  apply Nat.choose_pos
  exact log_le_sheetVars n ((Nat.pow_le_pow_right (by norm_num) (by norm_num)).trans hn)

/-! ## Face locality -/

/-- Correctness on the 2^m pinned unit queries only (the face read by `unitExtraction`). -/
def FaceCorrect (M : Machine) (T : ℕ → ℕ) (m : ℕ) : Prop :=
  ∀ a : Fin m → Bool,
    queryOutput M T (unitFormula m) a = evalFormula (extendAssignment a) (unitFormula m)

theorem faceCorrect_of_decides (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T) (m : ℕ) :
    FaceCorrect M T m :=
  fun a => queryOutput_eq_eval M T hD _ (unitFormula_variablesBelow m) a

/-- The repaired extraction sees M only through its answers on the face. -/
theorem extraction_depends_only_on_face (M₁ M₂ : Machine) (T₁ T₂ : ℕ → ℕ) (m : ℕ)
    (h : ∀ a : Fin m → Bool,
      queryOutput M₁ T₁ (unitFormula m) a = queryOutput M₂ T₂ (unitFormula m) a) :
    unitExtraction m (machineSource M₁ T₁ (unitFormula m) m) =
      unitExtraction m (machineSource M₂ T₂ (unitFormula m) m) := by
  rw [unitExtraction_eq_restricted_face, unitExtraction_eq_restricted_face,
    pinnedGauge_extracts_compactTarget, pinnedGauge_extracts_compactTarget,
    compactTarget_eq_machineQueryPolynomial, compactTarget_eq_machineQueryPolynomial,
    machineQueryPolynomial, machineQueryPolynomial, interpolate_congr h]

theorem pinned_of_faceCorrect (M : Machine) (T : ℕ → ℕ) (m : ℕ) (hF : FaceCorrect M T m) :
    pinnedGauge (unitFormula m) m (machineSource M T (unitFormula m) m) =
      rename (variablePosition (unitFormula m) m) (verifierCharacteristic m (unitFormula m)) := by
  rw [pinnedGauge_extracts_compactTarget, compactTarget_eq_machineQueryPolynomial,
    machineQueryPolynomial, verifierCharacteristic, interpolate_congr hF]

theorem unitExtraction_of_faceCorrect (M : Machine) (T : ℕ → ℕ) (m : ℕ)
    (hF : FaceCorrect M T m) :
    unitExtraction m (machineSource M T (unitFormula m) m) = fullMonomial m := by
  rw [unitExtraction_eq_restricted_face, pinned_of_faceCorrect M T m hF,
    restrictPoly_rename, unitFormula_characteristic]

theorem designated_sheet_of_faceCorrect
    (D : TuringMachine.DTM) (n : ℕ) (hn2 : 2 ≤ n)
    (htb : D.timeBound ≤ 4) (hns : D.numStates ≤ n)
    (B : BlockPartition (PaperFaithfulCompilation.cookLevinUVSplit D n).total)
    (M : Machine) (T : ℕ → ℕ) (hF : FaceCorrect M T (n / 3)) :
    sheetExtraction n (machineSource M T (unitFormula (n / 3)) (n / 3)) =
      (cookLevinStrictFOBTarget D n hn2 htb hns B).coupledPoly := by
  rw [sheetExtraction, AlgHom.comp_apply, unitExtraction_of_faceCorrect M T _ hF,
    quadraticLift_recovers_designated_sheet D n hn2 htb hns B]

theorem verifier_rank_le_source_of_faceCorrect (M : Machine) (T : ℕ → ℕ) (m : ℕ)
    (hF : FaceCorrect M T m) (k ell : ℕ) :
    mlBlockedSpdpRank (discreteBlocks m) k ell (verifierCharacteristic m (unitFormula m)) ≤
      mlBlockedSpdpRank (discreteBlocks (unitInputLength m)) k ell
        (machineSource M T (unitFormula m) m) := by
  classical
  have h := mlBlockedSpdpRank_piSubst_le (pinnedKeep (unitFormula m) m)
    (fun j => bit (pinnedFixed (unitFormula m) m j)) (discreteBlocks (unitInputLength m)) k ell
    (machineSource M T (unitFormula m) m) (machineSource_multilinear M T _ m)
  change mlBlockedSpdpRank _ k ell (pinnedGauge (unitFormula m) m _) ≤ _ at h
  rw [pinned_of_faceCorrect M T m hF,
    strict_rank_discrete_rename _ (variablePosition_injective _ m)] at h
  exact h

theorem choose_le_source_of_faceCorrect (M : Machine) (T : ℕ → ℕ) (m k ell : ℕ)
    (hF : FaceCorrect M T m) :
    Nat.choose m k ≤ mlBlockedSpdpRank (discreteBlocks (unitInputLength m)) k ell
      (machineSource M T (unitFormula m) m) :=
  (choose_le_characteristic_strict_rank m k ell).trans
    (verifier_rank_le_source_of_faceCorrect M T m hF k ell)

/-- The branch's designated-sheet rank bridge with `Decides M SATLang T` weakened to
`FaceCorrect`. -/
theorem designated_rank_le_source_of_faceCorrect
    (D : TuringMachine.DTM) (n : ℕ) (hn : 2 ^ 20 ≤ n) (hn2 : 2 ≤ n)
    (htb : D.timeBound ≤ 4) (hns : D.numStates ≤ n)
    (B : BlockPartition (PaperFaithfulCompilation.cookLevinUVSplit D n).total)
    (M : Machine) (T : ℕ → ℕ) (hF : FaceCorrect M T (n / 3)) :
    mlBlockedSpdpRank (cookLevinStrictFOBTarget D n hn2 htb hns B).coupledPartition
        (Nat.log 2 n) (Nat.log 2 n)
        (cookLevinStrictFOBTarget D n hn2 htb hns B).coupledPoly ≤
      mlBlockedSpdpRank (discreteBlocks (unitInputLength (n / 3)))
        (Nat.log 2 n) (Nat.log 2 n)
        (machineSource M T (unitFormula (n / 3)) (n / 3)) := by
  rw [← designated_sheet_of_faceCorrect D n hn2 htb hns B M T hF, sheetExtraction,
    AlgHom.comp_apply, unitExtraction_of_faceCorrect M T _ hF, quadraticLift_fullMonomial]
  calc
    _ ≤ mlBlockedSpdpRank (discreteBlocks (n / 3)) (Nat.log 2 n) (Nat.log 2 n)
        (SymmetricPower.boolFactorFullProd (n / 3)) :=
      mlBlockedSpdpRank_coarsen ℚ _ _ _ _ _ (fun i j hij => by
        change i = j at hij
        rw [hij])
    _ ≤ mlBlockedSpdpRank (discreteBlocks (n / 3)) (Nat.log 2 n) (Nat.log 2 n)
          (fullMonomial (n / 3)) :=
      boolFactorFullProd_rank_le_fullMonomial (n / 3) _ _ (log_le_sheetVars n hn) le_rfl
    _ ≤ _ := by
      rw [← unitFormula_characteristic]
      exact verifier_rank_le_source_of_faceCorrect M T _ hF _ _

/-- Paper window: face-correctness alone forces source rank > n^200 (n ≥ 2^804). -/
theorem npow200_lt_source_of_faceCorrect (n : ℕ) (hn : 2 ^ 804 ≤ n)
    (M : Machine) (T : ℕ → ℕ) (hF : FaceCorrect M T (n / 3)) :
    n ^ 200 < mlBlockedSpdpRank (discreteBlocks (unitInputLength (n / 3)))
      (Nat.log 2 n) (Nat.log 2 n) (machineSource M T (unitFormula (n / 3)) (n / 3)) :=
  (PaperFaithfulCompilation.arithmetic_gap_2pow804 n hn).trans_le
    (choose_le_source_of_faceCorrect M T _ _ _ hF)

end GapG3Repaired

#print axioms GapG3Repaired.acceptAll_source_eq_one
#print axioms GapG3Repaired.acceptAll_source_rank_zero
#print axioms GapG3Repaired.acceptAll_passesG3
#print axioms GapG3Repaired.acceptAll_passesG3_extracted
#print axioms GapG3Repaired.faceCorrect_of_decides
#print axioms GapG3Repaired.extraction_depends_only_on_face
#print axioms GapG3Repaired.unitExtraction_of_faceCorrect
#print axioms GapG3Repaired.designated_sheet_of_faceCorrect
#print axioms GapG3Repaired.verifier_rank_le_source_of_faceCorrect
#print axioms GapG3Repaired.choose_le_source_of_faceCorrect
#print axioms GapG3Repaired.designated_rank_le_source_of_faceCorrect
#print axioms GapG3Repaired.npow200_lt_source_of_faceCorrect
