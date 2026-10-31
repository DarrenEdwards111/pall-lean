import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleenePrecHandler
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneReaderGenSome
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneGenExtract
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneSelfReader

/-! # Kleene interpreter project — prec handler totality (.Dom) (PROVED)

The `prec` handler is total (eprecG self-read via `readerGen idCode`, composite b-read via `readerGen
sndSubCode`, base via `readerGen fstSubCode`, all through `readerGen_some`).  `precHandler_dom`.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`. -/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode
open Nat.Partrec
open PallLean.Paper93.DeepMath.PathB.KleeneList (encodeList)

theorem precHandler_dom (E B N k n ec : ℕ) (L : List ℕ) :
    (precHandler.eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList L))) (Nat.pair k (Nat.pair ec n)))).Dom := by
  set X := Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList L))) (Nat.pair k (Nat.pair ec n)) with hX
  have hk : (Code.comp Code.left Code.right).eval X = Part.some k := by rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hnE : nExtract.eval X = Part.some n := by show (Code.comp Code.right (Code.comp Code.right Code.right)).eval X = _; rw [hX]; simp [nExtract, Code.eval, Nat.unpair_pair]
  have hn1 : n1Src.eval X = Part.some (Nat.unpair n).1 := by show (Code.comp Code.left nExtract).eval X = _; rw [comp_eval _ _ _ _ hnE]; simp [Code.eval]
  have hn2 : n2Src.eval X = Part.some (Nat.unpair n).2 := by show (Code.comp Code.right nExtract).eval X = _; rw [comp_eval _ _ _ _ hnE]; simp [Code.eval]
  have hmS : mSrc.eval X = Part.some ((Nat.unpair n).2 - 1) := by show (Code.comp predCode (Code.comp Code.right nExtract)).eval X = _; rw [comp_eval _ _ _ _ (show (Code.comp Code.right nExtract).eval X = Part.some (Nat.unpair n).2 from by rw [comp_eval _ _ _ _ hnE]; simp [Code.eval]), eval_predCode, Nat.pred_eq_sub_one]
  have hpm : pairN1MSrc.eval X = Part.some (Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 - 1)) := by show (Code.pair n1Src mSrc).eval X = _; exact pair_eval _ _ _ _ _ hn1 hmS
  have hkpv : (Code.comp predCode (Code.comp Code.left Code.right)).eval X = Part.some (k - 1) := by rw [comp_eval _ _ _ _ hk, eval_predCode, Nat.pred_eq_sub_one]
  have hBv : bExtract.eval X = Part.some B := by show (Code.comp Code.right (Code.comp Code.left Code.left)).eval X = _; rw [hX]; simp [Code.eval, Nat.unpair_pair]
  -- eprecG total
  obtain ⟨vself, hself⟩ : ∃ v, (readerGen idCode kPredSrc pairN1MSrc).eval X = Part.some v :=
    ⟨_, by have h := readerGen_some idCode kPredSrc pairN1MSrc ec (k-1) (Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 - 1)) E B N k n ec L (eval_idCode ec) (hX ▸ hkpv) (hX ▸ hpm); rw [← hX] at h; exact h⟩
  have hleqEG : (Code.comp leqIndicatorCode (Code.pair pairN1MSrc bExtract)).eval X = Part.some (if Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 - 1) ≤ B then 1 else 0) := by rw [comp_pair_eval _ _ _ _ _ _ hpm hBv, eval_leqIndicatorCode]
  obtain ⟨_, heg⟩ : ∃ w, eprecGCode.eval X = Part.some w := ⟨_, by show (Code.comp mulCode (Code.pair _ _)).eval X = _; rw [comp_pair_eval _ _ _ _ _ _ hleqEG hself, eval_mulCode]⟩
  obtain ⟨_, hiS⟩ : ∃ w, iSrc.eval X = Part.some w := ⟨_, by show (Code.comp predCode eprecGCode).eval X = _; rw [comp_eval _ _ _ _ heg, eval_predCode]⟩
  obtain ⟨vcmp, hcmp⟩ : ∃ v, compositeSrc.eval X = Part.some v := ⟨_, by show (Code.pair n1Src (Code.pair mSrc iSrc)).eval X = _; exact pair_eval _ _ _ _ _ hn1 (pair_eval _ _ _ _ _ hmS hiS)⟩
  obtain ⟨vbr, hbr⟩ : ∃ v, (readerGen sndSubCode (Code.comp Code.left Code.right) compositeSrc).eval X = Part.some v :=
    ⟨_, by have h := readerGen_some sndSubCode (Code.comp Code.left Code.right) compositeSrc (Nat.unpair (Nat.unpair ec).2).2 k vcmp E B N k n ec L (eval_sndSub_gen ec) (hX ▸ hk) (hX ▸ hcmp); rw [← hX] at h; exact h⟩
  obtain ⟨_, hisEG⟩ : ∃ w, (Code.comp isPosCode eprecGCode).eval X = Part.some w := ⟨_, by rw [comp_eval _ _ _ _ heg, eval_isPosCode]⟩
  obtain ⟨_, hleqC⟩ : ∃ w, (Code.comp leqIndicatorCode (Code.pair compositeSrc bExtract)).eval X = Part.some w := ⟨_, by rw [comp_pair_eval _ _ _ _ _ _ hcmp hBv, eval_leqIndicatorCode]⟩
  obtain ⟨_, hib⟩ : ∃ w, (Code.comp mulCode (Code.pair (Code.comp leqIndicatorCode (Code.pair compositeSrc bExtract)) (readerGen sndSubCode (Code.comp Code.left Code.right) compositeSrc))).eval X = Part.some w := ⟨_, by rw [comp_pair_eval _ _ _ _ _ _ hleqC hbr, eval_mulCode]⟩
  obtain ⟨_, hps⟩ : ∃ w, precStepCode.eval X = Part.some w := ⟨_, by show (Code.comp mulCode (Code.pair _ _)).eval X = _; rw [comp_pair_eval _ _ _ _ _ _ hisEG hib, eval_mulCode]⟩
  obtain ⟨vbase, hbase⟩ : ∃ v, (readerGen fstSubCode (Code.comp Code.left Code.right) n1Src).eval X = Part.some v :=
    ⟨_, by have h := readerGen_some fstSubCode (Code.comp Code.left Code.right) n1Src (Nat.unpair (Nat.unpair ec).2).1 k (Nat.unpair n).1 E B N k n ec L (eval_fstSub_gen ec) (hX ▸ hk) (hX ▸ hn1); rw [← hX] at h; exact h⟩
  obtain ⟨_, hguard⟩ : ∃ w, (Code.comp leqIndicatorCode (Code.pair nExtract (Code.comp predCode (Code.comp Code.left Code.right)))).eval X = Part.some w := ⟨_, by rw [comp_pair_eval _ _ _ _ _ _ hnE hkpv, eval_leqIndicatorCode]⟩
  obtain ⟨_, hizN2⟩ : ∃ w, (Code.comp isZeroCode n2Src).eval X = Part.some w := ⟨_, by rw [comp_eval _ _ _ _ hn2, eval_isZeroCode]⟩
  obtain ⟨_, hipN2⟩ : ∃ w, (Code.comp isPosCode n2Src).eval X = Part.some w := ⟨_, by rw [comp_eval _ _ _ _ hn2, eval_isPosCode]⟩
  obtain ⟨_, ht1⟩ : ∃ w, (Code.comp mulCode (Code.pair (Code.comp isZeroCode n2Src) (readerGen fstSubCode (Code.comp Code.left Code.right) n1Src))).eval X = Part.some w := ⟨_, by rw [comp_pair_eval _ _ _ _ _ _ hizN2 hbase, eval_mulCode]⟩
  obtain ⟨_, ht2⟩ : ∃ w, (Code.comp mulCode (Code.pair (Code.comp isPosCode n2Src) precStepCode)).eval X = Part.some w := ⟨_, by rw [comp_pair_eval _ _ _ _ _ _ hipN2 hps, eval_mulCode]⟩
  obtain ⟨_, hsel⟩ : ∃ w, (Code.comp addCode (Code.pair (Code.comp mulCode (Code.pair (Code.comp isZeroCode n2Src) (readerGen fstSubCode (Code.comp Code.left Code.right) n1Src))) (Code.comp mulCode (Code.pair (Code.comp isPosCode n2Src) precStepCode)))).eval X = Part.some w := ⟨_, by rw [comp_pair_eval _ _ _ _ _ _ ht1 ht2, eval_addCode]⟩
  show ((Code.comp mulCode (Code.pair _ _)).eval X).Dom
  rw [comp_pair_eval _ _ _ _ _ _ hguard hsel, eval_mulCode]; trivial

end PallLean.Paper93.DeepMath.PathB.KleeneUCode
#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.precHandler_dom
