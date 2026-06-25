import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneRfindHandler
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneReaderGenSome
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneGenExtract
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneSelfReader

/-! # Kleene interpreter project — rfind' handler totality (.Dom) (PROVED) — all 4 recursive doms done

The `rfind'` handler is total (a-read via `readerGen Code.right`, self via `readerGen idCode`, through
`readerGen_some`).  `rfindHandler_dom`.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`. -/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode
open Nat.Partrec
open PallLean.Paper93.DeepMath.PathB.KleeneList (encodeList)

theorem rfindHandler_dom (E B N k n ec : ℕ) (L : List ℕ) :
    (rfindHandler.eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList L))) (Nat.pair k (Nat.pair ec n)))).Dom := by
  set X := Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList L))) (Nat.pair k (Nat.pair ec n)) with hX
  have hk : (Code.comp Code.left Code.right).eval X = Part.some k := by rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hnE : nExtract.eval X = Part.some n := by show (Code.comp Code.right (Code.comp Code.right Code.right)).eval X = _; rw [hX]; simp [nExtract, Code.eval, Nat.unpair_pair]
  have hn1 : n1Src.eval X = Part.some (Nat.unpair n).1 := by show (Code.comp Code.left nExtract).eval X = _; rw [comp_eval _ _ _ _ hnE]; simp [Code.eval]
  have hm1 : mPlus1Src.eval X = Part.some ((Nat.unpair n).2 + 1) := by show (Code.comp Code.succ (Code.comp Code.right nExtract)).eval X = _; rw [comp_eval _ _ _ _ (show (Code.comp Code.right nExtract).eval X = Part.some (Nat.unpair n).2 from by rw [comp_eval _ _ _ _ hnE]; simp [Code.eval])]; simp [Code.eval]
  have hsi : selfInputSrc.eval X = Part.some (Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 + 1)) := by show (Code.pair n1Src mPlus1Src).eval X = _; exact pair_eval _ _ _ _ _ hn1 hm1
  have hkpv : (Code.comp predCode (Code.comp Code.left Code.right)).eval X = Part.some (k - 1) := by rw [comp_eval _ _ _ _ hk, eval_predCode, Nat.pred_eq_sub_one]
  have hBv : bExtract.eval X = Part.some B := by show (Code.comp Code.right (Code.comp Code.left Code.left)).eval X = _; rw [hX]; simp [Code.eval, Nat.unpair_pair]
  obtain ⟨va, ha⟩ : ∃ v, (readerGen Code.right (Code.comp Code.left Code.right) nExtract).eval X = Part.some v :=
    ⟨_, by have h := readerGen_some Code.right (Code.comp Code.left Code.right) nExtract (Nat.unpair ec).2 k n E B N k n ec L (by simp [Code.eval]) (hX ▸ hk) (hX ▸ hnE); rw [← hX] at h; exact h⟩
  have hx : (Code.comp predCode (readerGen Code.right (Code.comp Code.left Code.right) nExtract)).eval X = Part.some (va - 1) := by rw [comp_eval _ _ _ _ ha, eval_predCode, Nat.pred_eq_sub_one]
  obtain ⟨vsr, hsr⟩ : ∃ v, (readerGen idCode kPredSrc selfInputSrc).eval X = Part.some v :=
    ⟨_, by have h := readerGen_some idCode kPredSrc selfInputSrc ec (k-1) (Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 + 1)) E B N k n ec L (eval_idCode ec) (hX ▸ hkpv) (hX ▸ hsi); rw [← hX] at h; exact h⟩
  obtain ⟨_, hguard⟩ : ∃ w, (Code.comp leqIndicatorCode (Code.pair nExtract (Code.comp predCode (Code.comp Code.left Code.right)))).eval X = Part.some w := ⟨_, by rw [comp_pair_eval _ _ _ _ _ _ hnE hkpv, eval_leqIndicatorCode]⟩
  obtain ⟨_, hisA⟩ : ∃ w, (Code.comp isPosCode (readerGen Code.right (Code.comp Code.left Code.right) nExtract)).eval X = Part.some w := ⟨_, by rw [comp_eval _ _ _ _ ha, eval_isPosCode]⟩
  obtain ⟨_, hizX⟩ : ∃ w, (Code.comp isZeroCode (Code.comp predCode (readerGen Code.right (Code.comp Code.left Code.right) nExtract))).eval X = Part.some w := ⟨_, by rw [comp_eval _ _ _ _ hx, eval_isZeroCode]⟩
  obtain ⟨_, hipX⟩ : ∃ w, (Code.comp isPosCode (Code.comp predCode (readerGen Code.right (Code.comp Code.left Code.right) nExtract))).eval X = Part.some w := ⟨_, by rw [comp_eval _ _ _ _ hx, eval_isPosCode]⟩
  obtain ⟨_, hgs⟩ : ∃ w, (Code.comp leqIndicatorCode (Code.pair selfInputSrc bExtract)).eval X = Part.some w := ⟨_, by rw [comp_pair_eval _ _ _ _ _ _ hsi hBv, eval_leqIndicatorCode]⟩
  obtain ⟨_, hself⟩ : ∃ w, (Code.comp mulCode (Code.pair (Code.comp leqIndicatorCode (Code.pair selfInputSrc bExtract)) (readerGen idCode kPredSrc selfInputSrc))).eval X = Part.some w := ⟨_, by rw [comp_pair_eval _ _ _ _ _ _ hgs hsr, eval_mulCode]⟩
  obtain ⟨_, hthen⟩ : ∃ w, (Code.comp mulCode (Code.pair (Code.comp isZeroCode (Code.comp predCode (readerGen Code.right (Code.comp Code.left Code.right) nExtract))) mPlus1Src)).eval X = Part.some w := ⟨_, by rw [comp_pair_eval _ _ _ _ _ _ hizX hm1, eval_mulCode]⟩
  obtain ⟨_, helse⟩ : ∃ w, (Code.comp mulCode (Code.pair (Code.comp isPosCode (Code.comp predCode (readerGen Code.right (Code.comp Code.left Code.right) nExtract))) (Code.comp mulCode (Code.pair (Code.comp leqIndicatorCode (Code.pair selfInputSrc bExtract)) (readerGen idCode kPredSrc selfInputSrc))))).eval X = Part.some w := ⟨_, by rw [comp_pair_eval _ _ _ _ _ _ hipX hself, eval_mulCode]⟩
  obtain ⟨_, hcond⟩ : ∃ w, (Code.comp addCode (Code.pair (Code.comp mulCode (Code.pair (Code.comp isZeroCode (Code.comp predCode (readerGen Code.right (Code.comp Code.left Code.right) nExtract))) mPlus1Src)) (Code.comp mulCode (Code.pair (Code.comp isPosCode (Code.comp predCode (readerGen Code.right (Code.comp Code.left Code.right) nExtract))) (Code.comp mulCode (Code.pair (Code.comp leqIndicatorCode (Code.pair selfInputSrc bExtract)) (readerGen idCode kPredSrc selfInputSrc))))))).eval X = Part.some w := ⟨_, by rw [comp_pair_eval _ _ _ _ _ _ hthen helse, eval_addCode]⟩
  obtain ⟨_, hinner⟩ : ∃ w, (Code.comp mulCode (Code.pair (Code.comp isPosCode (readerGen Code.right (Code.comp Code.left Code.right) nExtract)) (Code.comp addCode (Code.pair (Code.comp mulCode (Code.pair (Code.comp isZeroCode (Code.comp predCode (readerGen Code.right (Code.comp Code.left Code.right) nExtract))) mPlus1Src)) (Code.comp mulCode (Code.pair (Code.comp isPosCode (Code.comp predCode (readerGen Code.right (Code.comp Code.left Code.right) nExtract))) (Code.comp mulCode (Code.pair (Code.comp leqIndicatorCode (Code.pair selfInputSrc bExtract)) (readerGen idCode kPredSrc selfInputSrc))))))))).eval X = Part.some w := ⟨_, by rw [comp_pair_eval _ _ _ _ _ _ hisA hcond, eval_mulCode]⟩
  show ((Code.comp mulCode (Code.pair _ _)).eval X).Dom
  rw [comp_pair_eval _ _ _ _ _ _ hguard hinner, eval_mulCode]; trivial

end PallLean.Paper93.DeepMath.PathB.KleeneUCode
#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.rfindHandler_dom
