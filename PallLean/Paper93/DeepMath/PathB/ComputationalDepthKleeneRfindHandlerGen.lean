import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneRfindHandler
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneReaderGen
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneGenExtract

/-! # Kleene interpreter project — the generic `rfind'` handler (PROVED)

The `rfind'` handler for arbitrary `ec` (tag-7 path).  Subcode `a.enc = (unpair ec).2` read via `Code.right`
(`rfind' enc = pair 7 a.enc`); self-recursion via `idCode` (reads `ec`).  Uses `rfindSub_lt` for the bound.
`eval_rfindHandler_gen`.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`. -/

open Nat.Partrec
open PallLean.Paper93.DeepMath.PathB.KleeneUCode
open PallLean.Paper93.DeepMath.PathB.KleeneList (encodeList)
open PallLean.Paper93.DeepMath.PathB.KleeneRank (cfgRank cfgRank_lt_code cfgRank_lt_fuel)
namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode

theorem eval_rfindHandler_gen (E B N k n ec : ℕ) (spec : ℕ → ℕ)
    (htag : 1 ≤ (Nat.unpair ec).1) (hec : ec ≤ E) (hn : n ≤ B) (hN : N = cfgRank E B k ec n) (hk1 : 1 ≤ k) :
    rfindHandler.eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N)))) (Nat.pair k (Nat.pair ec n)))
      = Part.some ((if n ≤ k - 1 then 1 else 0)
          * ((if spec (cfgRank E B k (Nat.unpair ec).2 n) = 0 then 0 else 1)
             * ((if spec (cfgRank E B k (Nat.unpair ec).2 n) - 1 = 0 then 1 else 0) * ((Nat.unpair n).2 + 1)
                + (if spec (cfgRank E B k (Nat.unpair ec).2 n) - 1 = 0 then 0 else 1)
                  * (if Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 + 1) ≤ B
                      then spec (cfgRank E B (k - 1) ec (Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 + 1))) else 0)))) := by
  set X := Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N)))) (Nat.pair k (Nat.pair ec n)) with hX
  have hnExt : nExtract.eval X = Part.some n := by
    show (Code.comp Code.right (Code.comp Code.right Code.right)).eval X = _; rw [hX]; simp [nExtract, Code.eval, Nat.unpair_pair]
  have hk : (Code.comp Code.left Code.right).eval X = Part.some k := by rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hkpv : (Code.comp predCode (Code.comp Code.left Code.right)).eval X = Part.some (k - 1) := by
    rw [comp_eval _ _ _ _ hk, eval_predCode, Nat.pred_eq_sub_one]
  have hn1v : n1Src.eval X = Part.some (Nat.unpair n).1 := by
    show (Code.comp Code.left nExtract).eval X = _; rw [comp_eval _ _ _ _ hnExt]; simp [Code.eval]
  have hm1v : mPlus1Src.eval X = Part.some ((Nat.unpair n).2 + 1) := by
    show (Code.comp Code.succ (Code.comp Code.right nExtract)).eval X = _
    rw [comp_eval _ _ _ _ (show (Code.comp Code.right nExtract).eval X = Part.some (Nat.unpair n).2 from by rw [comp_eval _ _ _ _ hnExt]; simp [Code.eval])]; simp [Code.eval]
  have hsiv : selfInputSrc.eval X = Part.some (Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 + 1)) := by
    show (Code.pair n1Src mPlus1Src).eval X = _; exact pair_eval _ _ _ _ _ hn1v hm1v
  have hBv : bExtract.eval X = Part.some B := by
    show (Code.comp Code.right (Code.comp Code.left Code.left)).eval X = _; rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hsubA : (Code.right : Code).eval ec = Part.some (Nat.unpair ec).2 := by simp [UCode.enc, Code.eval, Nat.unpair_pair]
  have haread : (readerGen Code.right (Code.comp Code.left Code.right) nExtract).eval X = Part.some (spec (cfgRank E B k (Nat.unpair ec).2 n)) := by
    have := reader_gen_correct Code.right (Code.comp Code.left Code.right) nExtract (Nat.unpair ec).2 k n E B N k n ec spec hsubA hk hnExt (by rw [hN]; exact cfgRank_lt_code E B k ec (Nat.unpair ec).2 n n (rfindSub_lt ec htag) hec hn)
    rwa [← hX] at this
  have hx : (Code.comp predCode (readerGen Code.right (Code.comp Code.left Code.right) nExtract)).eval X = Part.some (spec (cfgRank E B k (Nat.unpair ec).2 n) - 1) := by
    rw [comp_eval _ _ _ _ haread, eval_predCode, Nat.pred_eq_sub_one]
  have hisPosEoa : (Code.comp isPosCode (readerGen Code.right (Code.comp Code.left Code.right) nExtract)).eval X = Part.some (if spec (cfgRank E B k (Nat.unpair ec).2 n) = 0 then 0 else 1) := by
    rw [comp_eval _ _ _ _ haread, eval_isPosCode]
  have hizX : (Code.comp isZeroCode (Code.comp predCode (readerGen Code.right (Code.comp Code.left Code.right) nExtract))).eval X = Part.some (if spec (cfgRank E B k (Nat.unpair ec).2 n) - 1 = 0 then 1 else 0) := by
    rw [comp_eval _ _ _ _ hx, eval_isZeroCode]
  have hipX : (Code.comp isPosCode (Code.comp predCode (readerGen Code.right (Code.comp Code.left Code.right) nExtract))).eval X = Part.some (if spec (cfgRank E B k (Nat.unpair ec).2 n) - 1 = 0 then 0 else 1) := by
    rw [comp_eval _ _ _ _ hx, eval_isPosCode]
  have hguardSelf : (Code.comp leqIndicatorCode (Code.pair selfInputSrc bExtract)).eval X = Part.some (if Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 + 1) ≤ B then 1 else 0) := by
    rw [comp_pair_eval _ _ _ _ _ _ hsiv hBv, eval_leqIndicatorCode]
  have hselfG : (Code.comp mulCode (Code.pair (Code.comp leqIndicatorCode (Code.pair selfInputSrc bExtract)) (readerGen idCode kPredSrc selfInputSrc))).eval X = Part.some (if Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 + 1) ≤ B then spec (cfgRank E B (k - 1) ec (Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 + 1))) else 0) := by
    by_cases hsB : Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 + 1) ≤ B
    · have hsr := self_lower_reader kPredSrc selfInputSrc (k-1) (Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 + 1)) E B N k n ec spec hkpv hsiv (by omega) hec hsB hN
      rw [← hX] at hsr; rw [comp_pair_eval _ _ _ _ _ _ hguardSelf hsr, eval_mulCode, if_pos hsB, if_pos hsB, one_mul]
    · have hraw := readerGen_some idCode kPredSrc selfInputSrc ec (k-1) (Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 + 1)) E B N k n ec (tableList spec N) (eval_idCode _) hkpv hsiv
      rw [← hX] at hraw; rw [comp_pair_eval _ _ _ _ _ _ hguardSelf hraw, eval_mulCode, if_neg hsB, if_neg hsB, zero_mul]
  have hthen : (Code.comp mulCode (Code.pair (Code.comp isZeroCode (Code.comp predCode (readerGen Code.right (Code.comp Code.left Code.right) nExtract))) mPlus1Src)).eval X = Part.some ((if spec (cfgRank E B k (Nat.unpair ec).2 n) - 1 = 0 then 1 else 0) * ((Nat.unpair n).2 + 1)) := by
    rw [comp_pair_eval _ _ _ _ _ _ hizX hm1v, eval_mulCode]
  have helse : (Code.comp mulCode (Code.pair (Code.comp isPosCode (Code.comp predCode (readerGen Code.right (Code.comp Code.left Code.right) nExtract))) (Code.comp mulCode (Code.pair (Code.comp leqIndicatorCode (Code.pair selfInputSrc bExtract)) (readerGen idCode kPredSrc selfInputSrc))))).eval X = Part.some ((if spec (cfgRank E B k (Nat.unpair ec).2 n) - 1 = 0 then 0 else 1) * (if Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 + 1) ≤ B then spec (cfgRank E B (k - 1) ec (Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 + 1))) else 0)) := by
    rw [comp_pair_eval _ _ _ _ _ _ hipX hselfG, eval_mulCode]
  have hcond : (Code.comp addCode (Code.pair (Code.comp mulCode (Code.pair (Code.comp isZeroCode (Code.comp predCode (readerGen Code.right (Code.comp Code.left Code.right) nExtract))) mPlus1Src)) (Code.comp mulCode (Code.pair (Code.comp isPosCode (Code.comp predCode (readerGen Code.right (Code.comp Code.left Code.right) nExtract))) (Code.comp mulCode (Code.pair (Code.comp leqIndicatorCode (Code.pair selfInputSrc bExtract)) (readerGen idCode kPredSrc selfInputSrc))))))).eval X = Part.some ((if spec (cfgRank E B k (Nat.unpair ec).2 n) - 1 = 0 then 1 else 0) * ((Nat.unpair n).2 + 1) + (if spec (cfgRank E B k (Nat.unpair ec).2 n) - 1 = 0 then 0 else 1) * (if Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 + 1) ≤ B then spec (cfgRank E B (k - 1) ec (Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 + 1))) else 0)) := by
    rw [comp_pair_eval _ _ _ _ _ _ hthen helse, eval_addCode]
  have hinner : (Code.comp mulCode (Code.pair (Code.comp isPosCode (readerGen Code.right (Code.comp Code.left Code.right) nExtract)) (Code.comp addCode (Code.pair (Code.comp mulCode (Code.pair (Code.comp isZeroCode (Code.comp predCode (readerGen Code.right (Code.comp Code.left Code.right) nExtract))) mPlus1Src)) (Code.comp mulCode (Code.pair (Code.comp isPosCode (Code.comp predCode (readerGen Code.right (Code.comp Code.left Code.right) nExtract))) (Code.comp mulCode (Code.pair (Code.comp leqIndicatorCode (Code.pair selfInputSrc bExtract)) (readerGen idCode kPredSrc selfInputSrc))))))))).eval X = Part.some ((if spec (cfgRank E B k (Nat.unpair ec).2 n) = 0 then 0 else 1) * ((if spec (cfgRank E B k (Nat.unpair ec).2 n) - 1 = 0 then 1 else 0) * ((Nat.unpair n).2 + 1) + (if spec (cfgRank E B k (Nat.unpair ec).2 n) - 1 = 0 then 0 else 1) * (if Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 + 1) ≤ B then spec (cfgRank E B (k - 1) ec (Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 + 1))) else 0))) := by
    rw [comp_pair_eval _ _ _ _ _ _ hisPosEoa hcond, eval_mulCode]
  have hguardN : (Code.comp leqIndicatorCode (Code.pair nExtract (Code.comp predCode (Code.comp Code.left Code.right)))).eval X = Part.some (if n ≤ k - 1 then 1 else 0) := by
    rw [comp_pair_eval _ _ _ _ _ _ hnExt hkpv, eval_leqIndicatorCode]
  show (Code.comp mulCode (Code.pair _ _)).eval X = _
  rw [comp_pair_eval _ _ _ _ _ _ hguardN hinner, eval_mulCode]

end PallLean.Paper93.DeepMath.PathB.KleeneUCode
#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.eval_rfindHandler_gen
