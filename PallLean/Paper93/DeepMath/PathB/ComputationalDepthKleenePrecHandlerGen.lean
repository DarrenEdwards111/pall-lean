import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleenePrecSelf
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleenePrecStep
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleenePrecHandler
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneReaderGen
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneGenExtract

/-! # Kleene interpreter project — the generic `prec` handler (PROVED)

The `prec` handler for arbitrary `ec` (tag-6 path).  `eprecG`'s self-read uses `idCode` (reads `ec` itself at
lower fuel, no sub-extraction) so it generalises by simply replacing `(prec a b).enc` with `ec`.  The base
read (`fstSubCode`) and step `b`-read (`sndSubCode`) use the general extraction (`eval_fstSub_gen`+`fstSub_lt`,
`eval_sndSub_gen`+`sndSub_lt`).  `eval_eprecG_gen`, `eval_precStep_gen`, `eval_precHandler_gen`.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`. -/

open Nat.Partrec
open PallLean.Paper93.DeepMath.PathB.KleeneUCode
open PallLean.Paper93.DeepMath.PathB.KleeneList (encodeList)
open PallLean.Paper93.DeepMath.PathB.KleeneRank (cfgRank cfgRank_lt_code)
namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode

theorem eval_eprecG_gen (E B N k n ec : ℕ) (spec : ℕ → ℕ)
    (hec : ec ≤ E) (hn : n ≤ B) (hN : N = cfgRank E B k ec n) (hk1 : 1 ≤ k) :
    eprecGCode.eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N)))) (Nat.pair k (Nat.pair ec n)))
      = Part.some (if Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 - 1) ≤ B
          then spec (cfgRank E B (k - 1) ec (Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 - 1))) else 0) := by
  set X := Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N)))) (Nat.pair k (Nat.pair ec n)) with hX
  have hp : pairN1MSrc.eval X = Part.some (Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 - 1)) := by
    refine pair_eval _ _ _ _ _ ?_ ?_
    · show (Code.comp Code.left nExtract).eval X = _; rw [hX]; simp [nExtract, Code.eval, Nat.unpair_pair]
    · show (Code.comp predCode (Code.comp Code.right nExtract)).eval X = _
      rw [comp_eval _ _ _ _ (show (Code.comp Code.right nExtract).eval X = Part.some (Nat.unpair n).2 from by rw [hX]; simp [nExtract, Code.eval, Nat.unpair_pair]), eval_predCode, Nat.pred_eq_sub_one]
  have hBv : bExtract.eval X = Part.some B := by
    show (Code.comp Code.right (Code.comp Code.left Code.left)).eval X = _; rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hkp : kPredSrc.eval X = Part.some (k - 1) := by
    show (Code.comp predCode (Code.comp Code.left Code.right)).eval X = _
    rw [comp_eval _ _ _ _ (show (Code.comp Code.left Code.right).eval X = Part.some k from by rw [hX]; simp [Code.eval, Nat.unpair_pair]), eval_predCode, Nat.pred_eq_sub_one]
  have hleq : (Code.comp leqIndicatorCode (Code.pair pairN1MSrc bExtract)).eval X = Part.some (if Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 - 1) ≤ B then 1 else 0) := by
    rw [comp_pair_eval _ _ _ _ _ _ hp hBv, eval_leqIndicatorCode]
  show (Code.comp mulCode (Code.pair _ _)).eval X = _
  by_cases hb : Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 - 1) ≤ B
  · have hself := self_lower_reader kPredSrc pairN1MSrc (k-1) (Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 - 1)) E B N k n ec spec hkp hp (by omega) hec hb hN
    rw [← hX] at hself
    rw [comp_pair_eval _ _ _ _ _ _ hleq hself, eval_mulCode, if_pos hb, if_pos hb, one_mul]
  · have hraw := readerGen_some idCode kPredSrc pairN1MSrc ec (k-1) (Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 - 1)) E B N k n ec (tableList spec N) (eval_idCode _) hkp hp
    rw [← hX] at hraw
    rw [comp_pair_eval _ _ _ _ _ _ hleq hraw, eval_mulCode, if_neg hb, if_neg hb, zero_mul]

theorem eval_precStep_gen (E B N k n ec : ℕ) (spec : ℕ → ℕ)
    (htag : 1 ≤ (Nat.unpair ec).1) (hec : ec ≤ E) (hn : n ≤ B) (hN : N = cfgRank E B k ec n) (hk1 : 1 ≤ k) :
    ∃ ev cmp,
      ev = (if Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 - 1) ≤ B
          then spec (cfgRank E B (k - 1) ec (Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 - 1))) else 0)
      ∧ cmp = Nat.pair (Nat.unpair n).1 (Nat.pair ((Nat.unpair n).2 - 1) (ev - 1))
      ∧ precStepCode.eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N)))) (Nat.pair k (Nat.pair ec n)))
        = Part.some ((if ev = 0 then 0 else 1) * (if cmp ≤ B then spec (cfgRank E B k (Nat.unpair (Nat.unpair ec).2).2 cmp) else 0)) := by
  set X := Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N)))) (Nat.pair k (Nat.pair ec n)) with hX
  have heprec := eval_eprecG_gen E B N k n ec spec hec hn hN hk1
  rw [← hX] at heprec
  set ev := (if Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 - 1) ≤ B
          then spec (cfgRank E B (k - 1) ec (Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 - 1))) else 0) with hev
  refine ⟨ev, Nat.pair (Nat.unpair n).1 (Nat.pair ((Nat.unpair n).2 - 1) (ev - 1)), rfl, rfl, ?_⟩
  set cmp := Nat.pair (Nat.unpair n).1 (Nat.pair ((Nat.unpair n).2 - 1) (ev - 1)) with hcmp
  have hn1 : n1Src.eval X = Part.some (Nat.unpair n).1 := by
    show (Code.comp Code.left nExtract).eval X = _; rw [hX]; simp [nExtract, Code.eval, Nat.unpair_pair]
  have hmv : mSrc.eval X = Part.some ((Nat.unpair n).2 - 1) := by
    show (Code.comp predCode (Code.comp Code.right nExtract)).eval X = _
    rw [comp_eval _ _ _ _ (show (Code.comp Code.right nExtract).eval X = Part.some (Nat.unpair n).2 from by rw [hX]; simp [nExtract, Code.eval, Nat.unpair_pair]), eval_predCode, Nat.pred_eq_sub_one]
  have hiv : iSrc.eval X = Part.some (ev - 1) := by
    show (Code.comp predCode eprecGCode).eval X = _; rw [comp_eval _ _ _ _ heprec, eval_predCode, Nat.pred_eq_sub_one]
  have hcmpv : compositeSrc.eval X = Part.some cmp := by
    show (Code.pair n1Src (Code.pair mSrc iSrc)).eval X = _
    exact pair_eval _ _ _ _ _ hn1 (pair_eval _ _ _ _ _ hmv hiv)
  have hBv : bExtract.eval X = Part.some B := by
    show (Code.comp Code.right (Code.comp Code.left Code.left)).eval X = _; rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hk : (Code.comp Code.left Code.right).eval X = Part.some k := by rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hisPos : (Code.comp isPosCode eprecGCode).eval X = Part.some (if ev = 0 then 0 else 1) := by
    rw [comp_eval _ _ _ _ heprec, eval_isPosCode]
  have hleqC : (Code.comp leqIndicatorCode (Code.pair compositeSrc bExtract)).eval X = Part.some (if cmp ≤ B then 1 else 0) := by
    rw [comp_pair_eval _ _ _ _ _ _ hcmpv hBv, eval_leqIndicatorCode]
  have hinner : (Code.comp mulCode (Code.pair (Code.comp leqIndicatorCode (Code.pair compositeSrc bExtract)) (readerGen sndSubCode (Code.comp Code.left Code.right) compositeSrc))).eval X = Part.some (if cmp ≤ B then spec (cfgRank E B k (Nat.unpair (Nat.unpair ec).2).2 cmp) else 0) := by
    by_cases hcB : cmp ≤ B
    · have hbr := reader_gen_correct sndSubCode (Code.comp Code.left Code.right) compositeSrc (Nat.unpair (Nat.unpair ec).2).2 k cmp E B N k n ec spec (eval_sndSub_gen ec) hk hcmpv (by rw [hN]; exact cfgRank_lt_code E B k ec (Nat.unpair (Nat.unpair ec).2).2 n cmp (sndSub_lt ec htag) hec hcB)
      rw [comp_pair_eval _ _ _ _ _ _ hleqC hbr, eval_mulCode, if_pos hcB, if_pos hcB, one_mul]
    · have hbr := readerGen_some sndSubCode (Code.comp Code.left Code.right) compositeSrc (Nat.unpair (Nat.unpair ec).2).2 k cmp E B N k n ec (tableList spec N) (eval_sndSub_gen ec) hk hcmpv
      rw [comp_pair_eval _ _ _ _ _ _ hleqC hbr, eval_mulCode, if_neg hcB, if_neg hcB, zero_mul]
  show (Code.comp mulCode (Code.pair _ _)).eval X = _
  rw [comp_pair_eval _ _ _ _ _ _ hisPos hinner, eval_mulCode]

theorem eval_precHandler_gen (E B N k n ec : ℕ) (spec : ℕ → ℕ)
    (htag : 1 ≤ (Nat.unpair ec).1) (hec : ec ≤ E) (hn : n ≤ B) (hN : N = cfgRank E B k ec n) (hk1 : 1 ≤ k) :
    ∃ stepval, precHandler.eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N)))) (Nat.pair k (Nat.pair ec n)))
      = Part.some ((if n ≤ k - 1 then 1 else 0)
          * ((if (Nat.unpair n).2 = 0 then 1 else 0) * spec (cfgRank E B k (Nat.unpair (Nat.unpair ec).2).1 (Nat.unpair n).1)
             + (if (Nat.unpair n).2 = 0 then 0 else 1) * stepval)) := by
  set X := Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N)))) (Nat.pair k (Nat.pair ec n)) with hX
  obtain ⟨ev, cmp, hevdef, hcmpdef, hstep⟩ := eval_precStep_gen E B N k n ec spec htag hec hn hN hk1
  rw [← hX] at hstep
  refine ⟨(if ev = 0 then 0 else 1) * (if cmp ≤ B then spec (cfgRank E B k (Nat.unpair (Nat.unpair ec).2).2 cmp) else 0), ?_⟩
  have hnExt : nExtract.eval X = Part.some n := by
    show (Code.comp Code.right (Code.comp Code.right Code.right)).eval X = _; rw [hX]; simp [nExtract, Code.eval, Nat.unpair_pair]
  have hn2v : n2Src.eval X = Part.some (Nat.unpair n).2 := by
    show (Code.comp Code.right nExtract).eval X = _; rw [comp_eval _ _ _ _ hnExt]; simp [Code.eval]
  have hn1v : n1Src.eval X = Part.some (Nat.unpair n).1 := by
    show (Code.comp Code.left nExtract).eval X = _; rw [comp_eval _ _ _ _ hnExt]; simp [Code.eval]
  have hkpv : (Code.comp predCode (Code.comp Code.left Code.right)).eval X = Part.some (k - 1) := by
    rw [comp_eval _ _ _ _ (show (Code.comp Code.left Code.right).eval X = Part.some k from by rw [hX]; simp [Code.eval, Nat.unpair_pair]), eval_predCode, Nat.pred_eq_sub_one]
  have hk : (Code.comp Code.left Code.right).eval X = Part.some k := by rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hguard : (Code.comp leqIndicatorCode (Code.pair nExtract (Code.comp predCode (Code.comp Code.left Code.right)))).eval X = Part.some (if n ≤ k - 1 then 1 else 0) := by
    rw [comp_pair_eval _ _ _ _ _ _ hnExt hkpv, eval_leqIndicatorCode]
  have hbase : (readerGen fstSubCode (Code.comp Code.left Code.right) n1Src).eval X = Part.some (spec (cfgRank E B k (Nat.unpair (Nat.unpair ec).2).1 (Nat.unpair n).1)) := by
    have := reader_gen_correct fstSubCode (Code.comp Code.left Code.right) n1Src (Nat.unpair (Nat.unpair ec).2).1 k (Nat.unpair n).1 E B N k n ec spec (eval_fstSub_gen ec) hk hn1v (by rw [hN]; exact cfgRank_lt_code E B k ec (Nat.unpair (Nat.unpair ec).2).1 n (Nat.unpair n).1 (fstSub_lt ec htag) hec (le_trans (Nat.unpair_left_le n) hn))
    rwa [← hX] at this
  have hizN2 : (Code.comp isZeroCode n2Src).eval X = Part.some (if (Nat.unpair n).2 = 0 then 1 else 0) := by
    rw [comp_eval _ _ _ _ hn2v, eval_isZeroCode]
  have hipN2 : (Code.comp isPosCode n2Src).eval X = Part.some (if (Nat.unpair n).2 = 0 then 0 else 1) := by
    rw [comp_eval _ _ _ _ hn2v, eval_isPosCode]
  have ht1 : (Code.comp mulCode (Code.pair (Code.comp isZeroCode n2Src) (readerGen fstSubCode (Code.comp Code.left Code.right) n1Src))).eval X = Part.some ((if (Nat.unpair n).2 = 0 then 1 else 0) * spec (cfgRank E B k (Nat.unpair (Nat.unpair ec).2).1 (Nat.unpair n).1)) := by
    rw [comp_pair_eval _ _ _ _ _ _ hizN2 hbase, eval_mulCode]
  have ht2 : (Code.comp mulCode (Code.pair (Code.comp isPosCode n2Src) precStepCode)).eval X = Part.some ((if (Nat.unpair n).2 = 0 then 0 else 1) * ((if ev = 0 then 0 else 1) * (if cmp ≤ B then spec (cfgRank E B k (Nat.unpair (Nat.unpair ec).2).2 cmp) else 0))) := by
    rw [comp_pair_eval _ _ _ _ _ _ hipN2 hstep, eval_mulCode]
  have hsel : (Code.comp addCode (Code.pair (Code.comp mulCode (Code.pair (Code.comp isZeroCode n2Src) (readerGen fstSubCode (Code.comp Code.left Code.right) n1Src))) (Code.comp mulCode (Code.pair (Code.comp isPosCode n2Src) precStepCode)))).eval X = Part.some ((if (Nat.unpair n).2 = 0 then 1 else 0) * spec (cfgRank E B k (Nat.unpair (Nat.unpair ec).2).1 (Nat.unpair n).1) + (if (Nat.unpair n).2 = 0 then 0 else 1) * ((if ev = 0 then 0 else 1) * (if cmp ≤ B then spec (cfgRank E B k (Nat.unpair (Nat.unpair ec).2).2 cmp) else 0))) := by
    rw [comp_pair_eval _ _ _ _ _ _ ht1 ht2, eval_addCode]
  show (Code.comp mulCode (Code.pair _ _)).eval X = _
  rw [comp_pair_eval _ _ _ _ _ _ hguard hsel, eval_mulCode]

end PallLean.Paper93.DeepMath.PathB.KleeneUCode
#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.eval_precHandler_gen
