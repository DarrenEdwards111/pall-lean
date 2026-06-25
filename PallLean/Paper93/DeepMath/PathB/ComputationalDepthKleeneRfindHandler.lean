import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleenePrecSelf
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneReaderGenSome
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneReaderGen
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneEq
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneEncMono

/-!
# Kleene interpreter project — the `rfind'` handler (PROVED)

The fourth (last) recursive handler.  `rfind' a` at `n` reads `x = evaln k a n` (the a-call input is
`pair (unpair n).1 (unpair n).2 = n`, so it is read at `n` directly — no extra guard, `n ≤ B`), then branches:
if `x = 0` returns `(unpair n).2`, else recurses on itself at fuel `k-1` with input `pair (unpair n).1
((unpair n).2 + 1)` (guarded by `[· ≤ B]`).  Under the guard `n ≤ k-1`:

  `[n≤k-1] · isPos(eoa) · ( [eoa-1=0]·(m+1) + [eoa-1≠0]·(guarded self-read) )`,

matching `encode_rfind_step` (`m = (unpair n).2`, `eoa = encodeOpt (evaln k a n)`).

  `mPlus1Src`, `selfInputSrc`, `rfindHandler`, `eval_rfindHandler`.

## What is proved (clean axioms, no `sorry`)

* `eval_rfindHandler`.

## Honest scope

The `rfind'` handler — completing all eight handlers.  The body (`mkDispatch` over the 8 + fuel-0), `spec`/
`hbody`, the interpreter, and the runtime remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode

open Nat.Partrec
open PallLean.Paper93.DeepMath.PathB.KleeneList (encodeList)
open PallLean.Paper93.DeepMath.PathB.KleeneRank (cfgRank cfgRank_lt_code cfgRank_lt_fuel)

/-- `m + 1 = (unpair n).2 + 1` (the `rfind'` search step). -/
noncomputable def mPlus1Src : Code := Code.comp Code.succ (Code.comp Code.right nExtract)
/-- The `rfind'` self-recursion input `pair (unpair n).1 ((unpair n).2 + 1)`. -/
noncomputable def selfInputSrc : Code := Code.pair n1Src mPlus1Src

/-- The `rfind'` handler. -/
noncomputable def rfindHandler : Code :=
  Code.comp mulCode (Code.pair
    (Code.comp leqIndicatorCode (Code.pair nExtract (Code.comp predCode (Code.comp Code.left Code.right))))
    (Code.comp mulCode (Code.pair (Code.comp isPosCode (readerGen Code.right (Code.comp Code.left Code.right) nExtract))
      (Code.comp addCode (Code.pair
        (Code.comp mulCode (Code.pair (Code.comp isZeroCode (Code.comp predCode (readerGen Code.right (Code.comp Code.left Code.right) nExtract))) mPlus1Src))
        (Code.comp mulCode (Code.pair (Code.comp isPosCode (Code.comp predCode (readerGen Code.right (Code.comp Code.left Code.right) nExtract)))
          (Code.comp mulCode (Code.pair (Code.comp leqIndicatorCode (Code.pair selfInputSrc bExtract)) (readerGen idCode kPredSrc selfInputSrc))))))))))

theorem eval_rfindHandler (E B N k n : ℕ) (a : UCode) (spec : ℕ → ℕ)
    (hec : (UCode.rfind' a).enc ≤ E) (hn : n ≤ B) (hN : N = cfgRank E B k (UCode.rfind' a).enc n) (hk1 : 1 ≤ k) :
    rfindHandler.eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N)))) (Nat.pair k (Nat.pair (UCode.rfind' a).enc n)))
      = Part.some ((if n ≤ k - 1 then 1 else 0)
          * ((if spec (cfgRank E B k a.enc n) = 0 then 0 else 1)
             * ((if spec (cfgRank E B k a.enc n) - 1 = 0 then 1 else 0) * ((Nat.unpair n).2 + 1)
                + (if spec (cfgRank E B k a.enc n) - 1 = 0 then 0 else 1)
                  * (if Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 + 1) ≤ B
                      then spec (cfgRank E B (k - 1) (UCode.rfind' a).enc (Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 + 1))) else 0)))) := by
  set X := Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N)))) (Nat.pair k (Nat.pair (UCode.rfind' a).enc n)) with hX
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
  have hsubA : (Code.right : Code).eval (UCode.rfind' a).enc = Part.some a.enc := by simp [UCode.enc, Code.eval, Nat.unpair_pair]
  have haread : (readerGen Code.right (Code.comp Code.left Code.right) nExtract).eval X = Part.some (spec (cfgRank E B k a.enc n)) := by
    have := reader_gen_correct Code.right (Code.comp Code.left Code.right) nExtract a.enc k n E B N k n (UCode.rfind' a).enc spec hsubA hk hnExt (by rw [hN]; exact cfgRank_lt_code E B k (UCode.rfind' a).enc a.enc n n (enc_lt_rfind' a) hec hn)
    rwa [← hX] at this
  have hx : (Code.comp predCode (readerGen Code.right (Code.comp Code.left Code.right) nExtract)).eval X = Part.some (spec (cfgRank E B k a.enc n) - 1) := by
    rw [comp_eval _ _ _ _ haread, eval_predCode, Nat.pred_eq_sub_one]
  have hisPosEoa : (Code.comp isPosCode (readerGen Code.right (Code.comp Code.left Code.right) nExtract)).eval X = Part.some (if spec (cfgRank E B k a.enc n) = 0 then 0 else 1) := by
    rw [comp_eval _ _ _ _ haread, eval_isPosCode]
  have hizX : (Code.comp isZeroCode (Code.comp predCode (readerGen Code.right (Code.comp Code.left Code.right) nExtract))).eval X = Part.some (if spec (cfgRank E B k a.enc n) - 1 = 0 then 1 else 0) := by
    rw [comp_eval _ _ _ _ hx, eval_isZeroCode]
  have hipX : (Code.comp isPosCode (Code.comp predCode (readerGen Code.right (Code.comp Code.left Code.right) nExtract))).eval X = Part.some (if spec (cfgRank E B k a.enc n) - 1 = 0 then 0 else 1) := by
    rw [comp_eval _ _ _ _ hx, eval_isPosCode]
  have hguardSelf : (Code.comp leqIndicatorCode (Code.pair selfInputSrc bExtract)).eval X = Part.some (if Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 + 1) ≤ B then 1 else 0) := by
    rw [comp_pair_eval _ _ _ _ _ _ hsiv hBv, eval_leqIndicatorCode]
  have hselfG : (Code.comp mulCode (Code.pair (Code.comp leqIndicatorCode (Code.pair selfInputSrc bExtract)) (readerGen idCode kPredSrc selfInputSrc))).eval X = Part.some (if Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 + 1) ≤ B then spec (cfgRank E B (k - 1) (UCode.rfind' a).enc (Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 + 1))) else 0) := by
    by_cases hsB : Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 + 1) ≤ B
    · have hsr := self_lower_reader kPredSrc selfInputSrc (k-1) (Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 + 1)) E B N k n (UCode.rfind' a).enc spec hkpv hsiv (by omega) hec hsB hN
      rw [← hX] at hsr; rw [comp_pair_eval _ _ _ _ _ _ hguardSelf hsr, eval_mulCode, if_pos hsB, if_pos hsB, one_mul]
    · have hraw := readerGen_some idCode kPredSrc selfInputSrc (UCode.rfind' a).enc (k-1) (Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 + 1)) E B N k n (UCode.rfind' a).enc (tableList spec N) (eval_idCode _) hkpv hsiv
      rw [← hX] at hraw; rw [comp_pair_eval _ _ _ _ _ _ hguardSelf hraw, eval_mulCode, if_neg hsB, if_neg hsB, zero_mul]
  have hthen : (Code.comp mulCode (Code.pair (Code.comp isZeroCode (Code.comp predCode (readerGen Code.right (Code.comp Code.left Code.right) nExtract))) mPlus1Src)).eval X = Part.some ((if spec (cfgRank E B k a.enc n) - 1 = 0 then 1 else 0) * ((Nat.unpair n).2 + 1)) := by
    rw [comp_pair_eval _ _ _ _ _ _ hizX hm1v, eval_mulCode]
  have helse : (Code.comp mulCode (Code.pair (Code.comp isPosCode (Code.comp predCode (readerGen Code.right (Code.comp Code.left Code.right) nExtract))) (Code.comp mulCode (Code.pair (Code.comp leqIndicatorCode (Code.pair selfInputSrc bExtract)) (readerGen idCode kPredSrc selfInputSrc))))).eval X = Part.some ((if spec (cfgRank E B k a.enc n) - 1 = 0 then 0 else 1) * (if Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 + 1) ≤ B then spec (cfgRank E B (k - 1) (UCode.rfind' a).enc (Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 + 1))) else 0)) := by
    rw [comp_pair_eval _ _ _ _ _ _ hipX hselfG, eval_mulCode]
  have hcond : (Code.comp addCode (Code.pair (Code.comp mulCode (Code.pair (Code.comp isZeroCode (Code.comp predCode (readerGen Code.right (Code.comp Code.left Code.right) nExtract))) mPlus1Src)) (Code.comp mulCode (Code.pair (Code.comp isPosCode (Code.comp predCode (readerGen Code.right (Code.comp Code.left Code.right) nExtract))) (Code.comp mulCode (Code.pair (Code.comp leqIndicatorCode (Code.pair selfInputSrc bExtract)) (readerGen idCode kPredSrc selfInputSrc))))))).eval X = Part.some ((if spec (cfgRank E B k a.enc n) - 1 = 0 then 1 else 0) * ((Nat.unpair n).2 + 1) + (if spec (cfgRank E B k a.enc n) - 1 = 0 then 0 else 1) * (if Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 + 1) ≤ B then spec (cfgRank E B (k - 1) (UCode.rfind' a).enc (Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 + 1))) else 0)) := by
    rw [comp_pair_eval _ _ _ _ _ _ hthen helse, eval_addCode]
  have hinner : (Code.comp mulCode (Code.pair (Code.comp isPosCode (readerGen Code.right (Code.comp Code.left Code.right) nExtract)) (Code.comp addCode (Code.pair (Code.comp mulCode (Code.pair (Code.comp isZeroCode (Code.comp predCode (readerGen Code.right (Code.comp Code.left Code.right) nExtract))) mPlus1Src)) (Code.comp mulCode (Code.pair (Code.comp isPosCode (Code.comp predCode (readerGen Code.right (Code.comp Code.left Code.right) nExtract))) (Code.comp mulCode (Code.pair (Code.comp leqIndicatorCode (Code.pair selfInputSrc bExtract)) (readerGen idCode kPredSrc selfInputSrc)))))))).eval X = Part.some ((if spec (cfgRank E B k a.enc n) = 0 then 0 else 1) * ((if spec (cfgRank E B k a.enc n) - 1 = 0 then 1 else 0) * ((Nat.unpair n).2 + 1) + (if spec (cfgRank E B k a.enc n) - 1 = 0 then 0 else 1) * (if Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 + 1) ≤ B then spec (cfgRank E B (k - 1) (UCode.rfind' a).enc (Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 + 1))) else 0))) := by
    rw [comp_pair_eval _ _ _ _ _ _ hisPosEoa hcond, eval_mulCode]
  have hguardN : (Code.comp leqIndicatorCode (Code.pair nExtract (Code.comp predCode (Code.comp Code.left Code.right)))).eval X = Part.some (if n ≤ k - 1 then 1 else 0) := by
    rw [comp_pair_eval _ _ _ _ _ _ hnExt hkpv, eval_leqIndicatorCode]
  show (Code.comp mulCode (Code.pair _ _)).eval X = _
  rw [comp_pair_eval _ _ _ _ _ _ hguardN hinner, eval_mulCode]

end PallLean.Paper93.DeepMath.PathB.KleeneUCode

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.eval_rfindHandler
