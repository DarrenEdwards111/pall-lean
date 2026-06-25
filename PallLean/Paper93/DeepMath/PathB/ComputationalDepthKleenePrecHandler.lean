import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleenePrecStep
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneEq
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneEncMono

/-!
# Kleene interpreter project — the `prec` handler (PROVED)

The third and most complex recursive handler.  `prec` is a `casesOn` on `n2 = (unpair n).2`, under the guard
`n ≤ k-1`:

  `[n ≤ k-1] · ( [n2=0] · (read a at n1)  +  [n2≠0] · step )`,

where `step` (`eval_precStep`) is itself a data-dependent `comp`-like with lower-fuel self-recursion and two
value-bound guards.  The additive selector matches `encode_prec_step`.  (Stated with `∃ stepval` carrying the
step value, which `hbody` will identify with `encodeOpt` of the recursive `evaln`.)

  `n2Src`, `precHandler`, `eval_precHandler`.

## What is proved (clean axioms, no `sorry`)

* `eval_precHandler`.

## Honest scope

The `prec` handler (Code-level cased value).  `rfind'`, the body, `spec`/`hbody`, the interpreter, and the
runtime remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode

open Nat.Partrec
open PallLean.Paper93.DeepMath.PathB.KleeneList (encodeList)
open PallLean.Paper93.DeepMath.PathB.KleeneRank (cfgRank cfgRank_lt_code)

/-- `n2 = (unpair n).2` (the `prec` recursion variable). -/
noncomputable def n2Src : Code := Code.comp Code.right nExtract

/-- The `prec` handler: guard × (`casesOn n2` selector over base/step). -/
noncomputable def precHandler : Code :=
  Code.comp mulCode (Code.pair
    (Code.comp leqIndicatorCode (Code.pair nExtract (Code.comp predCode (Code.comp Code.left Code.right))))
    (Code.comp addCode (Code.pair
      (Code.comp mulCode (Code.pair (Code.comp isZeroCode n2Src) (readerGen fstSubCode (Code.comp Code.left Code.right) n1Src)))
      (Code.comp mulCode (Code.pair (Code.comp isPosCode n2Src) precStepCode)))))

theorem eval_precHandler (E B N k n : ℕ) (a b : UCode) (spec : ℕ → ℕ)
    (hec : (UCode.prec a b).enc ≤ E) (hn : n ≤ B) (hN : N = cfgRank E B k (UCode.prec a b).enc n) (hk1 : 1 ≤ k) :
    ∃ stepval, precHandler.eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N)))) (Nat.pair k (Nat.pair (UCode.prec a b).enc n)))
      = Part.some ((if n ≤ k - 1 then 1 else 0)
          * ((if (Nat.unpair n).2 = 0 then 1 else 0) * spec (cfgRank E B k a.enc (Nat.unpair n).1)
             + (if (Nat.unpair n).2 = 0 then 0 else 1) * stepval)) := by
  set X := Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N)))) (Nat.pair k (Nat.pair (UCode.prec a b).enc n)) with hX
  obtain ⟨ev, cmp, hevdef, hcmpdef, hstep⟩ := eval_precStep E B N k n a b spec hec hn hN hk1
  rw [← hX] at hstep
  refine ⟨(if ev = 0 then 0 else 1) * (if cmp ≤ B then spec (cfgRank E B k b.enc cmp) else 0), ?_⟩
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
  have hbase : (readerGen fstSubCode (Code.comp Code.left Code.right) n1Src).eval X = Part.some (spec (cfgRank E B k a.enc (Nat.unpair n).1)) := by
    have := reader_gen_correct fstSubCode (Code.comp Code.left Code.right) n1Src a.enc k (Nat.unpair n).1 E B N k n (UCode.prec a b).enc spec (eval_fstSub_prec a b) hk hn1v (by rw [hN]; exact cfgRank_lt_code E B k (UCode.prec a b).enc a.enc n (Nat.unpair n).1 (enc_lt_prec_left a b) hec (le_trans (Nat.unpair_left_le n) hn))
    rwa [← hX] at this
  have hizN2 : (Code.comp isZeroCode n2Src).eval X = Part.some (if (Nat.unpair n).2 = 0 then 1 else 0) := by
    rw [comp_eval _ _ _ _ hn2v, eval_isZeroCode]
  have hipN2 : (Code.comp isPosCode n2Src).eval X = Part.some (if (Nat.unpair n).2 = 0 then 0 else 1) := by
    rw [comp_eval _ _ _ _ hn2v, eval_isPosCode]
  have ht1 : (Code.comp mulCode (Code.pair (Code.comp isZeroCode n2Src) (readerGen fstSubCode (Code.comp Code.left Code.right) n1Src))).eval X = Part.some ((if (Nat.unpair n).2 = 0 then 1 else 0) * spec (cfgRank E B k a.enc (Nat.unpair n).1)) := by
    rw [comp_pair_eval _ _ _ _ _ _ hizN2 hbase, eval_mulCode]
  have ht2 : (Code.comp mulCode (Code.pair (Code.comp isPosCode n2Src) precStepCode)).eval X = Part.some ((if (Nat.unpair n).2 = 0 then 0 else 1) * ((if ev = 0 then 0 else 1) * (if cmp ≤ B then spec (cfgRank E B k b.enc cmp) else 0))) := by
    rw [comp_pair_eval _ _ _ _ _ _ hipN2 hstep, eval_mulCode]
  have hsel : (Code.comp addCode (Code.pair (Code.comp mulCode (Code.pair (Code.comp isZeroCode n2Src) (readerGen fstSubCode (Code.comp Code.left Code.right) n1Src))) (Code.comp mulCode (Code.pair (Code.comp isPosCode n2Src) precStepCode)))).eval X = Part.some ((if (Nat.unpair n).2 = 0 then 1 else 0) * spec (cfgRank E B k a.enc (Nat.unpair n).1) + (if (Nat.unpair n).2 = 0 then 0 else 1) * ((if ev = 0 then 0 else 1) * (if cmp ≤ B then spec (cfgRank E B k b.enc cmp) else 0))) := by
    rw [comp_pair_eval _ _ _ _ _ _ ht1 ht2, eval_addCode]
  show (Code.comp mulCode (Code.pair _ _)).eval X = _
  rw [comp_pair_eval _ _ _ _ _ _ hguard hsel, eval_mulCode]

end PallLean.Paper93.DeepMath.PathB.KleeneUCode

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.eval_precHandler
