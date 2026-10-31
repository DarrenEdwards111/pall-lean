import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneSelfReader
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneReaderGenSome
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneIndicators
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneDispatch

/-!
# Kleene interpreter project — `prec` guarded self-read (PROVED)

`prec`'s step recurses on itself at fuel `k-1` with input `pair n1 m` (`n1 = (unpair n).1`, `m = (unpair n).2
- 1`).  That input can exceed `B`, so the read is guarded by `[pair n1 m ≤ B]`.  `eval_eprecG` computes the
guarded self-read `eprec`:

  `= if pair n1 m ≤ B then spec (cfgRank E B (k-1) (prec a b).enc (pair n1 m)) else 0`.

The `≤ B` branch uses `self_lower_reader` (reads the same code at lower fuel via `idCode` + `cfgRank_lt_fuel`);
the `> B` branch uses the raw `readerGen_some`, zeroed by the guard.  This also fixes the shared source codes
(`nExtract`, `n1Src`, `mSrc`, `pairN1MSrc`, `kPredSrc`, `bExtract`) used by the rest of the `prec` step.

## What is proved (clean axioms, no `sorry`)

* `eval_eprecG` (+ the source/`Code` definitions).

## Honest scope

`prec`'s guarded self-read.  The `prec` `b`-read at the composite, the `casesOn` assembly, `rfind'`, the body,
the interpreter, and the runtime remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode

open Nat.Partrec
open PallLean.Paper93.DeepMath.PathB.KleeneList (encodeList)
open PallLean.Paper93.DeepMath.PathB.KleeneRank (cfgRank)

/-- `n`-extractor from the handler bundle. -/
noncomputable def nExtract : Code := Code.comp Code.right (Code.comp Code.right Code.right)
/-- `n1 = (unpair n).1`. -/
noncomputable def n1Src : Code := Code.comp Code.left nExtract
/-- `m = (unpair n).2 - 1`. -/
noncomputable def mSrc : Code := Code.comp predCode (Code.comp Code.right nExtract)
/-- `pair n1 m` (the `prec` self-recursion input). -/
noncomputable def pairN1MSrc : Code := Code.pair n1Src mSrc
/-- `k - 1` (the lower fuel). -/
noncomputable def kPredSrc : Code := Code.comp predCode (Code.comp Code.left Code.right)
/-- `B` from the bundle. -/
noncomputable def bExtract : Code := Code.comp Code.right (Code.comp Code.left Code.left)

/-- The guarded `prec` self-read. -/
noncomputable def eprecGCode : Code :=
  Code.comp mulCode (Code.pair (Code.comp leqIndicatorCode (Code.pair pairN1MSrc bExtract))
    (readerGen idCode kPredSrc pairN1MSrc))

theorem eval_eprecG (E B N k n : ℕ) (a b : UCode) (spec : ℕ → ℕ)
    (hec : (UCode.prec a b).enc ≤ E) (hn : n ≤ B) (hN : N = cfgRank E B k (UCode.prec a b).enc n) (hk1 : 1 ≤ k) :
    eprecGCode.eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N)))) (Nat.pair k (Nat.pair (UCode.prec a b).enc n)))
      = Part.some (if Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 - 1) ≤ B
          then spec (cfgRank E B (k - 1) (UCode.prec a b).enc (Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 - 1))) else 0) := by
  set X := Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N)))) (Nat.pair k (Nat.pair (UCode.prec a b).enc n)) with hX
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
  · have hself := self_lower_reader kPredSrc pairN1MSrc (k-1) (Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 - 1)) E B N k n (UCode.prec a b).enc spec hkp hp (by omega) hec hb hN
    rw [← hX] at hself
    rw [comp_pair_eval _ _ _ _ _ _ hleq hself, eval_mulCode, if_pos hb, if_pos hb, one_mul]
  · have hraw := readerGen_some idCode kPredSrc pairN1MSrc (UCode.prec a b).enc (k-1) (Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 - 1)) E B N k n (UCode.prec a b).enc (tableList spec N) (eval_idCode _) hkp hp
    rw [← hX] at hraw
    rw [comp_pair_eval _ _ _ _ _ _ hleq hraw, eval_mulCode, if_neg hb, if_neg hb, zero_mul]

end PallLean.Paper93.DeepMath.PathB.KleeneUCode

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.eval_eprecG
