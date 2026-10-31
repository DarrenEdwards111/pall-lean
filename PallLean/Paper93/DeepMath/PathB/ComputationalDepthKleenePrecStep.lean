import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleenePrecSelf
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneReaderGen
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneEncMono

/-!
# Kleene interpreter project — the `prec` step (PROVED)

`prec`'s step case (`n2 = m+1`) is `(evaln (k-1) prec (pair n1 m)) >>= fun i => evaln k b (pair n1 (pair m
i))` — a data-dependent `comp`-like nested inside the `casesOn`.  `eval_precStep` computes it: read the
guarded self-result `eprec` (`eval_eprecG`), form `i = eprec - 1`, read `b` at the composite `pair n1 (pair m
i)` guarded by `[composite ≤ B]`, and combine multiplicatively:

  `= isPos(eprec) · (if composite ≤ B then spec (cfgRank E B k b.enc composite) else 0)`.

(Stated with `∃ ev cmp` binding `ev = eprec`, `cmp = composite` so the `casesOn` assembly can name them.)

## What is proved (clean axioms, no `sorry`)

* `eval_precStep` (+ `iSrc`, `compositeSrc`, `precStepCode`).

## Honest scope

`prec`'s step value.  The `casesOn` assembly (base vs step), `rfind'`, the body, the interpreter, and the
runtime remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode

open Nat.Partrec
open PallLean.Paper93.DeepMath.PathB.KleeneList (encodeList)
open PallLean.Paper93.DeepMath.PathB.KleeneRank (cfgRank cfgRank_lt_code)

/-- `i = eprec - 1` (the value of the recursive `prec` call). -/
noncomputable def iSrc : Code := Code.comp predCode eprecGCode
/-- The `b`-call input `pair n1 (pair m i)`. -/
noncomputable def compositeSrc : Code := Code.pair n1Src (Code.pair mSrc iSrc)

/-- The `prec` step: `eprec >>= (i ↦ read b at composite)`, branch-free. -/
noncomputable def precStepCode : Code :=
  Code.comp mulCode (Code.pair (Code.comp isPosCode eprecGCode)
    (Code.comp mulCode (Code.pair (Code.comp leqIndicatorCode (Code.pair compositeSrc bExtract))
      (readerGen sndSubCode (Code.comp Code.left Code.right) compositeSrc))))

theorem eval_precStep (E B N k n : ℕ) (a b : UCode) (spec : ℕ → ℕ)
    (hec : (UCode.prec a b).enc ≤ E) (hn : n ≤ B) (hN : N = cfgRank E B k (UCode.prec a b).enc n) (hk1 : 1 ≤ k) :
    ∃ ev cmp,
      ev = (if Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 - 1) ≤ B
          then spec (cfgRank E B (k - 1) (UCode.prec a b).enc (Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 - 1))) else 0)
      ∧ cmp = Nat.pair (Nat.unpair n).1 (Nat.pair ((Nat.unpair n).2 - 1) (ev - 1))
      ∧ precStepCode.eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N)))) (Nat.pair k (Nat.pair (UCode.prec a b).enc n)))
        = Part.some ((if ev = 0 then 0 else 1) * (if cmp ≤ B then spec (cfgRank E B k b.enc cmp) else 0)) := by
  set X := Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N)))) (Nat.pair k (Nat.pair (UCode.prec a b).enc n)) with hX
  have heprec := eval_eprecG E B N k n a b spec hec hn hN hk1
  rw [← hX] at heprec
  set ev := (if Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 - 1) ≤ B
          then spec (cfgRank E B (k - 1) (UCode.prec a b).enc (Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 - 1))) else 0) with hev
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
  have hinner : (Code.comp mulCode (Code.pair (Code.comp leqIndicatorCode (Code.pair compositeSrc bExtract)) (readerGen sndSubCode (Code.comp Code.left Code.right) compositeSrc))).eval X = Part.some (if cmp ≤ B then spec (cfgRank E B k b.enc cmp) else 0) := by
    by_cases hcB : cmp ≤ B
    · have hbr := reader_gen_correct sndSubCode (Code.comp Code.left Code.right) compositeSrc b.enc k cmp E B N k n (UCode.prec a b).enc spec (eval_sndSub_prec a b) hk hcmpv (by rw [hN]; exact cfgRank_lt_code E B k (UCode.prec a b).enc b.enc n cmp (enc_lt_prec_right a b) hec hcB)
      rw [comp_pair_eval _ _ _ _ _ _ hleqC hbr, eval_mulCode, if_pos hcB, if_pos hcB, one_mul]
    · have hbr := readerGen_some sndSubCode (Code.comp Code.left Code.right) compositeSrc b.enc k cmp E B N k n (UCode.prec a b).enc (tableList spec N) (eval_sndSub_prec a b) hk hcmpv
      rw [comp_pair_eval _ _ _ _ _ _ hleqC hbr, eval_mulCode, if_neg hcB, if_neg hcB, zero_mul]
  show (Code.comp mulCode (Code.pair _ _)).eval X = _
  rw [comp_pair_eval _ _ _ _ _ _ hisPos hinner, eval_mulCode]

end PallLean.Paper93.DeepMath.PathB.KleeneUCode

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.eval_precStep
