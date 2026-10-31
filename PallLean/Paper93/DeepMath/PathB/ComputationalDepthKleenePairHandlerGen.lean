import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleenePairHandler
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneReader
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneGenExtract

/-!
# Kleene interpreter project — the generic `pair` handler (PROVED)

The `pair` handler restated for an *arbitrary* `ec` (the tag-4 path), not just `ec = (pair a b).enc`.  Since
`eaCode = readerCode fstSubCode` definitionally and `reader_correct` is generic, the value reads the subcodes
as raw numbers `(unpair (unpair ec).2).1/.2` via the general extraction (`eval_fstSub_gen` + `fstSub_lt`).
This is the form `hbody` needs, since the table includes malformed configs.

* `eaCode_eq`, `ebCode_eq`, `eval_pairHandler_gen`.

Honest scope: the generic `pair` handler.  Generic `comp`/`prec`/`rfind'`, `hbody`, the interpreter, and the
runtime remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode

open Nat.Partrec
open PallLean.Paper93.DeepMath.PathB.KleeneList (encodeList)
open PallLean.Paper93.DeepMath.PathB.KleeneRank (cfgRank)

theorem eaCode_eq : eaCode = readerCode fstSubCode := rfl
theorem ebCode_eq : ebCode = readerCode sndSubCode := rfl

theorem eval_pairHandler_gen (E B N k n ec : ℕ) (spec : ℕ → ℕ)
    (htag : 1 ≤ (Nat.unpair ec).1) (hec : ec ≤ E) (hn : n ≤ B) (hN : N = cfgRank E B k ec n) :
    pairHandler.eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N))))
        (Nat.pair k (Nat.pair ec n)))
      = Part.some ((if n ≤ k - 1 then 1 else 0)
          * ((if spec (cfgRank E B k (Nat.unpair (Nat.unpair ec).2).1 n) = 0 then 0 else 1)
             * ((if spec (cfgRank E B k (Nat.unpair (Nat.unpair ec).2).2 n) = 0 then 0 else 1)
                * (Nat.pair (spec (cfgRank E B k (Nat.unpair (Nat.unpair ec).2).1 n) - 1)
                    (spec (cfgRank E B k (Nat.unpair (Nat.unpair ec).2).2 n) - 1) + 1)))) := by
  set X := Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N)))) (Nat.pair k (Nat.pair ec n)) with hX
  have hea : eaCode.eval X = Part.some (spec (cfgRank E B k (Nat.unpair (Nat.unpair ec).2).1 n)) := by
    have := reader_correct fstSubCode (Nat.unpair (Nat.unpair ec).2).1 E B N k n ec spec (eval_fstSub_gen ec) (fstSub_lt ec htag) hec hn hN
    rwa [← hX] at this
  have heb : ebCode.eval X = Part.some (spec (cfgRank E B k (Nat.unpair (Nat.unpair ec).2).2 n)) := by
    have := reader_correct sndSubCode (Nat.unpair (Nat.unpair ec).2).2 E B N k n ec spec (eval_sndSub_gen ec) (sndSub_lt ec htag) hec hn hN
    rwa [← hX] at this
  have hkp : (Code.comp predCode (Code.comp Code.left Code.right)).eval X = Part.some (k - 1) := by
    rw [comp_eval _ _ _ _ (show (Code.comp Code.left Code.right).eval X = Part.some k from by rw [hX]; simp [Code.eval, Nat.unpair_pair]), eval_predCode, Nat.pred_eq_sub_one]
  have hn2 : (Code.comp Code.right (Code.comp Code.right Code.right)).eval X = Part.some n := by rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hleq : (Code.comp leqIndicatorCode (Code.pair (Code.comp Code.right (Code.comp Code.right Code.right)) (Code.comp predCode (Code.comp Code.left Code.right)))).eval X = Part.some (if n ≤ k - 1 then 1 else 0) := by
    rw [comp_pair_eval _ _ _ _ _ _ hn2 hkp, eval_leqIndicatorCode]
  have hpa : (Code.comp isPosCode eaCode).eval X = Part.some (if spec (cfgRank E B k (Nat.unpair (Nat.unpair ec).2).1 n) = 0 then 0 else 1) := by
    rw [comp_eval _ _ _ _ hea, eval_isPosCode]
  have hpb : (Code.comp isPosCode ebCode).eval X = Part.some (if spec (cfgRank E B k (Nat.unpair (Nat.unpair ec).2).2 n) = 0 then 0 else 1) := by
    rw [comp_eval _ _ _ _ heb, eval_isPosCode]
  have hpf : (Code.comp Code.succ (Code.pair (Code.comp predCode eaCode) (Code.comp predCode ebCode))).eval X = Part.some (Nat.pair (spec (cfgRank E B k (Nat.unpair (Nat.unpair ec).2).1 n) - 1) (spec (cfgRank E B k (Nat.unpair (Nat.unpair ec).2).2 n) - 1) + 1) := by
    rw [comp_eval _ _ _ _ (pair_eval _ _ _ _ _ (by rw [comp_eval _ _ _ _ hea, eval_predCode, Nat.pred_eq_sub_one]) (by rw [comp_eval _ _ _ _ heb, eval_predCode, Nat.pred_eq_sub_one]))]; simp [Code.eval]
  have hm3 : (Code.comp mulCode (Code.pair (Code.comp isPosCode ebCode) (Code.comp Code.succ (Code.pair (Code.comp predCode eaCode) (Code.comp predCode ebCode))))).eval X = Part.some ((if spec (cfgRank E B k (Nat.unpair (Nat.unpair ec).2).2 n) = 0 then 0 else 1) * (Nat.pair (spec (cfgRank E B k (Nat.unpair (Nat.unpair ec).2).1 n) - 1) (spec (cfgRank E B k (Nat.unpair (Nat.unpair ec).2).2 n) - 1) + 1)) := by
    rw [comp_pair_eval _ _ _ _ _ _ hpb hpf, eval_mulCode]
  have hm2 : (Code.comp mulCode (Code.pair (Code.comp isPosCode eaCode) (Code.comp mulCode (Code.pair (Code.comp isPosCode ebCode) (Code.comp Code.succ (Code.pair (Code.comp predCode eaCode) (Code.comp predCode ebCode))))))).eval X = Part.some ((if spec (cfgRank E B k (Nat.unpair (Nat.unpair ec).2).1 n) = 0 then 0 else 1) * ((if spec (cfgRank E B k (Nat.unpair (Nat.unpair ec).2).2 n) = 0 then 0 else 1) * (Nat.pair (spec (cfgRank E B k (Nat.unpair (Nat.unpair ec).2).1 n) - 1) (spec (cfgRank E B k (Nat.unpair (Nat.unpair ec).2).2 n) - 1) + 1))) := by
    rw [comp_pair_eval _ _ _ _ _ _ hpa hm3, eval_mulCode]
  show (Code.comp mulCode (Code.pair _ _)).eval X = _
  rw [comp_pair_eval _ _ _ _ _ _ hleq hm2, eval_mulCode]

end PallLean.Paper93.DeepMath.PathB.KleeneUCode

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.eval_pairHandler_gen
