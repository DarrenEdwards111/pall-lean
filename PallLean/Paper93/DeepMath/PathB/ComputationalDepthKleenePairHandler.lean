import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleenePairReaders
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneIndicators
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneEncodeOpt

/-!
# Kleene interpreter project — the `pair` handler (PROVED)

The first complete recursive handler.  On the pair bundle it computes the branch-free multiplicative form
`[n≤k] · isPos(ea) · isPos(eb) · (pair(ea-1)(eb-1)+1)` with `ea = spec(rank a)`, `eb = spec(rank b)`.  By
`encode_pair_step` this equals `encodeOpt (evalnStep … (pair a b) n) = spec N` (when `spec = encodeOpt∘evaln`).

* `pairHandler`, `eval_pairHandler`.

Honest scope: the `pair` handler.  `comp`/`prec`/`rfind'`, the body, `spec`/`hbody`, the interpreter, and the
runtime remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode

open Nat.Partrec
open PallLean.Paper93.DeepMath.PathB.KleeneList (encodeList)
open PallLean.Paper93.DeepMath.PathB.KleeneRank (cfgRank)

/-- The `pair` handler: branch-free multiplicative computation of the encoded pair-result. -/
def pairHandler : Code :=
  Code.comp mulCode (Code.pair
    (Code.comp leqIndicatorCode (Code.pair (Code.comp Code.right (Code.comp Code.right Code.right))
      (Code.comp predCode (Code.comp Code.left Code.right))))
    (Code.comp mulCode (Code.pair (Code.comp isPosCode eaCode)
      (Code.comp mulCode (Code.pair (Code.comp isPosCode ebCode)
        (Code.comp Code.succ (Code.pair (Code.comp predCode eaCode) (Code.comp predCode ebCode))))))))

theorem eval_pairHandler (E B N k n : ℕ) (a b : UCode) (spec : ℕ → ℕ)
    (hec : (UCode.pair a b).enc ≤ E) (hn : n ≤ B) (hN : N = cfgRank E B k (UCode.pair a b).enc n) :
    pairHandler.eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N))))
        (Nat.pair k (Nat.pair (UCode.pair a b).enc n)))
      = Part.some ((if n ≤ k - 1 then 1 else 0) * ((if spec (cfgRank E B k a.enc n) = 0 then 0 else 1)
          * ((if spec (cfgRank E B k b.enc n) = 0 then 0 else 1)
              * (Nat.pair (spec (cfgRank E B k a.enc n) - 1) (spec (cfgRank E B k b.enc n) - 1) + 1)))) := by
  set X := Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N))))
    (Nat.pair k (Nat.pair (UCode.pair a b).enc n)) with hX
  have hea := eval_eaCode E B N k n a b spec hec hn hN
  have heb := eval_ebCode E B N k n a b spec hec hn hN
  have hkp : (Code.comp predCode (Code.comp Code.left Code.right)).eval X = Part.some (k - 1) := by
    rw [comp_eval _ _ _ _ (show (Code.comp Code.left Code.right).eval X = Part.some k from by
      rw [hX]; simp [Code.eval, Nat.unpair_pair]), eval_predCode, Nat.pred_eq_sub_one]
  have hn2 : (Code.comp Code.right (Code.comp Code.right Code.right)).eval X = Part.some n := by
    rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hleq : (Code.comp leqIndicatorCode (Code.pair (Code.comp Code.right (Code.comp Code.right Code.right))
      (Code.comp predCode (Code.comp Code.left Code.right)))).eval X = Part.some (if n ≤ k - 1 then 1 else 0) := by
    rw [comp_pair_eval _ _ _ _ _ _ hn2 hkp, eval_leqIndicatorCode]
  have hpa : (Code.comp isPosCode eaCode).eval X
      = Part.some (if spec (cfgRank E B k a.enc n) = 0 then 0 else 1) := by
    rw [comp_eval _ _ _ _ hea, eval_isPosCode]
  have hpb : (Code.comp isPosCode ebCode).eval X
      = Part.some (if spec (cfgRank E B k b.enc n) = 0 then 0 else 1) := by
    rw [comp_eval _ _ _ _ heb, eval_isPosCode]
  have hpf : (Code.comp Code.succ (Code.pair (Code.comp predCode eaCode) (Code.comp predCode ebCode))).eval X
      = Part.some (Nat.pair (spec (cfgRank E B k a.enc n) - 1) (spec (cfgRank E B k b.enc n) - 1) + 1) := by
    rw [comp_eval _ _ _ _ (pair_eval _ _ _ _ _ (by rw [comp_eval _ _ _ _ hea, eval_predCode])
      (by rw [comp_eval _ _ _ _ heb, eval_predCode]))]; simp [Code.eval]
  have hm3 : (Code.comp mulCode (Code.pair (Code.comp isPosCode ebCode)
      (Code.comp Code.succ (Code.pair (Code.comp predCode eaCode) (Code.comp predCode ebCode))))).eval X
      = Part.some ((if spec (cfgRank E B k b.enc n) = 0 then 0 else 1)
          * (Nat.pair (spec (cfgRank E B k a.enc n) - 1) (spec (cfgRank E B k b.enc n) - 1) + 1)) := by
    rw [comp_pair_eval _ _ _ _ _ _ hpb hpf, eval_mulCode]
  have hm2 : (Code.comp mulCode (Code.pair (Code.comp isPosCode eaCode)
      (Code.comp mulCode (Code.pair (Code.comp isPosCode ebCode)
        (Code.comp Code.succ (Code.pair (Code.comp predCode eaCode) (Code.comp predCode ebCode))))))).eval X
      = Part.some ((if spec (cfgRank E B k a.enc n) = 0 then 0 else 1)
          * ((if spec (cfgRank E B k b.enc n) = 0 then 0 else 1)
              * (Nat.pair (spec (cfgRank E B k a.enc n) - 1) (spec (cfgRank E B k b.enc n) - 1) + 1))) := by
    rw [comp_pair_eval _ _ _ _ _ _ hpa hm3, eval_mulCode]
  show (Code.comp mulCode (Code.pair _ _)).eval X = _
  rw [comp_pair_eval _ _ _ _ _ _ hleq hm2, eval_mulCode]

end PallLean.Paper93.DeepMath.PathB.KleeneUCode

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.eval_pairHandler
