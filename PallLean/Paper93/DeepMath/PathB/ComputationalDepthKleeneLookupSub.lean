import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneCfgRankCode
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneSub
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneTableCorrect
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneDecode

/-!
# Kleene interpreter project — the factored sub-result reader (PROVED)

The piece every recursive handler shares: read a sub-config's result from the table.  Given the body input
`pair (pair (pair E B) (pair N T)) (pair k (pair sec n'))`, `lookupSubCode` computes the sub-config rank
`cfgRank E B k sec n'`, the reverse-index offset `N - (rank+1)`, and `lookupCode`s the table.  When the
table is the correct one (`encodeList (tableList spec N)`) and the sub-config has smaller rank (`< N`), it
returns exactly `spec` at that rank — i.e. the (encoded) sub-result.

  `lookupSubCode`, `eval_lookupSubCode` — `= spec (cfgRank E B k sec n')` given `cfgRank … < N`.

This is the de-risked engineering payoff: with `buildTableCtx_correct` + `tableList_lookup`, reading a
sub-result is a clean `Code` returning the right `spec`.

## What is proved (clean axioms, no `sorry`)

* `lookupSubCode`, `eval_lookupSubCode`.

## Honest scope

The sub-result reader.  The four recursive handlers (using it + `evalnStep` combination), the per-cell body,
`spec = encoded evaln`, the interpreter, and the runtime remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/
open Nat.Partrec
open PallLean.Paper93.DeepMath.PathB.KleeneUCode
open PallLean.Paper93.DeepMath.PathB.KleeneList (encodeList lookupCode eval_lookupCode)
open PallLean.Paper93.DeepMath.PathB.KleeneRank (cfgRank)

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode

-- input X = pair (pair (pair E B) (pair N T)) (pair k (pair sec n'))
def lookupSubCode : Code :=
  Code.comp lookupCode (Code.pair
    (Code.comp Code.right (Code.comp Code.right Code.left))  -- T
    (Code.comp subCode (Code.pair
      (Code.comp Code.left (Code.comp Code.right Code.left))  -- N
      (Code.comp Code.succ (Code.comp cfgRankCode (Code.pair
        (Code.comp Code.left Code.left)                       -- ctx = pair E B
        (Code.pair (Code.comp Code.left Code.right)           -- k
          (Code.pair (Code.comp Code.left (Code.comp Code.right Code.right))   -- sec
            (Code.comp Code.right (Code.comp Code.right Code.right))))))))))    -- n'

theorem eval_lookupSubCode (E B N k sec n' : ℕ) (spec : ℕ → ℕ)
    (hsub : cfgRank E B k sec n' < N) :
    lookupSubCode.eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N))))
        (Nat.pair k (Nat.pair sec n')))
      = Part.some (spec (cfgRank E B k sec n')) := by
  set X := Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N)))) (Nat.pair k (Nat.pair sec n')) with hX
  have hctx : (Code.comp Code.left Code.left).eval X = Part.some (Nat.pair E B) := by rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hk : (Code.comp Code.left Code.right).eval X = Part.some k := by rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hsec : (Code.comp Code.left (Code.comp Code.right Code.right)).eval X = Part.some sec := by rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hn' : (Code.comp Code.right (Code.comp Code.right Code.right)).eval X = Part.some n' := by rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hN : (Code.comp Code.left (Code.comp Code.right Code.left)).eval X = Part.some N := by rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hT : (Code.comp Code.right (Code.comp Code.right Code.left)).eval X = Part.some (encodeList (tableList spec N)) := by rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hargs : (Code.pair (Code.comp Code.left Code.right) (Code.pair (Code.comp Code.left (Code.comp Code.right Code.right)) (Code.comp Code.right (Code.comp Code.right Code.right)))).eval X = Part.some (Nat.pair k (Nat.pair sec n')) := pair_eval _ _ _ _ _ hk (pair_eval _ _ _ _ _ hsec hn')
  have hsr : (Code.comp cfgRankCode (Code.pair (Code.comp Code.left Code.left) (Code.pair (Code.comp Code.left Code.right) (Code.pair (Code.comp Code.left (Code.comp Code.right Code.right)) (Code.comp Code.right (Code.comp Code.right Code.right)))))).eval X = Part.some (cfgRank E B k sec n') := by
    rw [comp_pair_eval _ _ _ _ _ _ hctx hargs, eval_cfgRankCode]; rfl
  have hsucc : (Code.comp Code.succ (Code.comp cfgRankCode (Code.pair (Code.comp Code.left Code.left) (Code.pair (Code.comp Code.left Code.right) (Code.pair (Code.comp Code.left (Code.comp Code.right Code.right)) (Code.comp Code.right (Code.comp Code.right Code.right))))))).eval X = Part.some (cfgRank E B k sec n' + 1) := by
    rw [comp_eval _ _ _ _ hsr]; simp [Code.eval]
  have hoff : (Code.comp subCode (Code.pair (Code.comp Code.left (Code.comp Code.right Code.left)) (Code.comp Code.succ (Code.comp cfgRankCode (Code.pair (Code.comp Code.left Code.left) (Code.pair (Code.comp Code.left Code.right) (Code.pair (Code.comp Code.left (Code.comp Code.right Code.right)) (Code.comp Code.right (Code.comp Code.right Code.right))))))))).eval X = Part.some (N - (cfgRank E B k sec n' + 1)) := by
    rw [comp_pair_eval _ _ _ _ _ _ hN hsucc, eval_subCode]
  show (Code.comp lookupCode (Code.pair _ _)).eval X = _
  rw [comp_pair_eval _ _ _ _ _ _ hT hoff, eval_lookupCode]
  rw [show N - (cfgRank E B k sec n' + 1) = N - 1 - cfgRank E B k sec n' from by omega]
  rw [tableList_lookup spec N (cfgRank E B k sec n') hsub]

end PallLean.Paper93.DeepMath.PathB.KleeneUCode

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.eval_lookupSubCode
