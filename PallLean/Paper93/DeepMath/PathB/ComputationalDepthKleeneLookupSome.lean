import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneLookupSub

/-!
# Kleene interpreter project — general Code-level `lookupSubCode` eval (PROVED)

`eval_lookupSubCode` requires the sub-rank `< N`.  For the data-dependent `comp`/`prec`/`rfind'` handlers,
the second lookup uses a *computed* input `vb` that may exceed `B` (out of table range); there the `[vb ≤ B]`
guard zeroes the contribution, but the `Code` still evaluates.  `lookupSubCode_some` gives the raw table
value for **any** input (no `< N` needed):

  `lookupSubCode_some` — `= some ((L.drop (N - (cfgRank … + 1))).headD 0)` for any `sec`, `n'`.

Honest scope: the general lookup eval (so handlers can multiply by `0` on the out-of-range branch).  The
data-dependent handlers, the body, the interpreter, and the runtime remain.  Nothing here is `NEXP ⊄ ACC⁰`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode

open Nat.Partrec
open PallLean.Paper93.DeepMath.PathB.KleeneList (encodeList lookupCode eval_lookupCode)
open PallLean.Paper93.DeepMath.PathB.KleeneRank (cfgRank)

/-- **General `lookupSubCode` eval (proved): the raw table value, any input.** -/
theorem lookupSubCode_some (E B N k sec n' : ℕ) (L : List ℕ) :
    lookupSubCode.eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList L)))
        (Nat.pair k (Nat.pair sec n'))) = Part.some ((L.drop (N - (cfgRank E B k sec n' + 1))).headD 0) := by
  set X := Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList L))) (Nat.pair k (Nat.pair sec n')) with hX
  have hctx : (Code.comp Code.left Code.left).eval X = Part.some (Nat.pair E B) := by
    rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hk : (Code.comp Code.left Code.right).eval X = Part.some k := by rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hsec : (Code.comp Code.left (Code.comp Code.right Code.right)).eval X = Part.some sec := by
    rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hn'2 : (Code.comp Code.right (Code.comp Code.right Code.right)).eval X = Part.some n' := by
    rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hN : (Code.comp Code.left (Code.comp Code.right Code.left)).eval X = Part.some N := by
    rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hT : (Code.comp Code.right (Code.comp Code.right Code.left)).eval X = Part.some (encodeList L) := by
    rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hargs : (Code.pair (Code.comp Code.left Code.right) (Code.pair (Code.comp Code.left (Code.comp Code.right Code.right)) (Code.comp Code.right (Code.comp Code.right Code.right)))).eval X = Part.some (Nat.pair k (Nat.pair sec n')) := pair_eval _ _ _ _ _ hk (pair_eval _ _ _ _ _ hsec hn'2)
  have hsr : (Code.comp cfgRankCode (Code.pair (Code.comp Code.left Code.left) (Code.pair (Code.comp Code.left Code.right) (Code.pair (Code.comp Code.left (Code.comp Code.right Code.right)) (Code.comp Code.right (Code.comp Code.right Code.right)))))).eval X = Part.some (cfgRank E B k sec n') := by
    rw [comp_pair_eval _ _ _ _ _ _ hctx hargs, eval_cfgRankCode]; rfl
  have hsucc : (Code.comp Code.succ (Code.comp cfgRankCode (Code.pair (Code.comp Code.left Code.left) (Code.pair (Code.comp Code.left Code.right) (Code.pair (Code.comp Code.left (Code.comp Code.right Code.right)) (Code.comp Code.right (Code.comp Code.right Code.right))))))).eval X = Part.some (cfgRank E B k sec n' + 1) := by
    rw [comp_eval _ _ _ _ hsr]; simp [Code.eval]
  have hoff : (Code.comp subCode (Code.pair (Code.comp Code.left (Code.comp Code.right Code.left)) (Code.comp Code.succ (Code.comp cfgRankCode (Code.pair (Code.comp Code.left Code.left) (Code.pair (Code.comp Code.left Code.right) (Code.pair (Code.comp Code.left (Code.comp Code.right Code.right)) (Code.comp Code.right (Code.comp Code.right Code.right))))))))).eval X = Part.some (N - (cfgRank E B k sec n' + 1)) := by
    rw [comp_pair_eval _ _ _ _ _ _ hN hsucc, eval_subCode]
  show (Code.comp lookupCode (Code.pair _ _)).eval X = _
  rw [comp_pair_eval _ _ _ _ _ _ hT hoff, eval_lookupCode]

end PallLean.Paper93.DeepMath.PathB.KleeneUCode

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.lookupSubCode_some
