import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneReaderGen
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneLookupSome

/-!
# Kleene interpreter project — raw universal reader (PROVED)

`reader_gen_correct` gives `spec(rank)` only when `rank < N`.  For `prec`/`rfind'`'s guarded reads (the
recursive self-call input `pair n1 m` and the `b`-call input `pair n1 (pair m i)` can both exceed `B`), the
reader still evaluates (raw table value) and the value-bound guard zeroes it.  `readerGen_some` gives the raw
value for **any** fuel/input.

  `readerGen_some` — `= some ((L.drop (N - (cfgRank … + 1))).headD 0)`.

## What is proved (clean axioms, no `sorry`)

* `readerGen_some`.

## Honest scope

The raw universal reader (out-of-range branches).  The `prec`/`rfind'` handlers, the body, the interpreter,
and the runtime remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode

open Nat.Partrec
open PallLean.Paper93.DeepMath.PathB.KleeneList (encodeList)
open PallLean.Paper93.DeepMath.PathB.KleeneRank (cfgRank)

/-- **Raw universal reader (proved): the table value for any fuel/input.** -/
theorem readerGen_some (subExtract kSource nSource : Code) (sc kv nv : ℕ) (E B N k n ecv : ℕ) (L : List ℕ)
    (hsub : subExtract.eval ecv = Part.some sc)
    (hks : kSource.eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList L)))
        (Nat.pair k (Nat.pair ecv n))) = Part.some kv)
    (hns : nSource.eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList L)))
        (Nat.pair k (Nat.pair ecv n))) = Part.some nv) :
    (readerGen subExtract kSource nSource).eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList L)))
        (Nat.pair k (Nat.pair ecv n))) = Part.some ((L.drop (N - (cfgRank E B kv sc nv + 1))).headD 0) := by
  set X := Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList L))) (Nat.pair k (Nat.pair ecv n)) with hX
  have hbi : (Code.left : Code).eval X = Part.some (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList L))) := by
    rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hec2 : (Code.comp Code.left (Code.comp Code.right Code.right)).eval X = Part.some ecv := by
    rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hsc : (Code.comp subExtract (Code.comp Code.left (Code.comp Code.right Code.right))).eval X
      = Part.some sc := by rw [comp_eval _ _ _ _ hec2]; exact hsub
  have hinput : (Code.pair Code.left (Code.pair kSource
      (Code.pair (Code.comp subExtract (Code.comp Code.left (Code.comp Code.right Code.right))) nSource))).eval X
      = Part.some (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList L)))
          (Nat.pair kv (Nat.pair sc nv))) :=
    pair_eval _ _ _ _ _ hbi (pair_eval _ _ _ _ _ hks (pair_eval _ _ _ _ _ hsc hns))
  rw [show (readerGen subExtract kSource nSource).eval X = ((Code.pair Code.left (Code.pair kSource
      (Code.pair (Code.comp subExtract (Code.comp Code.left (Code.comp Code.right Code.right))) nSource))).eval X).bind lookupSubCode.eval from rfl,
    hinput, Part.bind_some]
  exact lookupSubCode_some E B N kv sc nv L

end PallLean.Paper93.DeepMath.PathB.KleeneUCode

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.readerGen_some
