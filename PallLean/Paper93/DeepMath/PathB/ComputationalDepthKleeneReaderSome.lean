import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneReaderAt
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneLookupSome

/-!
# Kleene interpreter project — raw data-dependent reader (PROVED)

`reader_at_correct` gives `spec(rank)` only when the (computed) input `nv ≤ B`.  For `comp`'s out-of-range
branch (`vb > B`), the reader still evaluates (to a raw table value), and the `[vb≤B]` guard zeroes it.
`readerCodeAt_some` gives that raw value for **any** `nv`.

  `readerCodeAt_some` — `= some ((L.drop (N - (cfgRank … + 1))).headD 0)` for any computed input.

## What is proved (clean axioms, no `sorry`)

* `readerCodeAt_some`.

## Honest scope

The raw data-dependent reader.  The `comp`/`prec`/`rfind'` handlers, the body, the interpreter, and the
runtime remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode

open Nat.Partrec
open PallLean.Paper93.DeepMath.PathB.KleeneList (encodeList)
open PallLean.Paper93.DeepMath.PathB.KleeneRank (cfgRank)

/-- **Raw data-dependent reader (proved): the table value for any computed input.** -/
theorem readerCodeAt_some (subExtract nSource : Code) (sc nv : ℕ) (E B N k n ecv : ℕ) (L : List ℕ)
    (hsub : subExtract.eval ecv = Part.some sc)
    (hns : nSource.eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList L)))
        (Nat.pair k (Nat.pair ecv n))) = Part.some nv) :
    (readerCodeAt subExtract nSource).eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList L)))
        (Nat.pair k (Nat.pair ecv n)))
      = Part.some ((L.drop (N - (cfgRank E B k sc nv + 1))).headD 0) := by
  set X := Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList L))) (Nat.pair k (Nat.pair ecv n)) with hX
  have hbi : (Code.left : Code).eval X = Part.some (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList L))) := by
    rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hk : (Code.comp Code.left Code.right).eval X = Part.some k := by rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hec2 : (Code.comp Code.left (Code.comp Code.right Code.right)).eval X = Part.some ecv := by
    rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hsc : (Code.comp subExtract (Code.comp Code.left (Code.comp Code.right Code.right))).eval X
      = Part.some sc := by rw [comp_eval _ _ _ _ hec2]; exact hsub
  have hinput : (Code.pair Code.left (Code.pair (Code.comp Code.left Code.right)
      (Code.pair (Code.comp subExtract (Code.comp Code.left (Code.comp Code.right Code.right))) nSource))).eval X
      = Part.some (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList L)))
          (Nat.pair k (Nat.pair sc nv))) :=
    pair_eval _ _ _ _ _ hbi (pair_eval _ _ _ _ _ hk (pair_eval _ _ _ _ _ hsc hns))
  rw [show (readerCodeAt subExtract nSource).eval X = ((Code.pair Code.left (Code.pair (Code.comp Code.left Code.right)
      (Code.pair (Code.comp subExtract (Code.comp Code.left (Code.comp Code.right Code.right))) nSource))).eval X).bind lookupSubCode.eval from rfl,
    hinput, Part.bind_some]
  exact lookupSubCode_some E B N k sc nv L

end PallLean.Paper93.DeepMath.PathB.KleeneUCode

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.readerCodeAt_some
