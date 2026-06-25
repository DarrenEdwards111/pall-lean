import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneLookupSub
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneDecode

/-!
# Kleene interpreter project — the universal sub-result reader (PROVED)

The most general reader: the lookup's subcode, **fuel**, and input all come from arbitrary sub-`Code`s, and
the `rank < N` obligation is taken as a direct hypothesis (discharged per-handler by `cfgRank_lt_code` for
same-fuel subcodes or `cfgRank_lt_fuel` for `prec`/`rfind'`'s lower-fuel recursion).  This subsumes every
earlier reader variant.

  `readerGen subExtract kSource nSource`, `reader_gen_correct` — `= spec (cfgRank E B kv sc nv)` given the
  three sub-Code values and `cfgRank E B kv sc nv < N`.

For `prec`/`rfind'` the recursive call is at fuel `k` while the config fuel is `k+1`: take `kSource = pred`
of the fuel extractor and discharge `rank < N` via `cfgRank_lt_fuel`.

## What is proved (clean axioms, no `sorry`)

* `readerGen`, `reader_gen_correct`.

## Honest scope

The universal reader.  The `prec`/`rfind'` handler `Code`s, the body, the interpreter, and the runtime
remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode

open Nat.Partrec
open PallLean.Paper93.DeepMath.PathB.KleeneList (encodeList)
open PallLean.Paper93.DeepMath.PathB.KleeneRank (cfgRank)

/-- Universal reader: subcode, fuel, and input all from sub-`Code`s. -/
def readerGen (subExtract kSource nSource : Code) : Code :=
  Code.comp lookupSubCode (Code.pair Code.left (Code.pair kSource
    (Code.pair (Code.comp subExtract (Code.comp Code.left (Code.comp Code.right Code.right))) nSource)))

/-- **Universal reader correctness (proved).** -/
theorem reader_gen_correct (subExtract kSource nSource : Code) (sc kv nv : ℕ) (E B N k n ecv : ℕ) (spec : ℕ → ℕ)
    (hsub : subExtract.eval ecv = Part.some sc)
    (hks : kSource.eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N))))
        (Nat.pair k (Nat.pair ecv n))) = Part.some kv)
    (hns : nSource.eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N))))
        (Nat.pair k (Nat.pair ecv n))) = Part.some nv)
    (hrank : cfgRank E B kv sc nv < N) :
    (readerGen subExtract kSource nSource).eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N))))
        (Nat.pair k (Nat.pair ecv n))) = Part.some (spec (cfgRank E B kv sc nv)) := by
  set X := Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N))))
    (Nat.pair k (Nat.pair ecv n)) with hX
  have hbi : (Code.left : Code).eval X
      = Part.some (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N)))) := by
    rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hec2 : (Code.comp Code.left (Code.comp Code.right Code.right)).eval X = Part.some ecv := by
    rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hsc : (Code.comp subExtract (Code.comp Code.left (Code.comp Code.right Code.right))).eval X
      = Part.some sc := by rw [comp_eval _ _ _ _ hec2]; exact hsub
  have hinput : (Code.pair Code.left (Code.pair kSource
      (Code.pair (Code.comp subExtract (Code.comp Code.left (Code.comp Code.right Code.right))) nSource))).eval X
      = Part.some (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N))))
          (Nat.pair kv (Nat.pair sc nv))) :=
    pair_eval _ _ _ _ _ hbi (pair_eval _ _ _ _ _ hks (pair_eval _ _ _ _ _ hsc hns))
  rw [show (readerGen subExtract kSource nSource).eval X = ((Code.pair Code.left (Code.pair kSource
      (Code.pair (Code.comp subExtract (Code.comp Code.left (Code.comp Code.right Code.right))) nSource))).eval X).bind lookupSubCode.eval from rfl,
    hinput, Part.bind_some]
  exact eval_lookupSubCode E B N kv sc nv spec hrank

end PallLean.Paper93.DeepMath.PathB.KleeneUCode

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.reader_gen_correct
