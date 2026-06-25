import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneReader

/-!
# Kleene interpreter project — data-dependent sub-result reader (PROVED)

Generalizes `reader_correct` so the lookup input comes from an arbitrary sub-`Code` `nSource` (not just the
bundle's `n`).  This is exactly what `comp`'s second call needs (input = the computed value `vb` of `b`'s
result), and `prec`/`rfind'` similarly.

  `readerCodeAt subExtract nSource`, `reader_at_correct` — given `nSource` evaluates to `nv` (with `nv ≤ B`),
  `= spec (cfgRank E B k sc nv)`.

(The at-`n` reader is the instance `nSource = n`-extractor, `nv = n`.)

## What is proved (clean axioms, no `sorry`)

* `readerCodeAt`, `reader_at_correct`.

## Honest scope

The data-dependent reader (for `nv ≤ B`).  The out-of-range case uses `lookupSubCode_some` + the `[nv≤B]`
guard.  The `comp`/`prec`/`rfind'` handlers, the body, the interpreter, and the runtime remain.  Nothing here
is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode

open Nat.Partrec
open PallLean.Paper93.DeepMath.PathB.KleeneList (encodeList)
open PallLean.Paper93.DeepMath.PathB.KleeneRank (cfgRank cfgRank_lt_code)

/-- Reader with a data-dependent input from `nSource`. -/
def readerCodeAt (subExtract nSource : Code) : Code :=
  Code.comp lookupSubCode (Code.pair Code.left (Code.pair (Code.comp Code.left Code.right)
    (Code.pair (Code.comp subExtract (Code.comp Code.left (Code.comp Code.right Code.right))) nSource)))

/-- **Data-dependent reader correctness (proved).** -/
theorem reader_at_correct (subExtract nSource : Code) (sc nv : ℕ) (E B N k n ecv : ℕ) (spec : ℕ → ℕ)
    (hsub : subExtract.eval ecv = Part.some sc)
    (hns : nSource.eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N))))
        (Nat.pair k (Nat.pair ecv n))) = Part.some nv)
    (hlt : sc < ecv) (hec : ecv ≤ E) (hnv : nv ≤ B) (hN : N = cfgRank E B k ecv n) :
    (readerCodeAt subExtract nSource).eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N))))
        (Nat.pair k (Nat.pair ecv n))) = Part.some (spec (cfgRank E B k sc nv)) := by
  set X := Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N))))
    (Nat.pair k (Nat.pair ecv n)) with hX
  have hbi : (Code.left : Code).eval X
      = Part.some (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N)))) := by
    rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hk : (Code.comp Code.left Code.right).eval X = Part.some k := by rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hec2 : (Code.comp Code.left (Code.comp Code.right Code.right)).eval X = Part.some ecv := by
    rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hsc : (Code.comp subExtract (Code.comp Code.left (Code.comp Code.right Code.right))).eval X
      = Part.some sc := by rw [comp_eval _ _ _ _ hec2]; exact hsub
  have hinput : (Code.pair Code.left (Code.pair (Code.comp Code.left Code.right)
      (Code.pair (Code.comp subExtract (Code.comp Code.left (Code.comp Code.right Code.right))) nSource))).eval X
      = Part.some (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N))))
          (Nat.pair k (Nat.pair sc nv))) :=
    pair_eval _ _ _ _ _ hbi (pair_eval _ _ _ _ _ hk (pair_eval _ _ _ _ _ hsc hns))
  rw [show (readerCodeAt subExtract nSource).eval X = ((Code.pair Code.left (Code.pair (Code.comp Code.left Code.right)
      (Code.pair (Code.comp subExtract (Code.comp Code.left (Code.comp Code.right Code.right))) nSource))).eval X).bind lookupSubCode.eval from rfl,
    hinput, Part.bind_some]
  exact eval_lookupSubCode E B N k sc nv spec (by rw [hN]; exact cfgRank_lt_code E B k ecv sc n nv hlt hec hnv)

end PallLean.Paper93.DeepMath.PathB.KleeneUCode

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.reader_at_correct
