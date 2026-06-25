import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneLookupSub
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneDecode

/-!
# Kleene interpreter project — generic sub-result reader (PROVED)

A single reader parameterized by the subcode-extractor `subExtract`, factoring the per-constructor readers:
on the handler bundle it extracts a subcode `sc` from `ec` (`subExtract ec = sc`), looks it up at input `n`,
and returns `spec` at the sub-config rank — given `sc < ec` (the subcode is encoding-smaller) and the value
bounds.

  `readerCode subExtract`, `reader_correct` — `= spec (cfgRank E B k sc n)`.

Instantiated with `fstSubCode`/`sndSubCode` (+ the matching `enc_lt_*`) this gives the at-`n` sub-result for
`pair`/`comp`/`prec`'s subcodes uniformly.

## What is proved (clean axioms, no `sorry`)

* `readerCode`, `reader_correct`.

## Honest scope

The generic at-`n` reader.  The data-dependent reader (`comp`/`prec`/`rfind'` second call at a computed
input), the handlers, the body, the interpreter, and the runtime remain.  Nothing here is `NEXP ⊄ ACC⁰`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode

open Nat.Partrec
open PallLean.Paper93.DeepMath.PathB.KleeneList (encodeList)
open PallLean.Paper93.DeepMath.PathB.KleeneRank (cfgRank cfgRank_lt_code)

/-- Generic sub-result reader: extract a subcode via `subExtract`, look it up at input `n`. -/
def readerCode (subExtract : Code) : Code :=
  Code.comp lookupSubCode (Code.pair Code.left (Code.pair (Code.comp Code.left Code.right)
    (Code.pair (Code.comp subExtract (Code.comp Code.left (Code.comp Code.right Code.right)))
      (Code.comp Code.right (Code.comp Code.right Code.right)))))

/-- **Generic reader correctness (proved): `= spec (cfgRank E B k sc n)`.** -/
theorem reader_correct (subExtract : Code) (sc : ℕ) (E B N k n ecv : ℕ) (spec : ℕ → ℕ)
    (hsub : subExtract.eval ecv = Part.some sc) (hlt : sc < ecv)
    (hec : ecv ≤ E) (hn : n ≤ B) (hN : N = cfgRank E B k ecv n) :
    (readerCode subExtract).eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N))))
        (Nat.pair k (Nat.pair ecv n))) = Part.some (spec (cfgRank E B k sc n)) := by
  set X := Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N))))
    (Nat.pair k (Nat.pair ecv n)) with hX
  have hbi : (Code.left : Code).eval X
      = Part.some (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N)))) := by
    rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hk : (Code.comp Code.left Code.right).eval X = Part.some k := by rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hn2 : (Code.comp Code.right (Code.comp Code.right Code.right)).eval X = Part.some n := by
    rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hec2 : (Code.comp Code.left (Code.comp Code.right Code.right)).eval X = Part.some ecv := by
    rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hsc : (Code.comp subExtract (Code.comp Code.left (Code.comp Code.right Code.right))).eval X
      = Part.some sc := by rw [comp_eval _ _ _ _ hec2]; exact hsub
  have hinput : (Code.pair Code.left (Code.pair (Code.comp Code.left Code.right)
      (Code.pair (Code.comp subExtract (Code.comp Code.left (Code.comp Code.right Code.right)))
        (Code.comp Code.right (Code.comp Code.right Code.right))))).eval X
      = Part.some (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N))))
          (Nat.pair k (Nat.pair sc n))) :=
    pair_eval _ _ _ _ _ hbi (pair_eval _ _ _ _ _ hk (pair_eval _ _ _ _ _ hsc hn2))
  rw [show (readerCode subExtract).eval X = ((Code.pair Code.left (Code.pair (Code.comp Code.left Code.right)
      (Code.pair (Code.comp subExtract (Code.comp Code.left (Code.comp Code.right Code.right)))
        (Code.comp Code.right (Code.comp Code.right Code.right))))).eval X).bind lookupSubCode.eval from rfl,
    hinput, Part.bind_some]
  exact eval_lookupSubCode E B N k sc n spec (by rw [hN]; exact cfgRank_lt_code E B k ecv sc n n hlt hec hn)

end PallLean.Paper93.DeepMath.PathB.KleeneUCode

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.reader_correct
