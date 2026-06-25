import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneReaderGen
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneDispatch
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneEncMono

/-!
# Kleene interpreter project — `prec` base-case reader (PROVED)

`prec`'s base case (`n2 = 0`) is `evaln k a n1` where `n1 = (unpair n).1` (same fuel).  `prec_base` reads it:
the sub-config `(k, a, n1)` ranks below `N` because `a.enc < (prec a b).enc` (`enc_lt_prec_left`) and
`n1 ≤ n ≤ B` (`Nat.unpair_left_le`).

  `prec_base` — `= spec (cfgRank E B k a.enc (unpair n).1)`.

## What is proved (clean axioms, no `sorry`)

* `prec_base`.

## Honest scope

`prec`'s base case.  The `prec` step (nested `comp`-like with two value-bound guards + lower-fuel self-
recursion), the `casesOn` assembly, `rfind'`, the body, the interpreter, and the runtime remain.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode

open Nat.Partrec
open PallLean.Paper93.DeepMath.PathB.KleeneList (encodeList)
open PallLean.Paper93.DeepMath.PathB.KleeneRank (cfgRank cfgRank_lt_code)

/-- Read `evaln k a n1` (the `prec` base case), `n1 = (unpair n).1`. -/
theorem prec_base (E B N k n : ℕ) (a b : UCode) (spec : ℕ → ℕ)
    (hec : (UCode.prec a b).enc ≤ E) (hn : n ≤ B) (hN : N = cfgRank E B k (UCode.prec a b).enc n) :
    (readerGen fstSubCode (Code.comp Code.left Code.right) (Code.comp Code.left (Code.comp Code.right (Code.comp Code.right Code.right)))).eval
        (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N)))) (Nat.pair k (Nat.pair (UCode.prec a b).enc n)))
      = Part.some (spec (cfgRank E B k a.enc (Nat.unpair n).1)) := by
  apply reader_gen_correct fstSubCode (Code.comp Code.left Code.right) (Code.comp Code.left (Code.comp Code.right (Code.comp Code.right Code.right))) a.enc k (Nat.unpair n).1 E B N k n (UCode.prec a b).enc spec (eval_fstSub_prec a b)
  · simp [Code.eval, Nat.unpair_pair]
  · simp [Code.eval, Nat.unpair_pair]
  · rw [hN]; exact cfgRank_lt_code E B k (UCode.prec a b).enc a.enc n (Nat.unpair n).1 (enc_lt_prec_left a b) hec (le_trans (Nat.unpair_left_le n) hn)

end PallLean.Paper93.DeepMath.PathB.KleeneUCode

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.prec_base
