import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneLookupSub
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneEncMono

/-!
# Kleene interpreter project — pair handler sub-result correctness (PROVED)

The pair handler reads `evaln a` and `evaln b` from the table.  These lemmas confirm — using the now-proved
de-risked machinery — that those reads return exactly the right `spec` values: the sub-configs `(k, a, n)`
and `(k, b, n)` rank below the current config (via `enc_lt_pair_left/right` + `cfgRank_lt_code`), so
`lookupSubCode` (`eval_lookupSubCode`) returns `spec` at their ranks.

  `pair_ea` / `pair_eb` — `lookupSubCode` at the `a`/`b` sub-config `= spec (cfgRank … a.enc n / b.enc n)`.

This is the correctness core of the pair handler: the two sub-results are read correctly.  The handler `Code`
then combines them by the (proved) multiplicative identity `encode_pair_step`.

## What is proved (clean axioms, no `sorry`)

* `pair_ea`, `pair_eb`.

## Honest scope

The pair handler's sub-result correctness.  The handler `Code`'s multiplicative assembly + eval, the other
handlers, the body, the interpreter, and the runtime remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode

open Nat.Partrec
open PallLean.Paper93.DeepMath.PathB.KleeneList (encodeList)
open PallLean.Paper93.DeepMath.PathB.KleeneRank (cfgRank cfgRank_lt_code)

theorem pair_ea (E B N k n : ℕ) (a b : UCode) (spec : ℕ → ℕ)
    (hec : (UCode.pair a b).enc ≤ E) (hn : n ≤ B) (hN : N = cfgRank E B k (UCode.pair a b).enc n) :
    lookupSubCode.eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N))))
        (Nat.pair k (Nat.pair a.enc n))) = Part.some (spec (cfgRank E B k a.enc n)) := by
  apply eval_lookupSubCode
  rw [hN]; exact cfgRank_lt_code E B k (UCode.pair a b).enc a.enc n n (enc_lt_pair_left a b) hec hn

theorem pair_eb (E B N k n : ℕ) (a b : UCode) (spec : ℕ → ℕ)
    (hec : (UCode.pair a b).enc ≤ E) (hn : n ≤ B) (hN : N = cfgRank E B k (UCode.pair a b).enc n) :
    lookupSubCode.eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N))))
        (Nat.pair k (Nat.pair b.enc n))) = Part.some (spec (cfgRank E B k b.enc n)) := by
  apply eval_lookupSubCode
  rw [hN]; exact cfgRank_lt_code E B k (UCode.pair a b).enc b.enc n n (enc_lt_pair_right a b) hec hn

end PallLean.Paper93.DeepMath.PathB.KleeneUCode

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.pair_ea
#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.pair_eb
