import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneReaderGen

/-!
# Kleene interpreter project — identity code + self lower-fuel reader (PROVED)

`prec`/`rfind'` recurse on **themselves** (same code `ec`) at a *lower* fuel.  To read the same code via the
universal reader, the subcode-extractor must be the identity (return its input `ec`); `idCode := pair left
right` is identity (`eval idCode x = x` by `Nat.pair_unpair`).  `self_lower_reader` then reads `ec` at any
lower fuel `kv < k`, discharging `rank < N` via `cfgRank_lt_fuel`.

  `idCode`, `eval_idCode`, `self_lower_reader`.

## What is proved (clean axioms, no `sorry`)

* `idCode`, `eval_idCode`, `self_lower_reader`.

## Honest scope

The self lower-fuel reader (the `prec`/`rfind'` recursive read).  Their handler `Code`s, the body, the
interpreter, and the runtime remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode

open Nat.Partrec
open PallLean.Paper93.DeepMath.PathB.KleeneList (encodeList)
open PallLean.Paper93.DeepMath.PathB.KleeneRank (cfgRank cfgRank_lt_fuel)

/-- Identity code: `pair left right` returns its input (`Nat.pair_unpair`). -/
def idCode : Code := Code.pair Code.left Code.right

theorem eval_idCode (x : ℕ) : idCode.eval x = Part.some x := by
  show (Code.pair Code.left Code.right).eval x = _
  rw [show (Code.pair Code.left Code.right).eval x
      = Part.some (Nat.pair (Nat.unpair x).1 (Nat.unpair x).2) from ?_]
  · rw [Nat.pair_unpair]
  · exact pair_eval _ _ _ _ _ (by simp [Code.eval]) (by simp [Code.eval])

/-- **Self lower-fuel reader (proved): read the same code `ec` at a lower fuel `kv < k`.** -/
theorem self_lower_reader (kSource nSource : Code) (kv nv : ℕ) (E B N k n ecv : ℕ) (spec : ℕ → ℕ)
    (hks : kSource.eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N))))
        (Nat.pair k (Nat.pair ecv n))) = Part.some kv)
    (hns : nSource.eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N))))
        (Nat.pair k (Nat.pair ecv n))) = Part.some nv)
    (hkv : kv < k) (hec : ecv ≤ E) (hnv : nv ≤ B) (hN : N = cfgRank E B k ecv n) :
    (readerGen idCode kSource nSource).eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N))))
        (Nat.pair k (Nat.pair ecv n))) = Part.some (spec (cfgRank E B kv ecv nv)) :=
  reader_gen_correct idCode kSource nSource ecv kv nv E B N k n ecv spec (eval_idCode ecv) hks hns
    (by rw [hN]; exact cfgRank_lt_fuel E B k kv ecv ecv n nv hkv hec hnv)

end PallLean.Paper93.DeepMath.PathB.KleeneUCode

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.self_lower_reader
