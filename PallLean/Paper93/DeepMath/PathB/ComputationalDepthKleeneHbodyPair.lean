import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleenePairHandlerGen
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneSpec
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneUEvalnEqs
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneEncodeOpt

/-!
# Kleene interpreter project — `hbody` pair case (PROVED) — validates the full chain

The per-cell correctness for the `pair` constructor: on a tag-4 config, the (generic) `pair` handler — fed
`spec = specOf E B` — evaluates to `specOf E B (cfgRank …)`.  This chains every ingredient end-to-end:

  `eval_pairHandler_gen` (handler value, general `ec`)
    → `spec_cfgRank` (sub-rank reads = `encodeOpt (UCode.evaln k (decodeU sub) n)`)
    → `decodeU_tag4` (`decodeU ec = pair …`)
    → `uevaln_pair` (`UCode.evaln`'s pair equation)
    → `encode_pair_step` (the multiplicative ↔ encoded-result identity)
  = `specOf E B (cfgRank …)`.

The `comp`/`prec`/`rfind'`/base cases follow the identical pattern (with their own handler/identity/equation).

## What is proved (clean axioms, no `sorry`)

* `decodeU_tag4`, `hbody_pair_case`.

## Honest scope

The `pair` case of `hbody`, validating the chain.  The other cases, the dispatch assembly, `hbody` proper,
the interpreter, and the runtime remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode

open Nat.Partrec
open PallLean.Paper93.DeepMath.PathB.KleeneList (encodeList)
open PallLean.Paper93.DeepMath.PathB.KleeneRank (cfgRank)

/-- `decodeU` unfold on a tag-4 number. -/
theorem decodeU_tag4 (ec : ℕ) (htag : (Nat.unpair ec).1 = 4) :
    decodeU ec = UCode.pair (decodeU (Nat.unpair (Nat.unpair ec).2).1) (decodeU (Nat.unpair (Nat.unpair ec).2).2) := by
  conv_lhs => rw [decodeU, htag]

/-- **`hbody` pair case (proved): the generic `pair` handler computes `specOf` on a tag-4 config.** -/
theorem hbody_pair_case (E B k' n ec : ℕ) (htag : (Nat.unpair ec).1 = 4) (hec : ec ≤ E) (hn : n ≤ B) :
    pairHandler.eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair (cfgRank E B (k'+1) ec n) (encodeList (tableList (specOf E B) (cfgRank E B (k'+1) ec n))))) (Nat.pair (k'+1) (Nat.pair ec n)))
      = Part.some (specOf E B (cfgRank E B (k'+1) ec n)) := by
  have hsa : (Nat.unpair (Nat.unpair ec).2).1 < E + 1 := lt_of_lt_of_le (fstSub_lt ec (by omega)) (by omega)
  have hsb : (Nat.unpair (Nat.unpair ec).2).2 < E + 1 := lt_of_lt_of_le (sndSub_lt ec (by omega)) (by omega)
  have hnB : n < B + 1 := by omega
  rw [eval_pairHandler_gen E B (cfgRank E B (k'+1) ec n) (k'+1) n ec (specOf E B) (by omega) hec hn rfl]
  rw [spec_cfgRank E B (k'+1) (Nat.unpair (Nat.unpair ec).2).1 n hsa hnB,
      spec_cfgRank E B (k'+1) (Nat.unpair (Nat.unpair ec).2).2 n hsb hnB]
  rw [spec_cfgRank E B (k'+1) ec n (by omega) hnB, decodeU_tag4 ec htag, uevaln_pair k' n,
      encode_pair_step k' n (UCode.evaln (k'+1) (decodeU (Nat.unpair (Nat.unpair ec).2).1) n) (UCode.evaln (k'+1) (decodeU (Nat.unpair (Nat.unpair ec).2).2) n)]
  simp only [Nat.add_sub_cancel]

end PallLean.Paper93.DeepMath.PathB.KleeneUCode

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.hbody_pair_case
