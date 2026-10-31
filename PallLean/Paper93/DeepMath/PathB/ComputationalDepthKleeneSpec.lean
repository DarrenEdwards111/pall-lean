import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneEncodeOpt
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneDecodeU
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneRankDecode
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneUEvaln

/-!
# Kleene interpreter project — the table specification `specOf` (PROVED)

The intended contents of the DP table.  At a rank `N` (relative to dimensions `E, B`), the config `(k, ec, n)`
is recovered by the `cfgRank` division formula, and the cell should hold the encoded `evaln` of that config:

  `specOf E B N := encodeOpt (UCode.evaln (N/(B+1)/(E+1)) (decodeU ((N/(B+1)) % (E+1))) (N % (B+1)))`.

It is total on all numbers (via `decodeU`), and on a genuine rank it reads the right value:

  `spec_cfgRank` — `specOf E B (cfgRank E B k ec n) = encodeOpt (UCode.evaln k (decodeU ec) n)` (`ec<E+1`,
    `n<B+1`).

For a valid config `ec = enc u`, `decodeU ec = u` (`decode_enc`), so this is `encodeOpt (UCode.evaln k u n) =
encodeOpt (Code.evaln k u.toCode n)` — exactly what the table should compute.

## What is proved (clean axioms, no `sorry`)

* `specOf`, `spec_cfgRank`.

## Honest scope

The table specification.  `hbody` (the body computes `specOf`), the interpreter, and the runtime remain.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode

open PallLean.Paper93.DeepMath.PathB.KleeneRank (cfgRank cfgRank_decode)

/-- Intended table contents at rank `N` (relative to dimensions `E, B`). -/
noncomputable def specOf (E B N : ℕ) : ℕ :=
  encodeOpt (UCode.evaln (N / (B + 1) / (E + 1)) (decodeU ((N / (B + 1)) % (E + 1))) (N % (B + 1)))

/-- **`specOf` at a genuine rank (proved).** -/
theorem spec_cfgRank (E B k ec n : ℕ) (hec : ec < E + 1) (hn : n < B + 1) :
    specOf E B (cfgRank E B k ec n) = encodeOpt (UCode.evaln k (decodeU ec) n) := by
  obtain ⟨hmod, hecd, hkd⟩ := cfgRank_decode E B k ec n hec hn
  unfold specOf
  rw [hkd, hecd, hmod]

end PallLean.Paper93.DeepMath.PathB.KleeneUCode

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.spec_cfgRank
