import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBitCostFlatTable
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneSpec

/-!
# Bit-cost model — connection to the verified interpreter (PROVED)

The capstone of the bit-cost foundations: the memo table that the verified universal interpreter
(`universalInterp`, `ComputationalDepthKleeneUniversalInterp`) builds at the diagonal — whose top cell is the
correct `encodeOpt (Code.evaln K c0.toCode n0)` — has, **stored flat**, bit-size `≤ (B+1)²(E+1)·S` where `S`
bounds each cell's bit-length (`interp_flat_table_poly`).  Contrast the single-`Nat` `encodeList` value, which
is `≥ 2 ^ cfgRank` (`ComputationalDepthKleeneMemoBlowup`).

So under a bit-cost measure with addressable (flat) storage, the interpreter's table is polynomial-size,
**given poly-bit-length cell values** (the hypothesis `hcells`).

## Honest remaining gaps (the genuine difficulty, not mechanical)

* **Per-step bit-cost.** Bounding the *work* per cell (table reads + handler arithmetic) by poly bit-ops
  needs a cost model over the operations themselves, and a flat/`List`-based reformulation of the DP (the
  `Code`-level `buildTableCtx` reads via `unpair` on the giant `Nat`, which is not bit-cheap).
* **Poly-bit-length cells (`hcells`).** This is a real restriction, not a formality: in the Kleene model a
  `Code` can produce a doubly-exponential value from poly fuel (`Nat.pair` squares magnitude — `pair_ge_sq`),
  so `bitlen (specOf E B M)` is poly only for bit-bounded computations (e.g. decision problems with small
  intermediate values), not for all poly-fuel ones.

These are where efficient simulation is genuinely hard; they are stated, not papered over.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

open PallLean.Paper93.DeepMath.PathB.KleeneUCode
open PallLean.Paper93.DeepMath.PathB.KleeneRank (cfgRank)

namespace PallLean.Paper93.DeepMath.PathB.BitCost

/-- **The verified interpreter's memo table, stored flat, has polynomial bit-size** (given poly-bit-length
cell values): `≤ (B+1)²(E+1)·S` bits, versus `≥ 2 ^ cfgRank` as one `Nat`. -/
theorem interp_flat_table_poly (E B K n0 S : ℕ) (c0 : UCode)
    (hK : K ≤ B) (hcE : c0.enc ≤ E) (hn0 : n0 ≤ B)
    (hcells : ∀ M, M < cfgRank E B K c0.enc n0 + 1 → bitlen (specOf E B M) ≤ S) :
    listBitSize (tableList (specOf E B) (cfgRank E B K c0.enc n0 + 1))
      ≤ ((B + 1) * (B + 1) * (E + 1) + 1) * S :=
  diagonal_flat_table_poly E B K c0.enc n0 S (specOf E B) hK hcE hn0 hcells

end PallLean.Paper93.DeepMath.PathB.BitCost

#print axioms PallLean.Paper93.DeepMath.PathB.BitCost.interp_flat_table_poly
