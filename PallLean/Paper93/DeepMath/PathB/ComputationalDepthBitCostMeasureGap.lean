import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBitCostInterpReads
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneMemoBlowup

/-!
# Bit-cost model — the measure gap to `DiagRuntimePolyBounded` (PROVED, honest bridge status)

The EffSim Williams ingredient `DiagRuntimePolyBounded` (`ComputationalDepthACC0EffSimWall`) is stated in the
`Code.evaln` **fuel** measure (`runtimeOf = least halting fuel`), which — via the `n ≤ k` guard — charges by
the *magnitude* of intermediate values.  This file records, as one theorem, why the bit-cost efficient
simulation does **not** discharge it.

`read_vs_value_divergence`: for the diagonal target, the flat/addressable DP read-cost is `≤ 3·P²`
(`P=(B+1)²(E+1)+1`, polynomial — `interp_flat_dp_poly`), **while** the value `buildTableCtx interpBody`
produces is `≥ 2 ^ cfgRank` (`diagonal_memo_table_exp`).  The fuel measure charges by that value; the bit-cost
measure does not.  So the two measures diverge super-polynomially on the *same* construction, and bit-cost
efficiency cannot bridge to the fuel-measure hypothesis `DiagRuntimePolyBounded`.

**Honest bridge status.**  The gap to Williams is exactly the cost *measure*, not the construction:

* In the **bit-cost / addressable** model the simulation is polynomial (this arc — `bitBounded_efficient`).
* In the **`Code.evaln` fuel** model the single-`Nat` memo encoding is exponential (`MemoBlowup`), so
  `DiagRuntimePolyBounded` is *not* discharged by this construction.

Closing it in the fuel measure would require a fundamentally different `Code` (one whose `evaln` never holds a
super-polynomial intermediate value) — open, and plausibly as hard as the Hennie–Stearns ingredient itself.
This is stated, not papered over.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

open PallLean.Paper93.DeepMath.PathB.KleeneUCode
open PallLean.Paper93.DeepMath.PathB.KleeneRank (cfgRank)
open Nat.Partrec

namespace PallLean.Paper93.DeepMath.PathB.BitCost

/-- **Measure divergence: the same memo-DP is polynomial in flat read-cost but exponential in single-`Nat`
value** (the quantity the `Code.evaln` fuel measure of `DiagRuntimePolyBounded` charges by). -/
theorem read_vs_value_divergence (E B K n0 : ℕ) (c0 : UCode)
    (hKB : K ≤ B) (hcE : c0.enc < E + 1) (hn0 : n0 < B + 1) :
    buildReadCost (interpReads E B) (cfgRank E B K c0.enc n0 + 1)
        ≤ 3 * ((B + 1) * (B + 1) * (E + 1) + 1) * ((B + 1) * (B + 1) * (E + 1) + 1)
    ∧ ∃ v, (buildTableCtx interpBody).eval (Nat.pair (Nat.pair E B) (cfgRank E B K c0.enc n0 + 1))
          = Part.some v
        ∧ 2 ^ (cfgRank E B K c0.enc n0) ≤ v :=
  ⟨interp_flat_dp_poly E B K c0.enc n0 hKB (by omega) (by omega),
   diagonal_memo_table_exp E B K n0 c0 hKB hcE hn0⟩

end PallLean.Paper93.DeepMath.PathB.BitCost

#print axioms PallLean.Paper93.DeepMath.PathB.BitCost.read_vs_value_divergence
