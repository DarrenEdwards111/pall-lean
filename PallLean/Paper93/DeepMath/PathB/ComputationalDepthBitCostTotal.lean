import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBitCostInterpReads
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBitCostArith

/-!
# Bit-cost model — total per-step cost is polynomial (PROVED) — flat DP cost-model capstone

Combining the two halves:

* reads — `interp_flat_dp_poly` : `≤ 3·P²` (fully discharged; the `≤3`-reads-at-lower-rank structure is
  *proven* for the concrete `interpReads`).
* arithmetic — `interp_arith_poly` : `≤ P·(Σ_{t<9} g t)·s²` (op count bounded by a constant — the dispatch
  selects one of 9 fixed handler Codes).

the flat/`List` DP's **total per-step cost** at the diagonal is `≤ 3·P² + P·(Σ_{t<9} g t)·s²`,
`P = (B+1)²(E+1)+1` — **polynomial** in `(B, E, s)` (`interp_total_cost_poly`).

This is the efficient-simulation cost bound in a bit-cost / addressable-memory model: the universal
interpreter's memoised DP, stored flat, runs in polynomially many bit-operations — the polynomial counterpart
of the `≥ 2 ^ cfgRank` runtime under the magnitude-charging `Code.evaln` fuel measure
(`ComputationalDepthKleeneMemoBlowup`).  The sole remaining input is the operand bit-length `s` (polynomial
for bit-bounded computations).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

open PallLean.Paper93.DeepMath.PathB.KleeneRank (cfgRank)

namespace PallLean.Paper93.DeepMath.PathB.BitCost

/-- **The flat/List DP's TOTAL per-step cost (reads + arithmetic) at the diagonal is polynomial.** -/
theorem interp_total_cost_poly (g : ℕ → ℕ) (E B K ec n s : ℕ)
    (hK : K ≤ B) (hec : ec ≤ E) (hn : n ≤ B) :
    buildReadCost (interpReads E B) (cfgRank E B K ec n + 1)
        + buildArithCost (fun M => g (cappedTag E B M)) s (cfgRank E B K ec n + 1)
      ≤ 3 * ((B + 1) * (B + 1) * (E + 1) + 1) * ((B + 1) * (B + 1) * (E + 1) + 1)
        + ((B + 1) * (B + 1) * (E + 1) + 1) * (((List.range 9).map g).sum * opBitCost s) :=
  Nat.add_le_add (interp_flat_dp_poly E B K ec n hK hec hn) (interp_arith_poly g E B K ec n s hK hec hn)

end PallLean.Paper93.DeepMath.PathB.BitCost

#print axioms PallLean.Paper93.DeepMath.PathB.BitCost.interp_total_cost_poly
