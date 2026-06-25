import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBitCostModel
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneRank
import Mathlib.Tactic

/-!
# Bit-cost model — the operation count is polynomial (PROVED)

The memoised DP `buildTableCtx interpBody` fills exactly `cfgRank E B K c0.enc n0 + 1` cells.  Within the
bubble (`K ≤ B`, `c0.enc ≤ E`, `n0 ≤ B`) that rank is `≤ (B+1)²(E+1)` — **polynomial** in `(B, E)`.  So the
simulator performs only polynomially many cell operations; the exponential blow-up of
`ComputationalDepthKleeneMemoBlowup` lives entirely in the *single-`Nat` encoding* of the table, not in the
number of steps.  This is the operation-count half of a bit-cost bound.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

open PallLean.Paper93.DeepMath.PathB.KleeneRank (cfgRank)

namespace PallLean.Paper93.DeepMath.PathB.BitCost

/-- **The DP cell count (number of RAM operations) is polynomial in `(B, E)`.** -/
theorem cfgRank_le_poly (E B K ec n : ℕ) (hK : K ≤ B) (hec : ec ≤ E) (hn : n ≤ B) :
    cfgRank E B K ec n ≤ (B + 1) * (B + 1) * (E + 1) := by
  unfold cfgRank
  have hKe : K * (E + 1) ≤ B * (E + 1) := mul_le_mul_right' hK (E + 1)
  have h1 : K * (E + 1) + ec + 1 ≤ (B + 1) * (E + 1) := by nlinarith [hKe, hec]
  have h2 : (K * (E + 1) + ec + 1) * (B + 1) ≤ (B + 1) * (E + 1) * (B + 1) := mul_le_mul_right' h1 (B + 1)
  nlinarith [h2, hn]

end PallLean.Paper93.DeepMath.PathB.BitCost

#print axioms PallLean.Paper93.DeepMath.PathB.BitCost.cfgRank_le_poly
