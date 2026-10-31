import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBitCostFlatDP
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBitCostCellCount
import Mathlib.Tactic

/-!
# Bit-cost model — the flat DP runs in polynomial read-cost at the diagonal (PROVED)

Combining the flat-DP cost model (`buildReadCost_le`, `≤ R·N²`) with the polynomial cell count
(`cfgRank_le_poly`, `N ≤ (B+1)²(E+1)`): for any cell-read schedule with `≤ 2` reads per cell (the
interpreter's constructor arity), all at strictly lower rank, the total read cost over the
`cfgRank E B K ec n + 1` cells is `≤ 2·P²` with `P = (B+1)²(E+1)+1` — **polynomial** in `(B, E)`
(`diagonal_flat_dp_poly`).

The read-structure hypothesis (`≤ 2` reads, all `< N`) is the well-foundedness of the DP recurrence: every
handler reads at most two sub-cells, each at strictly lower rank by `cfgRank_lt_code` / `cfgRank_lt_fuel`
(with the value bounds ensuring read inputs stay `≤ B`).  It is stated as an explicit hypothesis here; its
instantiation for the concrete interpreter `readsOf` is the remaining mechanical connection.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

open PallLean.Paper93.DeepMath.PathB.KleeneRank (cfgRank)

namespace PallLean.Paper93.DeepMath.PathB.BitCost

/-- **The flat DP at the diagonal target runs in polynomial read-cost.** -/
theorem diagonal_flat_dp_poly (E B K ec n : ℕ) (readsOf : ℕ → List ℕ)
    (hK : K ≤ B) (hec : ec ≤ E) (hn : n ≤ B)
    (hreads : ∀ M, M < cfgRank E B K ec n + 1 →
      (∀ r ∈ readsOf M, r < cfgRank E B K ec n + 1) ∧ (readsOf M).length ≤ 2) :
    buildReadCost readsOf (cfgRank E B K ec n + 1)
      ≤ 2 * ((B + 1) * (B + 1) * (E + 1) + 1) * ((B + 1) * (B + 1) * (E + 1) + 1) := by
  set P := (B + 1) * (B + 1) * (E + 1) + 1 with hP
  have hcells : cfgRank E B K ec n + 1 ≤ P := by
    have := cfgRank_le_poly E B K ec n hK hec hn; omega
  have hbase : buildReadCost readsOf (cfgRank E B K ec n + 1)
      ≤ 2 * (cfgRank E B K ec n + 1) * (cfgRank E B K ec n + 1) :=
    buildReadCost_le readsOf 2 (cfgRank E B K ec n + 1) hreads
  calc buildReadCost readsOf (cfgRank E B K ec n + 1)
        ≤ 2 * (cfgRank E B K ec n + 1) * (cfgRank E B K ec n + 1) := hbase
    _ ≤ 2 * P * P := by
        have h1 : 2 * (cfgRank E B K ec n + 1) ≤ 2 * P := by omega
        exact Nat.mul_le_mul h1 hcells

end PallLean.Paper93.DeepMath.PathB.BitCost

#print axioms PallLean.Paper93.DeepMath.PathB.BitCost.diagonal_flat_dp_poly
