import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBitCostModel
import Mathlib.Tactic

/-!
# Bit-cost model — the flat/List DP per-step cost model (PROVED)

The efficient reformulation: build the memo table as an addressable flat list, where a cell reads earlier
cells *by rank*.  Reading rank `r` from a flat list costs `r + 1` (list access).  A cell that reads `≤ R`
ranks, all `< N`, costs `≤ R · N` (`cellReadCost_le`); summed over `N` cells, the whole flat DP costs
`≤ R · N²` (`buildReadCost_le`) — **polynomial**, in sharp contrast to the `Code.evaln` fuel measure on the
single-`Nat` table (`≥ 2 ^ N`, `ComputationalDepthKleeneMemoBlowup`).

For the universal interpreter each cell reads `≤ 2` sub-cells (the constructor arity), all at strictly lower
rank (the well-foundedness lemmas `cfgRank_lt_code` / `cfgRank_lt_fuel`), so `R = 2` and the read cost is
`≤ 2 N²`.  This is the per-step cost model the efficient simulator runs in.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.BitCost

/-- Cost of the table reads a single cell performs: reading rank `r` from a flat list costs `r + 1`
(list access traverses `r+1` nodes). -/
def cellReadCost (reads : List ℕ) : ℕ := (reads.map (· + 1)).sum

/-- Total read cost of the flat DP building `N` cells, cell `M` reading the ranks `readsOf M`. -/
def buildReadCost (readsOf : ℕ → List ℕ) (N : ℕ) : ℕ :=
  ((List.range N).map (fun M => cellReadCost (readsOf M))).sum

/-- **Per-cell read cost is `≤ R · N`** when a cell reads `≤ R` ranks, all `< N`. -/
theorem cellReadCost_le (reads : List ℕ) (R N : ℕ)
    (hlt : ∀ r ∈ reads, r < N) (hlen : reads.length ≤ R) :
    cellReadCost reads ≤ R * N := by
  have h1 : cellReadCost reads ≤ (reads.map (· + 1)).length • N := by
    apply List.sum_le_card_nsmul
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨r, hr, rfl⟩ := hx
    exact hlt r hr
  simp only [List.length_map, smul_eq_mul] at h1
  exact h1.trans (Nat.mul_le_mul_right N hlen)

/-- **The flat DP's total read cost is `≤ R · N²`** (polynomial): `N` cells, each reading `≤ R` ranks `< N`. -/
theorem buildReadCost_le (readsOf : ℕ → List ℕ) (R N : ℕ)
    (h : ∀ M, M < N → (∀ r ∈ readsOf M, r < N) ∧ (readsOf M).length ≤ R) :
    buildReadCost readsOf N ≤ R * N * N := by
  have hcells : buildReadCost readsOf N
      ≤ ((List.range N).map (fun M => cellReadCost (readsOf M))).length • (R * N) := by
    apply List.sum_le_card_nsmul
    intro x hx
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨M, hM, rfl⟩ := hx
    exact cellReadCost_le (readsOf M) R N (h M hM).1 (h M hM).2
  simp only [List.length_map, List.length_range, smul_eq_mul] at hcells
  calc buildReadCost readsOf N ≤ N * (R * N) := hcells
    _ = R * N * N := by ring

end PallLean.Paper93.DeepMath.PathB.BitCost

#print axioms PallLean.Paper93.DeepMath.PathB.BitCost.buildReadCost_le
