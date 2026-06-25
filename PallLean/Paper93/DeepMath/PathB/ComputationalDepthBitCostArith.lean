import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBitCostModel
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBitCostCellCount
import Mathlib.Tactic

/-!
# Bit-cost model — the per-cell arithmetic cost is polynomial (PROVED)

Beyond the table reads (`ComputationalDepthBitCostFlatDP`/`...InterpReads`), each cell also runs the handler's
arithmetic (`isPos`/`mul`/`add`/`pair`/…).  One such op on operands of bit-length `≤ s` costs `≤ s²`
(schoolbook, `opBitCost`).  A cell running `≤ C` ops costs `≤ C·s²`; summed over `N` cells, `≤ N·C·s²`
(`buildArithCost_le`).

The op count is **bounded by a constant** with no asserted numbers: the dispatch selects one of finitely many
(9, via `capCode`) **fixed** handler Codes, so the per-cell op count depends only on the *capped tag*, hence
`g (cappedTag E B M) ≤ Σ_{t<9} g t` for any per-tag count `g` (`ops_le_const`).  Therefore at the diagonal
the arithmetic cost is `≤ P · (Σ_{t<9} g t) · s²`, `P = (B+1)²(E+1)+1` — **polynomial**
(`interp_arith_poly`), given operand bit-length `≤ s`.

Combined with `interp_flat_dp_poly` (read cost `≤ 3·P²`), the flat/`List` DP's *total* per-step cost is
polynomial in `(B, E, s)`.  The only remaining input is the operand bit-length bound `s` (poly for
bit-bounded computations).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

open PallLean.Paper93.DeepMath.PathB.KleeneRank (cfgRank)

namespace PallLean.Paper93.DeepMath.PathB.BitCost

/-- Bit-cost of one arithmetic op (add/mul/pair/…) on operands of bit-length `≤ s` (schoolbook: `s²`). -/
def opBitCost (s : ℕ) : ℕ := s * s

/-- Total arithmetic bit-cost of the flat DP: cell `M` performs `opsOf M` ops, each costing `opBitCost s`. -/
def buildArithCost (opsOf : ℕ → ℕ) (s N : ℕ) : ℕ :=
  ((List.range N).map (fun M => opsOf M * opBitCost s)).sum

/-- **The flat DP's total arithmetic cost is `≤ N · C · s²`** when each cell runs `≤ C` ops on `≤ s`-bit
operands. -/
theorem buildArithCost_le (opsOf : ℕ → ℕ) (C s N : ℕ) (h : ∀ M, M < N → opsOf M ≤ C) :
    buildArithCost opsOf s N ≤ N * (C * opBitCost s) := by
  have hcells : buildArithCost opsOf s N
      ≤ ((List.range N).map (fun M => opsOf M * opBitCost s)).length • (C * opBitCost s) := by
    apply List.sum_le_card_nsmul
    intro x hx
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨M, hM, rfl⟩ := hx
    exact Nat.mul_le_mul_right (opBitCost s) (h M hM)
  simpa only [List.length_map, List.length_range, smul_eq_mul] using hcells

/-- The capped constructor tag of cell `M` (matching the dispatch's `capCode`): `≤ 8`. -/
def cappedTag (E B M : ℕ) : ℕ := min (Nat.unpair ((M / (B + 1)) % (E + 1))).1 8

/-- **The per-cell op count depends only on the capped tag, hence is bounded by a constant** (the sum of the
op counts of the finitely many — 9 — handlers): for any per-tag op count `g`,
`g (cappedTag E B M) ≤ Σ_{t<9} g t`. -/
theorem ops_le_const (g : ℕ → ℕ) (E B M : ℕ) :
    g (cappedTag E B M) ≤ ((List.range 9).map g).sum := by
  apply List.single_le_sum (fun x _ => Nat.zero_le x)
  apply List.mem_map_of_mem
  rw [List.mem_range]
  exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)

/-- **The flat DP's total arithmetic cost at the diagonal is polynomial.** -/
theorem interp_arith_poly (g : ℕ → ℕ) (E B K ec n s : ℕ) (hK : K ≤ B) (hec : ec ≤ E) (hn : n ≤ B) :
    buildArithCost (fun M => g (cappedTag E B M)) s (cfgRank E B K ec n + 1)
      ≤ ((B + 1) * (B + 1) * (E + 1) + 1) * (((List.range 9).map g).sum * opBitCost s) := by
  set P := (B + 1) * (B + 1) * (E + 1) + 1 with hP
  have hbase := buildArithCost_le (fun M => g (cappedTag E B M)) (((List.range 9).map g).sum) s
    (cfgRank E B K ec n + 1) (fun M _ => ops_le_const g E B M)
  have hcells : cfgRank E B K ec n + 1 ≤ P := by
    have := cfgRank_le_poly E B K ec n hK hec hn; omega
  exact hbase.trans (Nat.mul_le_mul_right _ hcells)

end PallLean.Paper93.DeepMath.PathB.BitCost

#print axioms PallLean.Paper93.DeepMath.PathB.BitCost.interp_arith_poly
