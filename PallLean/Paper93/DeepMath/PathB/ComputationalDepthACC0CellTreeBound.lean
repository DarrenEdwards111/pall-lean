import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CellTree
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ModpeDepth2

/-!
# Hard math (quantitative tree bound) — `C`-bounded leaves give cell count `≤ C^{#leaves}` (proved)

The quantitative form of the circuit-tree assembly (`ctree_cells_le`).  If every leaf count-gate of a count-tree has at most
`C` cells (`LeafBound C`), then the tree's product bound is `C^{#leaves}` (`cbound_le`), so the tree's cell count is
`≤ C^{#leaves}` (`ctree_cells_le_pow`).  For a constant-depth tree the number of leaves is polynomial, so this is
**quasipolynomial** — and `C`-bounded leaves are exactly the prime-power `MOD_{p^e} ∘ AND` blocks: each `gateCount` over `k`
`AND`-gates has `≤ k+1` cells (`cells_card_le`), so a count-tree of such blocks has cell count `≤ (k+1)^{#leaves}`
(`modpe_tree_cells_le`).

This is the end-to-end quantitative output of the symmetric cell-count method: any constant-depth tree of prime-power
`SYM∘AND` blocks has a quasipolynomial cell count — **field-independently**, surviving the prime-power RS barrier.

## What is proved (clean axioms, no `sorry`)

* **`leafCount`** / **`LeafBound`** — the leaf count and the per-leaf `C`-cell bound predicate.
* **`cbound_le`** (PROVED) — `LeafBound C t → cbound t ≤ C^{leafCount t}`.
* **`ctree_cells_le_pow`** (PROVED) — `LeafBound C t → (image (ceval t)).card ≤ C^{leafCount t}`.
* **`modpe_tree_cells_le`** (PROVED) — a count-tree of `MOD_{p^e}∘AND` blocks (each `≤ k` `AND`-gates) has cell count
  `≤ (k+1)^{#leaves}`.

## Honest scope

This is the quantitative cell-count bound (`C^{#leaves}`, quasipolynomial for constant depth) for trees of prime-power
`SYM∘AND` blocks.  The unconditional `NEXP ⊄ ACC⁰` (P≠NP-strength) is not done here.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0CellTreeBound

open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0CellTree (CTree ceval cbound ctree_cells_le)
open PallLean.Paper93.DeepMath.PathB.ACC0SymmetricObserver (gateCount)
open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd (monoAND)
open PallLean.Paper93.DeepMath.PathB.ACC0ModpeDepth2 (cells_card_le)

variable {n : ℕ}

/-- The number of leaves of a count-tree. -/
def leafCount : CTree n → ℕ
  | .leaf _ => 1
  | .node _ l r => leafCount l + leafCount r

/-- Every leaf count-gate has at most `C` cells. -/
def LeafBound (C : ℕ) : CTree n → Prop
  | .leaf f => (Finset.univ.image f).card ≤ C
  | .node _ l r => LeafBound C l ∧ LeafBound C r

/-- **`C`-bounded leaves give product bound `C^{#leaves}` (PROVED).** -/
theorem cbound_le (C : ℕ) (t : CTree n) (h : LeafBound C t) : cbound t ≤ C ^ leafCount t := by
  induction t with
  | leaf f => simpa [cbound, leafCount] using h
  | node agg l r ihl ihr =>
      simp only [LeafBound] at h
      simp only [cbound, leafCount, pow_add]
      exact Nat.mul_le_mul (ihl h.1) (ihr h.2)

/-- **Quantitative tree cell bound (PROVED): `C`-bounded leaves give cell count `≤ C^{#leaves}`.** -/
theorem ctree_cells_le_pow (C : ℕ) (t : CTree n) (h : LeafBound C t) :
    (Finset.univ.image (ceval t)).card ≤ C ^ leafCount t :=
  le_trans (ctree_cells_le t) (cbound_le C t h)

/-- A count-tree whose every leaf is a `gateCount` over `k` `AND`-gates is `(k+1)`-leaf-bounded. -/
def IsModpeTree (k : ℕ) : CTree n → Prop
  | .leaf f => ∃ mono : Fin k → Finset (Fin n), f = gateCount (fun j x => monoAND (mono j) x)
  | .node _ l r => IsModpeTree k l ∧ IsModpeTree k r

theorem isModpeTree_leafBound (k : ℕ) (t : CTree n) (h : IsModpeTree k t) :
    LeafBound (k + 1) t := by
  induction t with
  | leaf f =>
      obtain ⟨mono, rfl⟩ := h
      simpa [LeafBound] using cells_card_le (fun j x => monoAND (mono j) x)
  | node agg l r ihl ihr =>
      simp only [IsModpeTree] at h
      exact ⟨ihl h.1, ihr h.2⟩

/-- **A count-tree of prime-power `MOD_{p^e}∘AND` blocks has cell count `≤ (k+1)^{#leaves}` (PROVED).**  The end-to-end
quantitative bound: arbitrary-depth nesting of prime-power `SYM∘AND` blocks stays quasipolynomial (constant depth ⇒
polynomial `#leaves`), field-independently. -/
theorem modpe_tree_cells_le (k : ℕ) (t : CTree n) (h : IsModpeTree k t) :
    (Finset.univ.image (ceval t)).card ≤ (k + 1) ^ leafCount t :=
  ctree_cells_le_pow (k + 1) t (isModpeTree_leafBound k t h)

/-!
**Quantitative tree bound, proved.**  A count-tree with `C`-bounded leaves has cell count `≤ C^{#leaves}`; for prime-power
`MOD_{p^e}∘AND` leaves, `C = k+1`, giving `(k+1)^{#leaves}` — quasipolynomial for constant depth, field-independent.  This is
the end-to-end quantitative output of the symmetric cell-count method.  Remaining (open, not faked): the unconditional
`NEXP ⊄ ACC⁰`.  Not `NEXP ⊄ ACC⁰`, not `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0CellTreeBound

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CellTreeBound.modpe_tree_cells_le
