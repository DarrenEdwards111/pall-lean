import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CellCountRoute

/-!
# Block-product supports: cell count is the *product* of per-block cell counts

A **block-product** support system stacks `m` independent blocks of `b` gates each (`supports : Fin m → Fin b →
Finset (Fin n)`).  The cell pattern of a coordinate `v` is the *tuple* of its per-block patterns, so the number of
distinct cells is at most the **product** of the per-block cell counts — the `m`-fold generalisation of the binary
`cellPatternCount_append_le` (`…ACC0CellCountComposition`):

```
blockCellCount supports L  ≤  ∏ i, cellPatternCount (supports i) L   ( ≤ cᵐ if each block has ≤ c cells).
```

Flattening the blocks to a single `Fin (m·b)` gate index (`flatSupports`, via `finProdFinEquiv`) realises this as an
honest `cellPatternCount`, so a block product of low-cell blocks collapses and fails to correlate.

## What is proved (clean axioms, no `sorry`)

* `blockCellCount` / `flatSupports` — the tuple cell count, and the flattened `Fin (m·b)` support family.
* **`blockCellCount_le_prod`** — `blockCellCount supports L ≤ ∏ i, cellPatternCount (supports i) L`
  (the tuple map injects into `Fintype.piFinset` of the per-block images; `Fintype.card_piFinset`).
* **`blockCellCount_le_pow`** — the uniform corollary: each block `≤ c` cells ⇒ `blockCellCount ≤ cᵐ`.
* **`cellPatternCount_flat_eq`** — `cellPatternCount (flatSupports supports) L = blockCellCount supports L`
  (flattening is a relabelling of the gates; cell count is invariant under the `finProdFinEquiv` bijection).
* **`block_product_low_correlation`** — `(∏ i, cellPatternCount (supports i) L) < |L|` ⇒ `LowHolonomyCorrelation`.

## Honest scope

The composition multiplies cell counts: a block product stays low-cell only if *every* block does and the product
stays below `|L|` (e.g. `m` blocks each with `≤ c` cells need `cᵐ < |L|`).  A general `ACC⁰` system is not a low-cell
block product — forcing few cells under a restriction is the open observer lemma (`ACC0ForcesLowCellCount`).  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0BlockProductCellCount

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0CellCollapseRoute
open PallLean.Paper93.DeepMath.PathB.ACC0RankBridge
open PallLean.Paper93.DeepMath.PathB.ACC0CellCountRoute

variable {m b n : ℕ}

/-- The **block tuple cell count**: distinct tuples of per-block cell patterns over the live set. -/
def blockCellCount (supports : Fin m → Fin b → Finset (Fin n)) (L : Finset (Fin n)) : ℕ :=
  (L.image (fun v => fun i => cellPatternVec (supports i) v)).card

/-- The block family **flattened** to a single `Fin (m·b)` gate index, via `finProdFinEquiv`. -/
def flatSupports (supports : Fin m → Fin b → Finset (Fin n)) : Fin (m * b) → Finset (Fin n) :=
  fun e => supports (finProdFinEquiv.symm e).1 (finProdFinEquiv.symm e).2

/-- **The block cell count is at most the product of per-block cell counts (proved).**  The tuple map injects into the
`piFinset` of the per-block cell-pattern images. -/
theorem blockCellCount_le_prod (supports : Fin m → Fin b → Finset (Fin n)) (L : Finset (Fin n)) :
    blockCellCount supports L ≤ ∏ i, cellPatternCount (supports i) L := by
  unfold blockCellCount
  calc (L.image (fun v => fun i => cellPatternVec (supports i) v)).card
      ≤ (Fintype.piFinset (fun i => L.image (cellPatternVec (supports i)))).card := by
        apply Finset.card_le_card
        intro p hp
        rw [Finset.mem_image] at hp
        obtain ⟨v, hv, rfl⟩ := hp
        rw [Fintype.mem_piFinset]
        intro i
        exact Finset.mem_image_of_mem _ hv
    _ = ∏ i, (L.image (cellPatternVec (supports i))).card := Fintype.card_piFinset _
    _ = ∏ i, cellPatternCount (supports i) L := rfl

/-- **Uniform block bound (proved): every block has `≤ c` cells ⇒ `blockCellCount ≤ cᵐ`.** -/
theorem blockCellCount_le_pow (supports : Fin m → Fin b → Finset (Fin n)) (L : Finset (Fin n))
    (c : ℕ) (h : ∀ i, cellPatternCount (supports i) L ≤ c) :
    blockCellCount supports L ≤ c ^ m := by
  calc blockCellCount supports L
      ≤ ∏ i, cellPatternCount (supports i) L := blockCellCount_le_prod supports L
    _ ≤ ∏ _i : Fin m, c := Finset.prod_le_prod (fun i _ => Nat.zero_le _) (fun i _ => h i)
    _ = c ^ m := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **Flattening is a relabelling: the flattened cell count equals the block tuple count (proved).** -/
theorem cellPatternCount_flat_eq (supports : Fin m → Fin b → Finset (Fin n)) (L : Finset (Fin n)) :
    cellPatternCount (flatSupports supports) L = blockCellCount supports L := by
  have hΦinj : Function.Injective
      (fun w : Fin (m * b) → ZMod 2 => fun i j => w (finProdFinEquiv (i, j))) := by
    intro w w' hww
    funext e
    have key : e = finProdFinEquiv (finProdFinEquiv.symm e) :=
      (finProdFinEquiv.apply_symm_apply e).symm
    rw [key]
    obtain ⟨i, j⟩ := finProdFinEquiv.symm e
    exact congrFun (congrFun hww i) j
  unfold cellPatternCount cellPatternImage blockCellCount
  have hcomp : (fun v => fun i => cellPatternVec (supports i) v)
      = (fun w : Fin (m * b) → ZMod 2 => fun i j => w (finProdFinEquiv (i, j)))
          ∘ (cellPatternVec (flatSupports supports)) := by
    funext v i j
    simp only [Function.comp_apply, cellPatternVec, flatSupports, Equiv.symm_apply_apply]
  rw [hcomp, ← Finset.image_image, Finset.card_image_of_injective _ hΦinj]

/-- **A block product of low-cell blocks fails to correlate (proved).**  If the product of per-block cell counts is
below `|L|`, the flattened system collapses and the predictor cannot correlate with the holonomy parity. -/
theorem block_product_low_correlation (supports : Fin m → Fin b → Finset (Fin n))
    (g : (Fin (m * b) → ℕ) → Bool) (L : Finset (Fin n))
    (h : (∏ i, cellPatternCount (supports i) L) < L.card) :
    LowHolonomyCorrelation (flatSupports supports) g := by
  apply cellCountCollapse_implies_low_correlation (flatSupports supports) g L
  show cellPatternCount (flatSupports supports) L < L.card
  rw [cellPatternCount_flat_eq]
  exact lt_of_le_of_lt (blockCellCount_le_prod supports L) h

end PallLean.Paper93.DeepMath.PathB.ACC0BlockProductCellCount

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BlockProductCellCount.blockCellCount_le_prod
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BlockProductCellCount.blockCellCount_le_pow
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BlockProductCellCount.cellPatternCount_flat_eq
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BlockProductCellCount.block_product_low_correlation
