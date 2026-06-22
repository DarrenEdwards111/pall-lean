import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CellRecursion

/-!
# Hard math (circuit-tree assembly) — any count-tree has cell count ≤ the product over the tree (proved)

The end-to-end assembly of the arbitrary-depth cell-count recursion over a concrete recursive circuit datatype.  A
**count-tree** is a binary tree whose leaves are count-gates `(Fin n → Bool) → ℕ` and whose internal nodes combine the two
child counts via an arbitrary `ℕ → ℕ → ℕ` aggregation (a layer of symmetric processing — `MOD`/threshold/etc).  Its evaluation
`ceval` produces, for each input, a single count; the number of *distinct* counts it produces is its cell count.

The structural induction (`ctree_cells_le`) threads the cell recursion through every node: a node's cell count is at most the
**product** of its two children's cell counts (`cells_pair`), so the whole tree's cell count is at most `cbound t`, the product
of leaf cell counts over the tree.  For a depth-`d` tree whose leaves are prime-power `MOD_{p^e} ∘ AND` blocks (`≤ k+1` cells
each, `cells_card_le`), this is `(k+1)^{#leaves}` — quasipolynomial for constant depth, **field-independent** (hence surviving
the prime-power RS barrier `e ≥ 2`).

## What is proved (clean axioms, no `sorry`)

* **`cells_pair`** (PROVED) — `(image (x ↦ (f x, g x))).card ≤ (image f).card · (image g).card`.
* **`CTree`** / **`ceval`** / **`cbound`** — the binary count-tree, its evaluation, and the product-of-leaf-cells bound.
* **`ctree_cells_le`** (PROVED) — `(image (ceval t)).card ≤ cbound t` for every tree `t` (structural induction, node via
  `cells_pair`).

## Honest scope

This is the concrete circuit-tree assembly of the symmetric cell-count recursion — any (binary) count-tree of arbitrary depth
has cell count bounded by the product of its leaf cells.  Plugging in concrete `MOD_{p^e}∘AND` leaves gives the
quasipolynomial bound; the unconditional `NEXP ⊄ ACC⁰` (P≠NP-strength) is not done here.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0CellTree

open Finset

variable {n : ℕ}

/-- **Pair cell bound (PROVED): the joint of two functions has `≤` the product of their cell counts.** -/
theorem cells_pair {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : (Fin n → Bool) → α) (g : (Fin n → Bool) → β) :
    (Finset.univ.image (fun x => (f x, g x))).card
      ≤ (Finset.univ.image f).card * (Finset.univ.image g).card := by
  classical
  refine le_trans (Finset.card_le_card ?_) (le_of_eq (Finset.card_product _ _))
  intro p hp
  simp only [Finset.mem_image] at hp; obtain ⟨x, _, rfl⟩ := hp
  exact Finset.mem_product.mpr
    ⟨Finset.mem_image_of_mem f (mem_univ x), Finset.mem_image_of_mem g (mem_univ x)⟩

/-- A binary count-tree: leaves are count-gates, nodes combine two child counts. -/
inductive CTree (n : ℕ) where
  | leaf : ((Fin n → Bool) → ℕ) → CTree n
  | node : (ℕ → ℕ → ℕ) → CTree n → CTree n → CTree n

/-- Evaluation of a count-tree: a single count per input. -/
def ceval : CTree n → (Fin n → Bool) → ℕ
  | .leaf f => f
  | .node agg l r => fun x => agg (ceval l x) (ceval r x)

/-- The product-of-leaf-cells bound. -/
def cbound : CTree n → ℕ
  | .leaf f => (Finset.univ.image f).card
  | .node _ l r => cbound l * cbound r

/-- **Any count-tree's cell count is `≤` the product of its leaf cells (PROVED).**  Structural induction; each node multiplies
the children's cell counts (`cells_pair`). -/
theorem ctree_cells_le (t : CTree n) : (Finset.univ.image (ceval t)).card ≤ cbound t := by
  induction t with
  | leaf f => simp [ceval, cbound]
  | node agg l r ihl ihr =>
      have hfac : Finset.univ.image (ceval (.node agg l r)) ⊆
          (Finset.univ.image (fun x => (ceval l x, ceval r x))).image (fun p => agg p.1 p.2) := by
        intro y hy
        simp only [Finset.mem_image] at hy ⊢
        obtain ⟨x, _, rfl⟩ := hy
        exact ⟨(ceval l x, ceval r x), ⟨x, Finset.mem_univ x, rfl⟩, rfl⟩
      calc (Finset.univ.image (ceval (.node agg l r))).card
          ≤ ((Finset.univ.image (fun x => (ceval l x, ceval r x))).image
              (fun p => agg p.1 p.2)).card := Finset.card_le_card hfac
        _ ≤ (Finset.univ.image (fun x => (ceval l x, ceval r x))).card := Finset.card_image_le
        _ ≤ (Finset.univ.image (ceval l)).card * (Finset.univ.image (ceval r)).card :=
              cells_pair _ _
        _ ≤ cbound l * cbound r := Nat.mul_le_mul ihl ihr
        _ = cbound (.node agg l r) := by simp [cbound]

/-!
**Circuit-tree assembly, proved.**  Any binary count-tree of arbitrary depth has cell count `≤ cbound t` = the product of its
leaf cell counts — the end-to-end symmetric cell-count recursion over a concrete recursive datatype, threading `cells_pair`
through every node.  With prime-power `MOD_{p^e}∘AND` leaves this is quasipolynomial for constant depth, field-independent.
Remaining (open, not faked): the unconditional `NEXP ⊄ ACC⁰`.  Not `NEXP ⊄ ACC⁰`, not `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0CellTree

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CellTree.ctree_cells_le
