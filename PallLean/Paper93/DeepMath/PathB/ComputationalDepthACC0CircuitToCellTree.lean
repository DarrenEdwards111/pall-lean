import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CellTree
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CircuitModel

/-!
# Bridge — faithful translation of the concrete `ACC0Circuit` into the abstract count-tree (proved)

Connects the abstract symmetric cell-count machinery (`CTree`, `ceval`, `ctree_cells_le`) to the **concrete** circuit model
`ACC0Circuit` (binary `AND`/`OR`/`NOT`, `MOD` gates).  We translate any `ACC0Circuit` into a count-tree whose evaluation is the
`{0,1}`-indicator of the circuit's Boolean output (`ceval_toCTree`), so the count-tree faithfully represents the circuit.  SAT
of the circuit then corresponds exactly to the tree producing `1` (`satisfiable_iff_toCTree`).

This makes the cell-count tree machinery *applicable to real circuits*: every `ACC0Circuit` is a count-tree, so `ctree_cells_le`
bounds its cell count by the product of its leaf cells.

## What is proved (clean axioms, no `sorry`)

* **`toCTree`** — the structural translation `ACC0Circuit n → CTree n` (`const`/`var`/`mod` → `{0,1}` leaves; `not`/`and`/`or`
  → `ℕ→ℕ→ℕ` nodes `1−a`, `a·b`, `max a b`).
* **`ceval_toCTree`** (PROVED) — `ceval (toCTree C) x = if eval C x then 1 else 0` (eval-preservation, structural induction).
* **`satisfiable_iff_toCTree`** (PROVED) — `(∃ x, eval C x = true) ↔ ∃ x, ceval (toCTree C) x = 1`.

## Honest scope

This is the *faithful* bridge from `ACC0Circuit` to the count-tree.  With these naive Boolean leaves the cell-count bound
(`ctree_cells_le`) is loose — a Boolean output has `≤ 2` cells while the tree's product bound is `2^{#leaves}`; the
*quasipolynomial* benefit of the symmetric method requires coarser leaves that capture whole `MOD ∘ AND` blocks (the
`modpe_tree_cells_le` regime), not single variables.  The unconditional `NEXP ⊄ ACC⁰` (P≠NP-strength) is not done here.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0CircuitToCellTree

open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel (ACC0Circuit)
open PallLean.Paper93.DeepMath.PathB.ACC0CellTree (CTree ceval)

variable {n : ℕ}

/-- Structural translation of an `ACC0Circuit` into a count-tree (`{0,1}`-valued). -/
def toCTree : ACC0Circuit n → CTree n
  | .const b => .leaf (fun _ => if b then 1 else 0)
  | .var i => .leaf (fun x => if x i then 1 else 0)
  | .not c => .node (fun a _ => 1 - a) (toCTree c) (toCTree c)
  | .and a b => .node (fun u v => u * v) (toCTree a) (toCTree b)
  | .or a b => .node (fun u v => max u v) (toCTree a) (toCTree b)
  | .mod q S t => .leaf (fun x => if ACC0CircuitModel.eval (.mod q S t) x then 1 else 0)

private theorem not_lemma (b : Bool) : 1 - (if b then 1 else 0) = if !b then (1 : ℕ) else 0 := by
  cases b <;> rfl

private theorem and_lemma (a b : Bool) :
    (if a then 1 else 0) * (if b then 1 else 0) = if (a && b) then (1 : ℕ) else 0 := by
  cases a <;> cases b <;> rfl

private theorem or_lemma (a b : Bool) :
    max (if a then 1 else 0) (if b then 1 else 0) = if (a || b) then (1 : ℕ) else 0 := by
  cases a <;> cases b <;> rfl

/-- **The translation is eval-preserving (PROVED): the count-tree evaluates to the `{0,1}`-indicator of the circuit. -/
theorem ceval_toCTree (C : ACC0Circuit n) (x : Fin n → Bool) :
    ceval (toCTree C) x = if ACC0CircuitModel.eval C x then 1 else 0 := by
  induction C with
  | const b => rfl
  | var i => rfl
  | not c ih =>
      simp only [toCTree, ceval, ACC0CircuitModel.eval, ih]
      exact not_lemma _
  | and a b iha ihb =>
      simp only [toCTree, ceval, ACC0CircuitModel.eval, iha, ihb]
      exact and_lemma _ _
  | or a b iha ihb =>
      simp only [toCTree, ceval, ACC0CircuitModel.eval, iha, ihb]
      exact or_lemma _ _
  | mod q S t => rfl

/-- **SAT of the circuit corresponds to the count-tree producing `1` (PROVED).** -/
theorem satisfiable_iff_toCTree (C : ACC0Circuit n) :
    (∃ x, ACC0CircuitModel.eval C x = true) ↔ (∃ x, ceval (toCTree C) x = 1) := by
  constructor
  · rintro ⟨x, hx⟩; exact ⟨x, by rw [ceval_toCTree, hx]; rfl⟩
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [ceval_toCTree] at hx
    by_contra h
    simp only [Bool.not_eq_true] at h
    rw [h] at hx
    simp at hx

/-!
**Faithful bridge, proved.**  Every `ACC0Circuit` translates to a count-tree whose evaluation is the `{0,1}`-indicator of the
circuit (`ceval_toCTree`), and circuit-SAT corresponds to the tree producing `1`.  The abstract cell-count machinery now
applies to the concrete model; the quasipolynomial regime requires `MOD∘AND`-block leaves (`modpe_tree_cells_le`), not the
naive Boolean leaves here.  Remaining (open, not faked): the unconditional `NEXP ⊄ ACC⁰`.  Not `NEXP ⊄ ACC⁰`, not `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0CircuitToCellTree

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CircuitToCellTree.ceval_toCTree
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CircuitToCellTree.satisfiable_iff_toCTree
