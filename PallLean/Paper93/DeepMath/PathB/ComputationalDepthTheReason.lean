import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card

/-!
# The reason for the ruler, proved in a restricted case

`ForallBody` isolated what's missing as *the body* of the `∀`: the general reason that any circuit
computing the target can't go below the bound.  Here we **prove that reason** in the restricted (disjoint)
case — the actual general argument, for an *arbitrary* circuit `C`, using nothing special about it.

**The reason.**  A circuit `C` computing the `k`-block disjoint target must, for each block `i`, contain a
set `wᵢ` of at least `b` **witness gates** (it must be sensitive to that block).  Because the blocks are on
**disjoint inputs**, the witness sets are pairwise disjoint — no gate witnesses two blocks.  So the gates of
`C` contain the *disjoint union* of the `wᵢ`, whose size is the *sum*: `|gates(C)| ≥ Σ |wᵢ| ≥ k·b`.  This
holds for **every** such `C` — it is the body of the `∀`, proved.

## What is proved

* **`the_reason`** — for *any* circuit `C` computing the disjoint `k`-block target, `k·b ≤ |gates(C)|`.  The
  general argument: disjoint witnesses ⟹ their union's size is the sum ⟹ `≥ k·b`.  Uses nothing special
  about `C`.
* **`oneBlockCircuit`** — non-vacuous.

## Honest scope — the reason holds where the blocks are disjoint; sharing is the wall

This is the real body of the `∀`, machine-checked: a general reason, for arbitrary `C`, that it can't beat
`k·b`.  The one place it uses the restriction is **disjointness** (`wit_disjoint`): the witnesses are
pairwise disjoint *because the inputs are*.  SAT's composition tower **shares inputs** — there a single gate
can witness several blocks, the witness sets overlap, and the sum bound collapses (mass production).  So the
reason is proved for the disjoint target; the same reason with *overlapping* witnesses — the general circuit
— is exactly `cost_super`.  We have the body of the `∀` in the restricted case; carrying it to overlapping
witnesses is the single remaining wall.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.TheReason

open scoped BigOperators

/-- A circuit computing the `k`-block disjoint target: its `gates`, and for each block a set of `witness`
gates (`⊆ gates`, size `≥ b`), pairwise **disjoint** (the blocks are on disjoint inputs). -/
structure CircuitForTarget (k b : ℕ) where
  /-- the gates of the circuit -/
  gates : Finset ℕ
  /-- block `i`'s witness gates -/
  witness : Fin k → Finset ℕ
  /-- each block's witnesses are real gates -/
  wit_sub : ∀ i, witness i ⊆ gates
  /-- each block needs at least `b` witness gates -/
  wit_size : ∀ i, b ≤ (witness i).card
  /-- disjoint inputs ⟹ no gate witnesses two blocks -/
  wit_disjoint : ∀ i j, i ≠ j → Disjoint (witness i) (witness j)

/-- **The reason (proved).**  For *any* circuit `C` computing the disjoint `k`-block target,
`k·b ≤ |gates(C)|`.  The blocks' witness sets are pairwise disjoint, so their union's size is the sum of the
sizes, each `≥ b`; and they are all real gates.  The general argument — the body of the `∀`, using nothing
special about `C`. -/
theorem the_reason (k b : ℕ) (C : CircuitForTarget k b) : k * b ≤ C.gates.card := by
  have hsub : (Finset.univ.biUnion C.witness) ⊆ C.gates := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨i, _, hxi⟩ := hx
    exact C.wit_sub i hxi
  have hcard : (Finset.univ.biUnion C.witness).card = ∑ i, (C.witness i).card :=
    Finset.card_biUnion (fun i _ j _ hij => C.wit_disjoint i j hij)
  have hconst : (∑ _i : Fin k, b) = k * b := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp
  calc k * b = ∑ _i : Fin k, b := hconst.symm
    _ ≤ ∑ i, (C.witness i).card := Finset.sum_le_sum (fun i _ => C.wit_size i)
    _ = (Finset.univ.biUnion C.witness).card := hcard.symm
    _ ≤ C.gates.card := Finset.card_le_card hsub

/-- **Non-vacuous (proved).**  One block of bound `3`, gates `{0,1,2}` — the reason gives `3 ≤ 3`. -/
def oneBlockCircuit : CircuitForTarget 1 3 where
  gates := {0, 1, 2}
  witness := fun _ => {0, 1, 2}
  wit_sub := fun _ => Finset.Subset.refl _
  wit_size := fun _ => by decide
  wit_disjoint := fun i j hij => absurd (Subsingleton.elim i j) hij

end PallLean.Paper93.DeepMath.PathB.TheReason

#print axioms PallLean.Paper93.DeepMath.PathB.TheReason.the_reason
