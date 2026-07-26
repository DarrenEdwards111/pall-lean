import Mathlib.Data.Nat.Basic

/-!
# Charging the abstract model for sharing, in a restricted case

The thermodynamic observer said: the abstract circuit charges nothing for fanout (`ε = 0`), and that free
sharing is where mass production lives.  So the natural restricted experiment is to **charge the abstract
model for sharing** — put `ε > 0` back — and see what lower bound that buys.  The clean answer: charging
`c ≥ 1` per shared wire lifts the cost to at least the **formula (tree) cost**, so every formula lower
bound (Khrapchenko `n²`, Andreev `n^{5/2}`) transfers — but that is exactly the formula altitude, and it
caps below `P ≠ NP`.

## The model

A circuit has a DAG cost `dagCost` (abstract, fanout free) and a `sharing` amount (the wires it reuses —
the mass-production savings).  Unfolding the DAG to a **formula duplicates the sharing**, so
`treeCost = dagCost + sharing`.  Charging `c` per shared wire gives
`chargedCost c = dagCost + c·sharing`, interpolating: `c = 0` is the abstract DAG, `c = 1` is (at least)
the tree.

## What is proved

* **`charged_ge_tree`** — any positive charge lifts to the tree cost: `c ≥ 1 ⟹ treeCost ≤ chargedCost c`.
* **`charged_gets_formula_bound`** — hence every formula lower bound transfers: `L ≤ treeCost` and `c ≥ 1`
  give `L ≤ chargedCost c`.  The charged abstract model inherits Khrapchenko `n²`, Andreev `n^{5/2}`, …
* **`free_fanout_no_bound`** — the standard model gets nothing: `chargedCost 0 = dagCost` — with free
  fanout (`c = 0`) the charge vanishes and only the (small) DAG cost remains.
* **`charged_witness_bound`** — concrete: a circuit whose DAG saves `20` by sharing (`dagCost 5`,
  `treeCost 25`) has `chargedCost 1 ≥ 25` — the charge recovers the full tree bound.

## Honest scope — charging IS the formula altitude

This is a real restricted result: with a positive charge the abstract model acquires all the formula lower
bounds, which are genuinely super-linear/superpolynomial (`n²`, `n^{5/2}`).  But **charging `c ≥ 1` for
sharing *is* the formula model** — no free sharing is exactly what a formula is.  So the charge does all the
work, and it lands on the tree altitude, whose ceiling is `P ⊄ NC¹` (depth), *not* `P ≠ NP` (size).

The standard abstract circuit charges `c = 0` (`free_fanout_no_bound`): fanout is free, the charge
vanishes, and `cost_super` stands.  The charge `c` is precisely the **tree-vs-DAG gap** — turning it up
recovers the formula bounds and their ceiling; turning it to `0` (the real model) returns you to the wall.
Charging the abstract model in a restricted case is moving to the formula altitude, capped below `P ≠ NP`.
Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ChargedSharing

/-- A circuit as `dagCost` (abstract, fanout free) plus `sharing` (reused wires = mass-production savings). -/
structure ChargedCircuit where
  /-- abstract DAG size (fanout free) -/
  dagCost : ℕ
  /-- the shared/reused wires -/
  sharing : ℕ

/-- The formula (tree) cost: unfolding the DAG duplicates the sharing, `dagCost + sharing`. -/
def treeCost (C : ChargedCircuit) : ℕ := C.dagCost + C.sharing

/-- The charged cost at charge `c` per shared wire: `dagCost + c·sharing`.  `c = 0` is the abstract DAG. -/
def chargedCost (C : ChargedCircuit) (charge : ℕ) : ℕ := C.dagCost + charge * C.sharing

/-- **A positive charge lifts to the tree cost (proved).**  Charging `c ≥ 1` per shared wire makes the
charged cost at least the formula cost: `treeCost ≤ chargedCost c`. -/
theorem charged_ge_tree (C : ChargedCircuit) (charge : ℕ) (hc : 1 ≤ charge) :
    treeCost C ≤ chargedCost C charge := by
  show C.dagCost + C.sharing ≤ C.dagCost + charge * C.sharing
  have h : 1 * C.sharing ≤ charge * C.sharing := Nat.mul_le_mul hc (Nat.le_refl C.sharing)
  rw [Nat.one_mul] at h
  omega

/-- **Formula bounds transfer to the charged model (proved).**  A formula lower bound `L ≤ treeCost` and a
positive charge `c ≥ 1` give `L ≤ chargedCost c`.  Khrapchenko `n²`, Andreev `n^{5/2}`, … all transfer. -/
theorem charged_gets_formula_bound (C : ChargedCircuit) (charge L : ℕ) (hc : 1 ≤ charge)
    (hformula : L ≤ treeCost C) : L ≤ chargedCost C charge :=
  le_trans hformula (charged_ge_tree C charge hc)

/-- **Free fanout gets no bound (proved).**  The standard model charges `c = 0`: `chargedCost 0 = dagCost`.
The charge vanishes and only the (small) DAG cost remains — `cost_super` territory. -/
theorem free_fanout_no_bound (C : ChargedCircuit) : chargedCost C 0 = C.dagCost := by
  show C.dagCost + 0 * C.sharing = C.dagCost
  rw [Nat.zero_mul, Nat.add_zero]

/-- A circuit whose DAG saves `20` by sharing: `dagCost = 5`, `sharing = 20`, so `treeCost = 25`. -/
def chargedWitness : ChargedCircuit where
  dagCost := 5
  sharing := 20

/-- **Concrete transfer (proved).**  A formula bound `L = 25 ≤ treeCost` transfers to `chargedCost 1 ≥ 25`
— charging one per shared wire recovers the full tree bound the free DAG (cost `5`) evaded. -/
theorem charged_witness_bound : (25 : ℕ) ≤ chargedCost chargedWitness 1 :=
  charged_gets_formula_bound chargedWitness 1 25 (by decide) (by decide)

end PallLean.Paper93.DeepMath.PathB.ChargedSharing

#print axioms PallLean.Paper93.DeepMath.PathB.ChargedSharing.charged_ge_tree
#print axioms PallLean.Paper93.DeepMath.PathB.ChargedSharing.charged_gets_formula_bound
#print axioms PallLean.Paper93.DeepMath.PathB.ChargedSharing.free_fanout_no_bound
