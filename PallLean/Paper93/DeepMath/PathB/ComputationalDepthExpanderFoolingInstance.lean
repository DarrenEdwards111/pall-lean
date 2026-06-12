import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBurstBoundaryDebt
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBoundedBoundaryDebt

/-!
# Item 4: an explicit `2^n` fooling family + named time lower bounds

The debt-arc tradeoff theorems (`bounded_boundary_tradeoff`, `average_boundary_tradeoff`,
`burst_boundary_time_lower_bound`) take an abstract fooling set `P`.  This file supplies a **concrete,
explicit** one and states the resulting lower bounds as **named corollaries**.

## The explicit family

`hypercubeFool n` is the **complete** must-separate relation on the Boolean hypercube `Fin n → Bool`: every
pair of distinct `n`-bit points must be separated.  Its fooling set is all of `Fin n → Bool`, so

```
|P| = 2^n      (hypercube_card)
```

This is the **maximal** fooling set — every pair pairwise distinguishable — realised concretely (an observer
that must distinguish all `2^n` inputs, e.g. an EQUALITY/storage-type task sensitive to the whole input).  It
is the explicit witness of "`|P| = 2^{Ω(n)}` pairwise-must-separate continuations": the role of the
expander/`Kₙ`-Tseitin forcing in the programme is to *guarantee* such a family of distinguishable witness
branches for SAT; here we instantiate with the strongest count, `2^n`, directly.

## Named corollaries (clean axioms, no `sorry`)

* `hypercube_card` — `|P| = 2^n`.
* `hypercube_lowBoundary_requires_superpoly_time` — a **low-boundary** observer (boundary `≤ B` throughout)
  correctly distinguishing all `2^n` hypercube points needs `2^{n−B} ≤ T + 1`, i.e. **`T ≥ 2^{n−B} − 1`**.
  For `B = O(log n)` (poly width) this is `T ≥ 2^{n}/poly = 2^{Ω(n)}` — **super-polynomial time**.
* `hypercube_bounded_growth_requires_linear_time` — a **bounded-growth** observer (boundary grows `≤ r` per
  step) needs `2^n ≤ (T + 1)·2^{B_0 + r·T}`, forcing `r·T ≥ n − B_0 − ⌈log₂(T+1)⌉`, i.e. **`T = Ω(n/r)`** —
  linear time for `r = O(1)`.

## Honest scope

These are genuine, fully concrete **restricted** lower bounds for observers of the explicit `2^n` family:
super-poly for poly-width (bounded boundary), linear for bounded growth-rate.  They are **not** `P ≠ NP`:
the hypercube family forces every observer that must separate *all* `2^n` points, but a SAT decider need not —
it must separate only the `2^{Ω(n)}` witness branches *under some decomposition it is free to choose*, and the
min-over-decompositions (plus the unbounded-growth escape from item 3) remains the open quantifier.  What is
concrete here: the abstract bounds are now instantiated with an explicit family and yield named super-poly /
linear time lower bounds on their respective restricted classes.
-/

namespace PallLean.Paper93.DeepMath.PathB.BoundaryDebt

open scoped BigOperators

/-- The **complete** must-separate relation on the Boolean hypercube `Fin n → Bool`: every pair of distinct
points must be separated.  The associated fooling set is all of `Fin n → Bool`. -/
def hypercubeFool (n : ℕ) : Finset ((Fin n → Bool) × (Fin n → Bool)) :=
  Finset.univ.filter (fun p => p.1 ≠ p.2)

/-- Every distinct pair of hypercube points is in the complete must-separate relation: the universe is a
fooling set for `hypercubeFool n`. -/
theorem hypercube_fool (n : ℕ) :
    ∀ x ∈ (Finset.univ : Finset (Fin n → Bool)), ∀ y ∈ (Finset.univ : Finset (Fin n → Bool)),
      x ≠ y → (x, y) ∈ hypercubeFool n := by
  intro x _ y _ hxy
  rw [hypercubeFool, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, hxy⟩

/-- The explicit fooling set has `2^n` elements. -/
theorem hypercube_card (n : ℕ) : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- **Named corollary (super-poly time for low-boundary observers).**  A boundary-`B`-throughout observer
(servicing rate `≤ 2^B`, debt cleared by `T`) that correctly distinguishes all `2^n` hypercube points
satisfies `2^{n−B} ≤ T + 1`.  For `B = O(log n)` (`2^B = poly`) this is `T ≥ 2^{Ω(n)}` — **super-polynomial**.
-/
theorem hypercube_lowBoundary_requires_superpoly_time (n B : ℕ) (hBn : B ≤ n)
    (view0 : (Fin n → Bool) → Fin (2 ^ B))
    (debt : ℕ → ℕ) (T : ℕ)
    (hinit : debt 0 = debtCount (hypercubeFool n) view0)
    (hservice : ∀ t, debt t ≤ debt (t + 1) + 2 ^ B)
    (hcleared : debt T = 0) :
    2 ^ (n - B) ≤ T + 1 := by
  have htrade := bounded_boundary_tradeoff (Finset.univ : Finset (Fin n → Bool)) (hypercubeFool n)
    (hypercube_fool n) view0 debt T hinit hservice hcleared
  rw [hypercube_card] at htrade
  -- `2^n = 2^(n-B) * 2^B`, then cancel the positive factor `2^B`
  have hsplit : (2 : ℕ) ^ n = 2 ^ (n - B) * 2 ^ B := by
    rw [← pow_add]; congr 1; omega
  rw [hsplit] at htrade
  exact Nat.le_of_mul_le_mul_right htrade (by positivity)

/-- **Named corollary (linear time for bounded-growth observers).**  An observer whose boundary grows `≤ r`
per step, with initial boundary `B_0`, correctly distinguishing all `2^n` hypercube points satisfies
`2^n ≤ (T + 1)·2^{B_0 + r·T}` — forcing `r·T ≥ n − B_0 − ⌈log₂(T+1)⌉`, i.e. `T = Ω(n/r)`. -/
theorem hypercube_bounded_growth_requires_linear_time (n : ℕ)
    (B : ℕ → ℕ) (r : ℕ) (view0 : (Fin n → Bool) → Fin (2 ^ B 0))
    (debt : ℕ → ℕ) (T : ℕ)
    (hinit : debt 0 = debtCount (hypercubeFool n) view0)
    (hservice : ∀ t, debt t ≤ debt (t + 1) + 2 ^ B t)
    (hgrow : ∀ t, B (t + 1) ≤ B t + r)
    (hcleared : debt T = 0) :
    2 ^ n ≤ (T + 1) * 2 ^ (B 0 + r * T) := by
  have h := burst_boundary_time_lower_bound (Finset.univ : Finset (Fin n → Bool)) (hypercubeFool n)
    (hypercube_fool n) B r view0 debt T hinit hservice hgrow hcleared
  rwa [hypercube_card] at h

end PallLean.Paper93.DeepMath.PathB.BoundaryDebt

#print axioms PallLean.Paper93.DeepMath.PathB.BoundaryDebt.hypercube_card
#print axioms PallLean.Paper93.DeepMath.PathB.BoundaryDebt.hypercube_lowBoundary_requires_superpoly_time
#print axioms PallLean.Paper93.DeepMath.PathB.BoundaryDebt.hypercube_bounded_growth_requires_linear_time
