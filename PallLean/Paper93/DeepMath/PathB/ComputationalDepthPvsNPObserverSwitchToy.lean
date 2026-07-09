import Mathlib

/-!
# P-vs-NP observer-switch toy core

This file formalizes the first honest, minimal theorem suggested by the ACC scale-bridge lesson.

It is **not** `P ≠ NP`.  It is the finite pigeonhole core any Williams-style NP-search observer switch must
satisfy:

* if an observer/boundary preserves all residual assignment distinctions on `n` Boolean variables, then its boundary has
  at least `2^n` states;
* hence no observer with fewer than `2^n` boundary states can be fully residual-distinguishing;
* in particular, any proposed polynomial-size boundary must fail once `2^n` exceeds that polynomial.

This is the toy H4 obligation in theorem form.  The hard future step is to connect a real SAT/self-reduction residual
observer to this injectivity hypothesis while showing P-time algorithms force polynomial boundary size.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsNPObserverSwitchToy

/-- Boolean assignments on `n` variables. -/
abbrev Assignment (n : ℕ) := Fin n → Bool

/-- A boundary observer sends each assignment/residual branch to a boundary state. -/
abbrev BoundaryObserver (n : ℕ) (α : Type) := Assignment n → α

/-- The assignment space has size `2^n`. -/
theorem card_assignment (n : ℕ) : Fintype.card (Assignment n) = 2 ^ n := by
  simp [Assignment]

/-- If the observer preserves all assignment/residual distinctions, its boundary has at least `2^n` states. -/
theorem boundary_card_ge_exp {n : ℕ} {α : Type} [Fintype α]
    (obs : BoundaryObserver n α) (hobs : Function.Injective obs) : 2 ^ n ≤ Fintype.card α := by
  simpa [card_assignment] using Fintype.card_le_of_injective obs hobs

/-- No boundary with fewer than `2^n` states can preserve all assignment/residual distinctions. -/
theorem small_boundary_not_residual_distinguishing {n : ℕ} {α : Type} [Fintype α]
    (obs : BoundaryObserver n α) (hsmall : Fintype.card α < 2 ^ n) : ¬ Function.Injective obs := by
  intro hobs
  exact (not_le_of_gt hsmall) (boundary_card_ge_exp obs hobs)

/-- Polynomial-boundary contradiction schema: if `|α| ≤ n^k` and `n^k < 2^n`, the observer cannot be fully
residual-distinguishing. -/
theorem poly_boundary_not_residual_distinguishing {n k : ℕ} {α : Type} [Fintype α]
    (obs : BoundaryObserver n α) (hpoly : Fintype.card α ≤ n ^ k) (hgap : n ^ k < 2 ^ n) :
    ¬ Function.Injective obs := by
  exact small_boundary_not_residual_distinguishing obs (lt_of_le_of_lt hpoly hgap)

/-- Contradiction form of the toy H4 obligation. -/
theorem residual_distinguishing_contradicts_poly_boundary {n k : ℕ} {α : Type} [Fintype α]
    (obs : BoundaryObserver n α) (hobs : Function.Injective obs)
    (hpoly : Fintype.card α ≤ n ^ k) (hgap : n ^ k < 2 ^ n) : False := by
  exact (poly_boundary_not_residual_distinguishing obs hpoly hgap) hobs

/-!
Interpretation:

```text
P-side compression hypothesis:      |boundary| ≤ n^k
NP-side preservation hypothesis:    residual observer is injective on 2^n branches
scale gap:                          n^k < 2^n
--------------------------------------------------
contradiction
```

This is the finite combinatorial core.  It deliberately does not claim the missing hard parts:

1. a real SAT/search observer whose residual states are forced to be injective;
2. a theorem that every P-time SAT solver induces only polynomially many boundary states;
3. a non-natural/non-large design avoiding the standard barriers.
-/

end PallLean.Paper93.DeepMath.PathB.PvsNPObserverSwitchToy

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPObserverSwitchToy.boundary_card_ge_exp
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPObserverSwitchToy.small_boundary_not_residual_distinguishing
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPObserverSwitchToy.poly_boundary_not_residual_distinguishing
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPObserverSwitchToy.residual_distinguishing_contradicts_poly_boundary
