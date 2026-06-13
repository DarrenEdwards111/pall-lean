import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRavelableClass

/-!
# The separating boundary is *tight*: exactly `r` — so the wall is time, not space

The bounded‑space raveling gives the **lower** half: no boundary‑/space‑`< r` observer separates the
dimension‑`r` residual.  Here we add the matching **upper** half: the residual view *itself* (boundary `r`)
separates with **zero debt**.  Together they pin the separating boundary at **exactly `r`**.

The payoff is conceptual and honest: the hard family is *perfectly decidable* with boundary `r` (= space `r`) —
the full‑boundary, brute‑force, zero‑debt decider.  So the obstruction to a fast algorithm is **not space**
(space is tightly characterized and the family fits in space `r`); it is **time**.  The debt / space machinery
is exact on the space axis and provably cannot reach the time axis (`distinguishability_debt_not_time_lower_bound`)
— which is precisely where `P ≠ NP` lives.

## Proved (clean axioms, no `sorry`)

* `residual_separates` — **upper bound**: the boundary‑`r` residual view is a zero‑debt separator
  (`correct_view_zero_debt`): it distinguishes every must‑separate pair.
* `below_r_fails` — **lower bound**: no boundary‑`s` view with `s < r` separates (positive debt), reusing
  `boundedBoundary_no_separator`.
* `separating_boundary_tight` — **the tight characterization**: separating boundary `= r` exactly (a zero‑debt
  separator at `r`, none below `r`).
-/

namespace PallLean.Paper93.DeepMath.PathB.TightSeparatingSpace

open PallLean.Paper93.DeepMath.PathB.RavelableClass
open PallLean.Paper93.DeepMath.PathB.BoundaryDebt

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- **Upper bound (proved).**  The residual view itself — carrying boundary `r` (`Fin (2^r)`) — separates with
zero debt: every must‑separate pair has distinct residual outcomes, so none is merged. -/
theorem residual_separates {r : ℕ} (residual : C → Fin (2 ^ r)) :
    debtCount (residualFooling residual) residual = 0 := by
  apply correct_view_zero_debt
  intro p hp
  rw [residualFooling, Finset.mem_filter] at hp
  exact hp.2

/-- **Lower bound (proved).**  No boundary‑`s` view with `s < r` separates the dimension‑`r` residual — it
carries positive debt (`boundedBoundary_no_separator`). -/
theorem below_r_fails {s r : ℕ} (hsr : s < r) (residual : C → Fin (2 ^ r))
    (hsurj : Function.Surjective residual) (view : C → Fin (2 ^ s)) :
    debtCount (residualFooling residual) view ≠ 0 :=
  boundedBoundary_no_separator hsr residual hsurj view

/-- **The separating boundary is exactly `r` (proved).**  A zero‑debt separator exists at boundary `r` (the
residual itself), and none exists below `r`.  Space is tightly pinned; the family is space‑`r`‑decidable.  The
remaining obstruction is on the *time* axis — exactly `P ≠ NP`. -/
theorem separating_boundary_tight {r : ℕ} (residual : C → Fin (2 ^ r))
    (hsurj : Function.Surjective residual) :
    debtCount (residualFooling residual) residual = 0
    ∧ ∀ {s : ℕ}, s < r → ∀ view : C → Fin (2 ^ s), debtCount (residualFooling residual) view ≠ 0 :=
  ⟨residual_separates residual, fun {_} hsr view => below_r_fails hsr residual hsurj view⟩

end PallLean.Paper93.DeepMath.PathB.TightSeparatingSpace

#print axioms PallLean.Paper93.DeepMath.PathB.TightSeparatingSpace.residual_separates
#print axioms PallLean.Paper93.DeepMath.PathB.TightSeparatingSpace.separating_boundary_tight
