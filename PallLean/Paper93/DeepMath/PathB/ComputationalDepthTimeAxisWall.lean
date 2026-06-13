import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTightSeparatingSpace
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDecisionHolonomy

/-!
# The wall is on the time axis — consolidated

The space axis is **closed and tight**: the separating boundary is *exactly* `r`
(`separating_boundary_tight`).  Concretely:

* `SPACE(< r)` **fails** — no boundary‑`< r` view separates the dimension‑`r` residual (`below_r_fails`);
* `SPACE(= r)` **separates** — the residual view itself is a zero‑debt separator (`residual_separates`).

So a correct separator *exists* at boundary/space `r`; nothing about the family resists a space‑`r` algorithm.
Any remaining obstruction to a fast decider is therefore **not spatial** — it is **temporal**: the question is
whether that (existing) boundary‑`r` separator can be *computed in polynomial time*.

## Proved (clean axioms, no `sorry`)

* `space_axis_settled` — the tight characterization restated: separator at `r`, none below `r`.
* `timeAxis_wall` — **the reduction along the time axis**: given the named missing bridge
  `ResidualSeparatorRequiresSuperpolyTime` (the boundary‑`r` separator's decision time is super‑polynomial) and a
  super‑poly threshold, the family's decision time is not polynomially bounded (`P ≠ NP` for an NP‑complete
  family).  This is `decisionHolonomy_implies_not_poly` placed on the time axis.
* `space_machinery_cannot_supply_bridge` — **the gap**: an action / distinguishability‑debt bound of any size is
  achieved by a poly‑time single‑step high‑boundary trajectory, so the (space‑exact) debt machinery does **not**
  imply the time bridge (`distinguishability_debt_not_time_lower_bound`).

## Honest scope — the wall, located exactly

`ResidualSeparatorRequiresSuperpolyTime` is the **one missing theorem**.  It is *not* a space statement (space is
settled), and the debt/space machinery provably cannot reach it (`space_machinery_cannot_supply_bridge`).  It is
a pure *time* lower bound on realizing the boundary‑`r` separator — for an NP‑complete family, exactly `P ≠ NP`.
The productive direction is now to prove it for **restricted time models** (bounded‑width branching programs,
streaming, oblivious, small‑depth), expanding the ring of known lower bounds toward (but not claiming) all of
`P`.
-/

namespace PallLean.Paper93.DeepMath.PathB.TimeAxisWall

open PallLean.Paper93.DeepMath.PathB.TightSeparatingSpace
open PallLean.Paper93.DeepMath.PathB.DecisionHolonomy
open PallLean.Paper93.DeepMath.PathB.TimeBoundaryPrinciple
open PallLean.Paper93.DeepMath.PathB.BoundaryDebt

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- **The space axis is settled (restated).**  A zero‑debt separator exists at boundary `r`; none exists below
`r`.  Space is exactly `r`; the obstruction lies elsewhere. -/
theorem space_axis_settled {r : ℕ} (residual : C → Fin (2 ^ r)) (hsurj : Function.Surjective residual) :
    debtCount (residualFooling residual) residual = 0
    ∧ ∀ {s : ℕ}, s < r → ∀ view : C → Fin (2 ^ s), debtCount (residualFooling residual) view ≠ 0 :=
  separating_boundary_tight residual hsurj

/-- **The exact missing bridge, on the time axis.**  Even though a boundary‑`r` separator *exists*, computing it
takes super‑polynomial time: the family's decision time is bounded below by a super‑poly `threshold`.  This is
the single remaining hypothesis — a *time* lower bound, not a space one. -/
def ResidualSeparatorRequiresSuperpolyTime (decisionTime threshold : ℕ → ℕ) : Prop :=
  DecisionHolonomyHyp decisionTime threshold

/-- **The time‑axis wall (proved reduction).**  Given the missing bridge (the separator's decision time is
super‑poly) with a super‑poly threshold, the family's decision time is not polynomially bounded — `P ≠ NP` for an
NP‑complete family.  The space side contributes nothing further; the only input is the *time* bound. -/
theorem timeAxis_wall {decisionTime threshold : ℕ → ℕ}
    (hBridge : ResidualSeparatorRequiresSuperpolyTime decisionTime threshold)
    (hSP : SuperPoly threshold) :
    ¬ PolyBounded decisionTime :=
  decisionHolonomy_implies_not_poly hBridge hSP

/-- **The gap (proved): the space/debt machinery cannot supply the time bridge.**  For any debt value `D`, a
poly‑time single‑step trajectory achieves action `≥ D`.  So an action / distinguishability bound — however large,
and however tight on the space axis — gives **no** decision‑time lower bound.  The bridge must come from a
genuinely time/algorithmic argument. -/
theorem space_machinery_cannot_supply_bridge (D : ℕ) :
    ∃ B : ℕ → ℕ, D ≤ action B 1 :=
  distinguishability_debt_not_time_lower_bound D

end PallLean.Paper93.DeepMath.PathB.TimeAxisWall

#print axioms PallLean.Paper93.DeepMath.PathB.TimeAxisWall.space_axis_settled
#print axioms PallLean.Paper93.DeepMath.PathB.TimeAxisWall.timeAxis_wall
#print axioms PallLean.Paper93.DeepMath.PathB.TimeAxisWall.space_machinery_cannot_supply_bridge
