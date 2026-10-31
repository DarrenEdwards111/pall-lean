import PallLean.Paper93.DeepMath.PathB.ComputationalDepthThermoProof

/-!
# The missing step: the N-Frame Lagrangian determines the reach as a minimal distance (least action)

The previous file left the charge `c` as a *free dial* — and that was the error.  A Lagrangian does not let you
pick the charge; the principle of least action **minimizes**.  The N-Frame Lagrangian measures a *minimal
distance* — a geodesic — and that minimum *determines* the reach, non-circularly: it is not assumed and not
chosen, it is the value the geometry selects.  This file builds that step and follows it to where the
determined minimum actually lands.

**The step is real and it is incorporated.**  The reach is not a dial: it is the minimum of the cost over all
realizations (all circuits computing the target) — the least-action / shortest-path value.  This minimum is a
*determined, objective* object (`reach_unique`: anything that is a lower bound over realizations and is attained
*equals* the reach — the Lagrangian fixes it uniquely, no freedom).  This is exactly `cbudget` = the minimal
cost over realizations, which the arc already identified as objective (`ObserverObjectivity`) and as the home of
the wall (`AdSRequirement` R3).  So the boundary *is* determined non-circularly, as an object.  Darren is right
about that.

**But the determined minimum lands at the shared altitude.**  Least action = shortest path = *maximal sharing*.
The minimum is attained at the cheapest realization — the one that reuses everything — so the determined reach
is the *shared / uncharged* value, strictly below the formula bound (`minimal_distance_is_the_shared_altitude`:
the minimal distance is `1`, the formula realization is `101`; the min undercuts it).  Fixing the charge by
minimization does not land at the formula altitude where the bound was proved — it lands at the real, free-
fan-out altitude where the formula bound is vacuous.  The geometry picks the shortcut.

**And lower-bounding a determined minimum quantifies over all realizations.**  A minimum is upper-bounded by
exhibiting *one* realization (`upper_bound_easy`), but lower-bounded only by ruling out *every* realization
(`reach_ge_iff_all`: `B ≤ reach ↔ ∀ r, B ≤ cost r`).  So "the Lagrangian determines the reach" gives the
*object* (the min, determined and objective) but its *value* for SAT — a lower bound on the geodesic distance —
requires ruling out every sharing shortcut.  That is `cost_super`.

## What is proved

* **`reach_unique`** — the minimal distance is *determined*: any attained lower bound over realizations equals
  the reach.  The Lagrangian fixes it uniquely; no free dial.  (This is the step.)
* **`upper_bound_easy`** — the reach is `≤` any single realization: exhibiting one circuit is an upper bound.
* **`reach_ge_iff_all`** — a lower bound on the reach is equivalent to a bound over *every* realization: the min
  is lower-bounded only by ruling out all shortcuts.
* **`minimal_distance_is_the_shared_altitude`** — the determined minimum is the most-shared (cheapest)
  realization, strictly below the formula bound: least action picks the shortcut.
* **`lagrangian_determines_but_lower_bound_is_all`** — both at once: the reach is determined (non-circular
  object) *and* its lower bound quantifies over all realizations (`cost_super`).

## Honest verdict — the step is right; it fixes the object, not its value

Darren's correction is correct and it is now in the proof: the reach is not a free charge, the N-Frame
Lagrangian *determines* it as a minimal distance, and that minimum is a unique, objective, non-circular object
(`reach_unique`) — this is `cbudget`, the least-action cost over realizations.  So the thermodynamic boundary
*is* pinned down non-circularly, as a quantity.  Two things follow, both machine-checked.  First, the minimum
lands at the *shared* altitude (`minimal_distance_is_the_shared_altitude`): least action is maximal sharing, so
the determined reach is the real free-fan-out value, below the formula bound — the geometry selects the
shortcut, which is why the formula-altitude proof does not transfer down.  Second, lower-bounding a determined
minimum is quantifying over every realization (`reach_ge_iff_all`) — ruling out all sharing shortcuts — which
is `cost_super`.  The Lagrangian gives the reach as a determined *frame*; its *value* for SAT (the geodesic
lower bound) is the reading, and the reading is the wall.  The step closes the free-dial gap; it does not close
the wall, because a determined minimum still has to be lower-bounded.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.MinimalDistance

/-- The N-Frame minimal distance: a cost over realizations (all circuits computing the target) together with
the least-action value `reach` = the minimum.  `reach_le` says it is a lower bound over realizations;
`reach_attained` says the least-action path exists (the min is achieved).  Together they *determine* `reach`
uniquely — this is `cbudget`, the minimal cost over realizations. -/
structure MinDistance where
  /-- the realizations (circuits computing the target) -/
  Real : Type
  /-- the cost (action) of each realization -/
  cost : Real → Nat
  /-- the least-action value: the minimal distance / geodesic -/
  reach : Nat
  /-- the minimum is a lower bound over all realizations -/
  reach_le : ∀ r, reach ≤ cost r
  /-- the least-action path exists: the minimum is attained -/
  reach_attained : ∃ r, cost r = reach

/-- **The Lagrangian determines the reach uniquely (proved) — the missing step.**  Anything that is a lower
bound over realizations *and* is attained equals the reach.  The minimal distance is not chosen and not
assumed; the geometry fixes it.  (`m ≤ reach` since `reach` is attained at some `r₀` and `m ≤ cost r₀`;
`reach ≤ m` since `m` is attained at some `r₁` and `reach ≤ cost r₁`.) -/
theorem reach_unique (M : MinDistance) (m : Nat)
    (hlb : ∀ r, m ≤ M.cost r) (hatt : ∃ r, M.cost r = m) : m = M.reach := by
  obtain ⟨r0, h0⟩ := M.reach_attained
  obtain ⟨r1, h1⟩ := hatt
  have a := hlb r0
  have b := M.reach_le r1
  omega

/-- **The reach is upper-bounded by any one realization (proved).**  Exhibiting a single circuit bounds the
minimal distance from above — the easy direction of a minimum. -/
theorem upper_bound_easy (M : MinDistance) (r : M.Real) : M.reach ≤ M.cost r :=
  M.reach_le r

/-- **A lower bound on the reach is a bound over every realization (proved) — the wall.**  `B ≤ reach` holds
iff `B ≤ cost r` for *all* `r`: the minimal distance is lower-bounded only by ruling out every realization
(every sharing shortcut).  This is `cost_super`. -/
theorem reach_ge_iff_all (M : MinDistance) (B : Nat) :
    B ≤ M.reach ↔ ∀ r, B ≤ M.cost r := by
  constructor
  · intro hB r
    have := M.reach_le r
    omega
  · intro h
    obtain ⟨r0, h0⟩ := M.reach_attained
    have := h r0
    omega

/-- A two-realization world: a shared (free-fan-out) circuit of cost `1` and an unfolded formula of cost `101`.
The minimal distance is `1` — least action picks the shared shortcut. -/
def sharedVsFormula : MinDistance where
  Real := Bool
  cost := fun b => match b with | true => 101 | false => 1
  reach := 1
  reach_le := by intro r; cases r <;> decide
  reach_attained := ⟨false, rfl⟩

/-- **The determined minimum lands at the shared altitude (proved).**  Least action = maximal sharing: the
minimal distance is the cheapest (most-shared) realization (`= 1`), strictly below the formula realization
(`= 101`).  The geometry selects the shortcut, so the formula-altitude bound does not transfer to the reach. -/
theorem minimal_distance_is_the_shared_altitude :
    sharedVsFormula.reach = 1 ∧ sharedVsFormula.cost true = 101 ∧
    sharedVsFormula.reach < sharedVsFormula.cost true :=
  ⟨rfl, rfl, by decide⟩

/-- **The Lagrangian determines the reach, but its lower bound is over all realizations (proved).**  Left: the
reach is determined uniquely (non-circular object, the step).  Right: lower-bounding it quantifies over every
realization (`cost_super`).  The geometry fixes the *frame*; the *value* for SAT is the wall. -/
theorem lagrangian_determines_but_lower_bound_is_all (M : MinDistance) :
    (∀ m, (∀ r, m ≤ M.cost r) → (∃ r, M.cost r = m) → m = M.reach)
    ∧ (∀ B, B ≤ M.reach ↔ ∀ r, B ≤ M.cost r) :=
  ⟨fun m hlb hatt => reach_unique M m hlb hatt, reach_ge_iff_all M⟩

end PallLean.Paper93.DeepMath.PathB.MinimalDistance

#print axioms PallLean.Paper93.DeepMath.PathB.MinimalDistance.reach_unique
#print axioms PallLean.Paper93.DeepMath.PathB.MinimalDistance.upper_bound_easy
#print axioms PallLean.Paper93.DeepMath.PathB.MinimalDistance.reach_ge_iff_all
#print axioms PallLean.Paper93.DeepMath.PathB.MinimalDistance.minimal_distance_is_the_shared_altitude
#print axioms PallLean.Paper93.DeepMath.PathB.MinimalDistance.lagrangian_determines_but_lower_bound_is_all
