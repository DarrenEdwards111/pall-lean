import PallLean.Paper93.DeepMath.PathB.ComputationalDepthFoolingDebt

/-!
# `hdebt` proved for the bounded-boundary-throughout trajectory class (a restricted lower bound)

`ComputationalDepthSATActionConjecture.lean` showed the open input is `hdebt` (every correct trajectory has
super-log debt) — `P ≠ NP`-strength because a trajectory can *raise* its boundary over observer time.  This
file **proves `hdebt` for the restricted class where that escape is forbidden**: trajectories whose boundary
stays `≤ B` *throughout* (equivalently, servicing rate `≤ 2^B` per step — a width-`2^B` observer).

For such a trajectory the *initial* view also has boundary `≤ B`, so the debt mechanism
(`foolingSet_forces_debt`) bites at step 0, and the conservation (`merge_pay`) binds the whole action/time.

## Proved (clean axioms, no `sorry`)

* `bounded_boundary_time_lower_bound` — a *correct* bounded-boundary-throughout trajectory (servicing rate
  `≤ 2^B`, all debt cleared by time `T`) deciding an instance with a fooling set `P` satisfies
  `|P| − 2^B ≤ T · 2^B`.
* `bounded_boundary_tradeoff` — equivalently `|P| ≤ (T + 1) · 2^B`: a width-`2^B` observer needs time
  `T ≥ |P| / 2^B − 1`.

For the expander-amplified fooling set `|P| = 2^{Ω(n)}` and `B = O(log n)` (`2^B = poly`), this is
`T ≥ 2^{Ω(n)} / poly` = **super-polynomial** — so **SAT has no low-time bounded-boundary trajectory**: `hdebt`
holds on this class.

## Honest scope — this is a RESTRICTED lower bound, not `P ≠ NP`

The class is **bounded-boundary-throughout** (width `≤ 2^B`), which *forbids the escape* that makes the general
`hdebt` open: a general observer may raise its boundary (use large space), and that is exactly what this class
disallows.  So this is a genuine restricted lower bound — SAT needs super-poly time on width-`poly` (bounded
boundary) observers, given its `2^{Ω(n)}` fooling set — in the spirit of streaming / bounded-width branching
program / small-space lower bounds.  It is **not** `P ≠ NP`: a poly-time SAT decider may use poly *space*
(boundary up to `poly`, `2^B` up to exponential), well outside this class.  The general `hdebt` (every
trajectory, unbounded boundary) remains the open quantifier; nothing here closes it.
-/

namespace PallLean.Paper93.DeepMath.PathB.BoundaryDebt

open scoped BigOperators

variable {X : Type*} [DecidableEq X]

/-- **`hdebt` for bounded-boundary-throughout trajectories (proved).**  A correct trajectory whose servicing
rate stays `≤ 2^B` (boundary `≤ B` throughout), with initial view into `Fin (2^B)` and all debt cleared by
time `T`, deciding an instance with fooling set `P`, satisfies `|P| − 2^B ≤ T · 2^B`. -/
theorem bounded_boundary_time_lower_bound {B : ℕ}
    (P : Finset X) (F : Finset (X × X))
    (hfool : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → (x, y) ∈ F)
    (view0 : X → Fin (2 ^ B))
    (debt : ℕ → ℕ) (T : ℕ)
    (hinit : debt 0 = debtCount F view0)
    (hservice : ∀ t, debt t ≤ debt (t + 1) + 2 ^ B)
    (hcleared : debt T = 0) :
    P.card - 2 ^ B ≤ T * 2 ^ B := by
  have h1 : P.card - 2 ^ B ≤ debt 0 := by
    rw [hinit]; exact foolingSet_forces_debt P view0 F hfool
  have h2 : debt 0 ≤ T * 2 ^ B := merge_pay debt (2 ^ B) hservice T hcleared
  omega

/-- **The time–boundary tradeoff** for bounded-boundary-throughout observers: `|P| ≤ (T + 1) · 2^B`, i.e.
`T ≥ |P| / 2^B − 1`.  Width-`2^B` deciders need time proportional to the fooling-set size over the width. -/
theorem bounded_boundary_tradeoff {B : ℕ}
    (P : Finset X) (F : Finset (X × X))
    (hfool : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → (x, y) ∈ F)
    (view0 : X → Fin (2 ^ B))
    (debt : ℕ → ℕ) (T : ℕ)
    (hinit : debt 0 = debtCount F view0)
    (hservice : ∀ t, debt t ≤ debt (t + 1) + 2 ^ B)
    (hcleared : debt T = 0) :
    P.card ≤ (T + 1) * 2 ^ B := by
  have h1 := bounded_boundary_time_lower_bound P F hfool view0 debt T hinit hservice hcleared
  have hexp : (T + 1) * 2 ^ B = T * 2 ^ B + 2 ^ B := by ring
  omega

end PallLean.Paper93.DeepMath.PathB.BoundaryDebt

#print axioms PallLean.Paper93.DeepMath.PathB.BoundaryDebt.bounded_boundary_time_lower_bound
#print axioms PallLean.Paper93.DeepMath.PathB.BoundaryDebt.bounded_boundary_tradeoff
