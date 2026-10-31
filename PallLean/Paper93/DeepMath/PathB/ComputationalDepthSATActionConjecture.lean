import PallLean.Paper93.DeepMath.PathB.ComputationalDepthObserverTimeDebt

/-!
# "SAT has no low-action observer-time trajectory" — this IS the open quantifier (not proved)

This file states the conjecture precisely and proves the **reduction** that locates it, while making
unmistakable that the conjecture **itself is `P ≠ NP`** and is **not proved here** (and is not faked).

## The statement

A `Trajectory` is a correct observer-time computation deciding a problem; `action t` is its time-integrated
boundary action `S_obs`, `initialDebt t` its initial distinguishability debt.  The conservation
(`ObserverTimeDebt.correct_needs_action`) gives `initialDebt t ≤ action t` for correct trajectories.

> **`SATNoLowActionTrajectory threshold`** := every correct trajectory deciding SAT has `action > threshold`.

For a super-polynomial `threshold` this says SAT has no sub-super-poly observer-time trajectory — i.e. **SAT is
hard** — i.e. `P ≠ NP`-strength.

## What is proved (clean axioms, no `sorry`) — the REDUCTION only

* `no_low_action_of_high_debt` — **the conjecture reduces to the all-trajectories debt bound**: *if* every
  correct trajectory has `initialDebt > threshold`, then (by conservation `debt ≤ action`) every correct
  trajectory has `action > threshold` — i.e. `SATNoLowActionTrajectory`.  One line: `lt_of_lt_of_le`.

That is the honest content: **conservation turns "high debt under every trajectory" into "no low-action
trajectory".**

## What is NOT proved — and will not be faked

The hypothesis `hdebt` (every correct SAT trajectory has super-log *initial* debt) is the **open
all-decompositions quantifier** (`= CookLevinFrontierHyp` in debt form).  The debt *mechanism* is proved
(`BoundaryDebt.foolingSet_forces_debt`: a fooling set forces debt `≥ K − 2^B` for a **fixed low-boundary**
view), and the expander amplifies `K` to `2^{Ω(n)}`.  But a trajectory may **raise its boundary** over
observer time (paying action), so a *single* view's debt does not bind it; ruling out **every** correct
trajectory — the `min` over trajectories — is exactly the open problem.

**`hdebt` is `P ≠ NP`.**  It is left as an explicit hypothesis, not proved.  There is deliberately **no**
theorem in this file that concludes `SATNoLowActionTrajectory` (or `P ≠ NP`) unconditionally.  Proving
`hdebt` would require genuine new mathematics — that SAT's witness-branch debt cannot be serviced by any
low-action observer-time trajectory — which no one has, and which this development does not claim.
-/

namespace PallLean.Paper93.DeepMath.PathB.SATActionConjecture

variable {Traj : Type*}

/-- **`SATNoLowActionTrajectory`** (the conjecture, a `Prop`): every correct trajectory deciding SAT has
action above `threshold`.  For super-poly `threshold` this is `P ≠ NP`-strength.  *Not proved.* -/
def SATNoLowActionTrajectory (action : Traj → ℕ) (correct : Traj → Prop) (threshold : ℕ) : Prop :=
  ∀ t, correct t → threshold < action t

/-- **The reduction (proved).**  Given the conservation `initialDebt t ≤ action t` for correct trajectories
(from `ObserverTimeDebt.correct_needs_action`) and the **open** all-trajectories debt bound `hdebt` (every
correct trajectory has `initialDebt > threshold`), every correct trajectory has `action > threshold` — i.e.
`SATNoLowActionTrajectory`.

This is the *only* claim: the conjecture **follows from** `hdebt`, which is the open `P ≠ NP` quantifier.
Nothing here proves `hdebt`. -/
theorem no_low_action_of_high_debt {threshold : ℕ} (action initialDebt : Traj → ℕ)
    (correct : Traj → Prop)
    (conservation : ∀ t, correct t → initialDebt t ≤ action t)
    (hdebt : ∀ t, correct t → threshold < initialDebt t) :
    SATNoLowActionTrajectory action correct threshold :=
  fun t ht => lt_of_lt_of_le (hdebt t ht) (conservation t ht)

end PallLean.Paper93.DeepMath.PathB.SATActionConjecture

#print axioms PallLean.Paper93.DeepMath.PathB.SATActionConjecture.no_low_action_of_high_debt
