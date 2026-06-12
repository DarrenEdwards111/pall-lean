import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBoundaryDebt

/-!
# Observer-time boundary debt: the time-integrated action is conserved (proved)

`ComputationalDepthBoundaryDebt.lean` proved "merge now ⇒ pay later" with a *fixed* servicing rate.  The
N-Frame book's **observer time τ** (a sequence of epistemic updates, each with informational cost, under a
bounded cognitive light cone) refines this: the servicing rate **varies with τ** — the machine may change its
decomposition over observer time.  The key fix this gives, and the weakness it closes:

> a machine can hide boundary *at any single cut* by changing decomposition over time — but the
> **time-integrated boundary action `S_obs = ∑_τ rate_τ` is conserved**, so it *cannot* hide the total cost.

This is the dynamical (boundary-*action*) version of the God Move, where EQUALITY's escape (carry one bit over
a cheap streaming decomposition) is allowed *per step* yet the integral still tracks the debt.

## Proved (clean axioms, no `sorry`)

* `debt_conservation_varying` — telescoping with time-varying rate: `debt 0 ≤ debt T + ∑_{τ<T} rate τ`.
* `observerTimeAction` — the time-integrated boundary action `S_obs = ∑_{τ<T} rate τ`.
* `correct_needs_action` — **a faithful observer must spend action ≥ its initial debt**: `debt T = 0 ⇒
  debt 0 ≤ S_obs`.  (Changing decomposition over τ does not help — the integral is what is conserved.)
* `bounded_action_fails` — **bounded observer-time action ⇒ faithful decision impossible**: if `S_obs <
  debt 0`, then `debt T ≠ 0` (some must-separate pair stays merged — incorrect).

## The full action and the open input

Per the route-selector, the observer-time action is `S_obs = ∑_τ (B_τ + D_τ + E_τ − A_τ)` (boundary, merge
debt, approximation error, amplification gain).  Here `rate τ` is the per-step *servicing capacity* (`≈ B_τ`,
the boundary at update τ), and `debt` is the merge-debt `D_τ` being serviced.  The conservation is **proved**.

What remains **open** (unchanged, = `CookLevinFrontierHyp` in observer-time form): for SAT, the initial debt
`debt 0` (distinguishable witness-branch pairs) is **super-logarithmic**, and `rate τ = O(B_τ)` with
`∑_τ B_τ` small for any *low-boundary* trajectory — so no low-boundary observer-time trajectory can carry the
witness-branch debt across all τ without exploding `S_obs` or erring.  Proving that for SAT under *every*
trajectory is the open quantifier.  Nothing here asserts it; the contribution is that the **conservation of
the time-integrated action is now a theorem**, closing the "hide boundary over time" loophole.
-/

namespace PallLean.Paper93.DeepMath.PathB.ObserverTimeDebt

open scoped BigOperators

/-- **Debt conservation with time-varying servicing rate (proved).**  If at each observer-time step `t` the
debt drops by at most `rate t`, the initial debt is bounded by the final debt plus the **time-integrated**
servicing `∑_{t<T} rate t`. -/
theorem debt_conservation_varying (debt : ℕ → ℕ) (rate : ℕ → ℕ)
    (hservice : ∀ t, debt t ≤ debt (t + 1) + rate t) (T : ℕ) :
    debt 0 ≤ debt T + ∑ t ∈ Finset.range T, rate t := by
  induction T with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ]
      calc debt 0 ≤ debt k + ∑ t ∈ Finset.range k, rate t := ih
        _ ≤ (debt (k + 1) + rate k) + ∑ t ∈ Finset.range k, rate t := by
            have := hservice k; omega
        _ = debt (k + 1) + (∑ t ∈ Finset.range k, rate t + rate k) := by ring

/-- **The observer-time boundary action** `S_obs = ∑_{τ<T} rate τ` — the time-integrated servicing capacity
(the `∑_τ B_τ` term of the N-Frame action). -/
def observerTimeAction (rate : ℕ → ℕ) (T : ℕ) : ℕ := ∑ t ∈ Finset.range T, rate t

/-- **A faithful observer must spend action ≥ its initial debt (proved).**  If all debt is cleared by time
`T` (`debt T = 0`), then `debt 0 ≤ S_obs`.  Changing decomposition over observer time does not help — the
*integrated* action is conserved against the debt. -/
theorem correct_needs_action (debt : ℕ → ℕ) (rate : ℕ → ℕ)
    (hservice : ∀ t, debt t ≤ debt (t + 1) + rate t) (T : ℕ) (hcleared : debt T = 0) :
    debt 0 ≤ observerTimeAction rate T := by
  have h := debt_conservation_varying debt rate hservice T
  rw [observerTimeAction]
  omega

/-- **Bounded observer-time action ⇒ faithful decision impossible (proved).**  If the time-integrated action
is below the initial debt (`S_obs < debt 0`), the debt cannot be cleared (`debt T ≠ 0`): some must-separate
continuation pair stays merged, so the observer errs.  This is the dynamical boundary-action obstruction —
the loophole of hiding boundary by changing decomposition over time is closed by the *integral*. -/
theorem bounded_action_fails (debt : ℕ → ℕ) (rate : ℕ → ℕ)
    (hservice : ∀ t, debt t ≤ debt (t + 1) + rate t) (T : ℕ)
    (hsmall : observerTimeAction rate T < debt 0) :
    debt T ≠ 0 := by
  intro hcleared
  exact absurd (correct_needs_action debt rate hservice T hcleared) (Nat.not_le.mpr hsmall)

end PallLean.Paper93.DeepMath.PathB.ObserverTimeDebt

#print axioms PallLean.Paper93.DeepMath.PathB.ObserverTimeDebt.correct_needs_action
#print axioms PallLean.Paper93.DeepMath.PathB.ObserverTimeDebt.bounded_action_fails
