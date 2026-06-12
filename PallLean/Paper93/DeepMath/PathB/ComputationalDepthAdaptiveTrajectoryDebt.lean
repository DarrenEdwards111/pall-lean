import PallLean.Paper93.DeepMath.PathB.ComputationalDepthAdaptiveTrajectory

/-!
# Item 5, refined: adaptive trajectories with an explicit decomposition-switch cost

The structural file (`ComputationalDepthAdaptiveTrajectory.lean`) folded the cost of changing decomposition
into the locality hypothesis.  This file makes that cost **explicit and additive**, following the hierarchy
plan: model the per-step **switch cost** `SwitchCost(D_τ, D_{τ+1})` and prove the **weakest nontrivial**
adaptive debt theorem first.

## The accounting

When the observer changes decomposition `D_τ → D_{τ+1}` it must pay to translate unresolved information between
coordinate systems.  So the per-step debt servicing is bounded by the boundary capacity **plus** the switch
cost:

```
debt τ  ≤  debt (τ+1)  +  2^{B_τ}  +  SwitchCost_τ
```

and the time-integrated action gains a switch term:

```
S_obs  =  ∑_τ 2^{B_τ}  +  ∑_τ SwitchCost_τ.
```

**Either the boundary pays or the switch pays** — neither is free.

## Proved (clean axioms, no `sorry`)

* `adaptive_boundary_tradeoff` — a correct adaptive trajectory deciding a fooling-set-`P` instance satisfies
  `|P| ≤ 2^{B_0} + ∑_τ 2^{B_τ} + ∑_τ SwitchCost_τ`.  (Conservation with the per-step rate `2^{B_τ} +
  SwitchCost_τ`; `foolingSet_forces_debt` at step 0.)  This is the item-5 analogue of `average_boundary_tradeoff`.
* `adaptive_boundary_tradeoff_bounded_switch` — bounded-switch class `∑_τ SwitchCost_τ ≤ C`:
  `|P| ≤ 2^{B_0} + ∑_τ 2^{B_τ} + C`.
* `fixed_decomposition_recovers_average` — `SwitchCost ≡ 0` recovers exactly `|P| ≤ 2^{B_0} + ∑_τ 2^{B_τ}`.
* `adaptive_low_action_fails` — separation form: total action below `|P|` ⇒ the observer errs (`debt T ≠ 0`).

## The easy cases (instantiations)

* **fixed decomposition** — `SwitchCost_τ = 0`: recovers the average-boundary theorem (`∑ SwitchCost = 0`).
* **bounded number of switches** — at most `s` switches, each costing `≤ M`: `C ≤ s·M` (feed into the bounded
  form).
* **local switches** — each switch changes only `r` variables, so `SwitchCost_τ ≤ f(r)` is bounded per step.

## Honest SAT frontier (named, not faked)

The open `P ≠ NP` statement is now clean:

> **Every correct SAT observer trajectory has large boundary-action *or* large decomposition-switch cost.**

I.e. `∑_τ 2^{B_τ} + ∑_τ SwitchCost_τ` is super-polynomial for SAT under *every* adaptive trajectory.  The
bound above proves the *contrapositive direction is the only escape*: a SAT decider must either keep the
boundary high (paid in `∑ 2^{B_τ}`) or switch decompositions a lot / expensively (paid in `∑ SwitchCost_τ`).
Ruling out *both* being small simultaneously, under every trajectory, is the all-decompositions quantifier =
`P ≠ NP`.  This file does **not** prove it; it makes the two payment channels explicit so the open statement is
a single inequality about their sum.  The genuine modelling question left open is a *lower bound* on
`SwitchCost` for SAT's witness geometry (that translating witness-branch information across decompositions is
expensive) — that lower bound is the new mathematics, deliberately not assumed.
-/

namespace PallLean.Paper93.DeepMath.PathB.BoundaryDebt

open PallLean.Paper93.DeepMath.PathB.ObserverTimeDebt
open scoped BigOperators

variable {X : Type*} [DecidableEq X]

/-- **Adaptive boundary tradeoff (proved): the item-5 analogue of `average_boundary_tradeoff`.**  A correct
adaptive trajectory whose per-step debt servicing is bounded by the boundary capacity `2^{B_τ}` *plus* the
decomposition switch cost `SwitchCost_τ`, deciding a fooling-set-`P` instance, satisfies
`|P| ≤ 2^{B_0} + ∑_{τ<T} 2^{B_τ} + ∑_{τ<T} SwitchCost_τ`.  Either the boundary pays or the switch pays. -/
theorem adaptive_boundary_tradeoff (P : Finset X) (F : Finset (X × X))
    (hfool : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → (x, y) ∈ F)
    (B : ℕ → ℕ) (switchCost : ℕ → ℕ) (view0 : X → Fin (2 ^ B 0))
    (debt : ℕ → ℕ) (T : ℕ)
    (hinit : debt 0 = debtCount F view0)
    (hservice : ∀ t, debt t ≤ debt (t + 1) + 2 ^ B t + switchCost t)
    (hcleared : debt T = 0) :
    P.card ≤ 2 ^ B 0 + (∑ t ∈ Finset.range T, 2 ^ B t) + ∑ t ∈ Finset.range T, switchCost t := by
  have h1 : P.card - 2 ^ B 0 ≤ debt 0 := by
    rw [hinit]; exact foolingSet_forces_debt P view0 F hfool
  have h2 : debt 0 ≤ (∑ t ∈ Finset.range T, 2 ^ B t) + ∑ t ∈ Finset.range T, switchCost t := by
    have hc := debt_conservation_varying debt (fun t => 2 ^ B t + switchCost t)
      (fun t => by show debt t ≤ debt (t + 1) + (2 ^ B t + switchCost t); have := hservice t; omega) T
    rw [hcleared, Nat.zero_add, Finset.sum_add_distrib] at hc
    exact hc
  omega

/-- **Bounded-switch class.**  If the total decomposition-switch cost is at most `C`, then
`|P| ≤ 2^{B_0} + ∑_{τ<T} 2^{B_τ} + C`. -/
theorem adaptive_boundary_tradeoff_bounded_switch (P : Finset X) (F : Finset (X × X))
    (hfool : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → (x, y) ∈ F)
    (B : ℕ → ℕ) (switchCost : ℕ → ℕ) (view0 : X → Fin (2 ^ B 0))
    (debt : ℕ → ℕ) (T C : ℕ)
    (hinit : debt 0 = debtCount F view0)
    (hservice : ∀ t, debt t ≤ debt (t + 1) + 2 ^ B t + switchCost t)
    (hcleared : debt T = 0)
    (hswitch : ∑ t ∈ Finset.range T, switchCost t ≤ C) :
    P.card ≤ 2 ^ B 0 + (∑ t ∈ Finset.range T, 2 ^ B t) + C := by
  have h := adaptive_boundary_tradeoff P F hfool B switchCost view0 debt T hinit hservice hcleared
  omega

/-- **Fixed decomposition recovers the average-boundary theorem (proved).**  With zero switch cost the bound
collapses to `|P| ≤ 2^{B_0} + ∑_{τ<T} 2^{B_τ}`. -/
theorem fixed_decomposition_recovers_average (P : Finset X) (F : Finset (X × X))
    (hfool : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → (x, y) ∈ F)
    (B : ℕ → ℕ) (view0 : X → Fin (2 ^ B 0))
    (debt : ℕ → ℕ) (T : ℕ)
    (hinit : debt 0 = debtCount F view0)
    (hservice : ∀ t, debt t ≤ debt (t + 1) + 2 ^ B t)
    (hcleared : debt T = 0) :
    P.card ≤ 2 ^ B 0 + ∑ t ∈ Finset.range T, 2 ^ B t := by
  have h := adaptive_boundary_tradeoff P F hfool B (fun _ => 0) view0 debt T hinit
    (fun t => by show debt t ≤ debt (t + 1) + 2 ^ B t + 0; have := hservice t; omega) hcleared
  simpa using h

/-- **Separation form (proved): a low-total-action adaptive observer errs.**  If the combined action
`2^{B_0} + ∑_τ 2^{B_τ} + ∑_τ SwitchCost_τ` is below `|P|`, the observer cannot clear its debt (`debt T ≠ 0`).
For SAT this is the frontier: a decider must pay either in boundary or in switch cost. -/
theorem adaptive_low_action_fails (P : Finset X) (F : Finset (X × X))
    (hfool : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → (x, y) ∈ F)
    (B : ℕ → ℕ) (switchCost : ℕ → ℕ) (view0 : X → Fin (2 ^ B 0))
    (debt : ℕ → ℕ) (T : ℕ)
    (hinit : debt 0 = debtCount F view0)
    (hservice : ∀ t, debt t ≤ debt (t + 1) + 2 ^ B t + switchCost t)
    (hlow : 2 ^ B 0 + (∑ t ∈ Finset.range T, 2 ^ B t) + ∑ t ∈ Finset.range T, switchCost t < P.card) :
    debt T ≠ 0 := by
  intro hcleared
  have h := adaptive_boundary_tradeoff P F hfool B switchCost view0 debt T hinit hservice hcleared
  omega

end PallLean.Paper93.DeepMath.PathB.BoundaryDebt

#print axioms PallLean.Paper93.DeepMath.PathB.BoundaryDebt.adaptive_boundary_tradeoff
#print axioms PallLean.Paper93.DeepMath.PathB.BoundaryDebt.adaptive_boundary_tradeoff_bounded_switch
#print axioms PallLean.Paper93.DeepMath.PathB.BoundaryDebt.fixed_decomposition_recovers_average
#print axioms PallLean.Paper93.DeepMath.PathB.BoundaryDebt.adaptive_low_action_fails
