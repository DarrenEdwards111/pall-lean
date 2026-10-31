import PallLean.Paper93.DeepMath.PathB.ComputationalDepthAdaptiveTrajectoryDebt

/-!
# A lower bound on `SwitchCost` for the explicit witness geometry (proved, conditional on low boundary)

`adaptive_boundary_tradeoff` proved `|P| ≤ 2^{B_0} + ∑_τ 2^{B_τ} + ∑_τ SwitchCost_τ`: a correct adaptive
observer pays *either* in boundary *or* in switch cost.  Rearranging isolates the **switch-cost** channel:

```
∑_τ SwitchCost_τ  ≥  |P|  −  2^{B_0}  −  ∑_τ 2^{B_τ}.
```

So when the boundary budget is small, the switch cost must carry the **entire fooling-set burden** — exactly
"translating witness-branch information across decompositions is expensive."  For the explicit `2^n` hypercube
witness geometry and a *low-boundary* trajectory (every `B_τ ≤ b`, `T` steps) this is

```
∑_τ SwitchCost_τ  ≥  2^n  −  (T+1)·2^b,
```

which for `b = O(log n)`, `T = poly` is `2^n − poly` = **super-polynomial**.

## Proved (clean axioms, no `sorry`)

* `switchCost_lower_bound` — for any fooling set `P` and correct adaptive trajectory,
  `|P| − 2^{B_0} − ∑_τ 2^{B_τ} ≤ ∑_τ SwitchCost_τ`.
* `hypercube_switchCost_lower_bound` — concrete `|P| = 2^n`:
  `2^n − 2^{B_0} − ∑_τ 2^{B_τ} ≤ ∑_τ SwitchCost_τ`.
* `hypercube_lowBoundary_switchCost_superpoly` — low-boundary form: if every `B_τ ≤ b`, then
  `2^n − (T+1)·2^b ≤ ∑_τ SwitchCost_τ` — super-polynomial switch cost for `b = O(log n)`, `T = poly`.

## Honest scope — this is a genuine lower bound, but it is NOT `P ≠ NP`

Two things keep this honest and restricted, and both are the residual escapes named throughout the arc:

1. **It is the complete (`2^n`) fooling geometry.**  The bound is for an observer that must separate *all*
   `2^n` hypercube points.  A SAT decider need not face the complete fooling set *under the decomposition it is
   free to choose* — the min-over-decompositions escape is untouched.  So this lower-bounds `SwitchCost` for
   the explicit maximal witness geometry, not for SAT under every decomposition.
2. **It is conditional on low boundary.**  The bound `2^n − (T+1)·2^b ≤ ∑ SwitchCost` is *vacuous* once
   `(T+1)·2^b ≥ 2^n` — i.e. a trajectory may pay in **boundary** instead (linear/poly space, `b ≥ n`),
   driving the switch-cost lower bound to zero.  This is the same boundary-vs-switch trade the tradeoff
   theorem makes explicit: we proved the switch channel is expensive *only when the boundary channel is
   cheap*.

So this **does** prove "translating witness-branch information across decompositions is expensive" — for the
explicit `2^n` witness geometry, on low-boundary trajectories.  It does **not** close `P ≠ NP`: the
unconditional statement (super-poly `∑ SwitchCost` for SAT under *every* low-boundary low-switch decomposition,
with the boundary escape also blocked) is the all-decompositions quantifier = `P ≠ NP`, and is **not** proved
here.  The genuine new mathematics — that SAT's witness geometry forces a *complete-enough* fooling set under
every cheap decomposition — remains the open frontier, named not faked.
-/

namespace PallLean.Paper93.DeepMath.PathB.BoundaryDebt

open scoped BigOperators

variable {X : Type*} [DecidableEq X]

/-- **Lower bound on total switch cost (proved).**  For a correct adaptive trajectory deciding a
fooling-set-`P` instance, the total decomposition-switch cost carries whatever the boundary budget does not:
`|P| − 2^{B_0} − ∑_τ 2^{B_τ} ≤ ∑_τ SwitchCost_τ`. -/
theorem switchCost_lower_bound (P : Finset X) (F : Finset (X × X))
    (hfool : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → (x, y) ∈ F)
    (B : ℕ → ℕ) (switchCost : ℕ → ℕ) (view0 : X → Fin (2 ^ B 0))
    (debt : ℕ → ℕ) (T : ℕ)
    (hinit : debt 0 = debtCount F view0)
    (hservice : ∀ t, debt t ≤ debt (t + 1) + 2 ^ B t + switchCost t)
    (hcleared : debt T = 0) :
    P.card - 2 ^ B 0 - (∑ t ∈ Finset.range T, 2 ^ B t) ≤ ∑ t ∈ Finset.range T, switchCost t := by
  have h := adaptive_boundary_tradeoff P F hfool B switchCost view0 debt T hinit hservice hcleared
  omega

/-- **Concrete witness geometry (`|P| = 2^n`).**  For the complete hypercube fooling family,
`2^n − 2^{B_0} − ∑_τ 2^{B_τ} ≤ ∑_τ SwitchCost_τ`. -/
theorem hypercube_switchCost_lower_bound (n : ℕ)
    (B : ℕ → ℕ) (switchCost : ℕ → ℕ) (view0 : (Fin n → Bool) → Fin (2 ^ B 0))
    (debt : ℕ → ℕ) (T : ℕ)
    (hinit : debt 0 = debtCount (hypercubeFool n) view0)
    (hservice : ∀ t, debt t ≤ debt (t + 1) + 2 ^ B t + switchCost t)
    (hcleared : debt T = 0) :
    2 ^ n - 2 ^ B 0 - (∑ t ∈ Finset.range T, 2 ^ B t) ≤ ∑ t ∈ Finset.range T, switchCost t := by
  have h := switchCost_lower_bound (Finset.univ : Finset (Fin n → Bool)) (hypercubeFool n)
    (hypercube_fool n) B switchCost view0 debt T hinit hservice hcleared
  rwa [hypercube_card] at h

/-- **Super-polynomial switch cost for low-boundary trajectories (proved).**  If every step's boundary is at
most `b`, then for the `2^n` witness geometry `2^n − (T+1)·2^b ≤ ∑_τ SwitchCost_τ`.  For `b = O(log n)` and
`T = poly`, the right side is `poly`, so `∑_τ SwitchCost_τ ≥ 2^n − poly` = **super-polynomial**: a low-boundary
observer of the witness geometry must pay super-poly total switch cost. -/
theorem hypercube_lowBoundary_switchCost_superpoly (n b : ℕ)
    (B : ℕ → ℕ) (switchCost : ℕ → ℕ) (view0 : (Fin n → Bool) → Fin (2 ^ B 0))
    (debt : ℕ → ℕ) (T : ℕ)
    (hinit : debt 0 = debtCount (hypercubeFool n) view0)
    (hservice : ∀ t, debt t ≤ debt (t + 1) + 2 ^ B t + switchCost t)
    (hbound : ∀ t, B t ≤ b)
    (hcleared : debt T = 0) :
    2 ^ n - (T + 1) * 2 ^ b ≤ ∑ t ∈ Finset.range T, switchCost t := by
  have h := adaptive_boundary_tradeoff (Finset.univ : Finset (Fin n → Bool)) (hypercubeFool n)
    (hypercube_fool n) B switchCost view0 debt T hinit hservice hcleared
  rw [hypercube_card] at h
  have hb0 : 2 ^ B 0 ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (hbound 0)
  have hsumB : ∑ t ∈ Finset.range T, 2 ^ B t ≤ T * 2 ^ b := by
    calc ∑ t ∈ Finset.range T, 2 ^ B t
        ≤ ∑ _t ∈ Finset.range T, 2 ^ b :=
          Finset.sum_le_sum (fun t _ => Nat.pow_le_pow_right (by norm_num) (hbound t))
      _ = T * 2 ^ b := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hkey : (T + 1) * 2 ^ b = 2 ^ b + T * 2 ^ b := by ring
  rw [hkey]
  omega

end PallLean.Paper93.DeepMath.PathB.BoundaryDebt

#print axioms PallLean.Paper93.DeepMath.PathB.BoundaryDebt.switchCost_lower_bound
#print axioms PallLean.Paper93.DeepMath.PathB.BoundaryDebt.hypercube_switchCost_lower_bound
#print axioms PallLean.Paper93.DeepMath.PathB.BoundaryDebt.hypercube_lowBoundary_switchCost_superpoly
