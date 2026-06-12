import PallLean.Paper93.DeepMath.PathB.ComputationalDepthAverageBoundaryDebt

/-!
# Amortized burst boundary cost (proved): a boundary spike pays its height in time

`average_boundary_tradeoff` left one escape: a **single huge spike** — one step with `2^{B_τ} ≥ |P|`
(boundary `≥ log|P|`) clears the whole fooling set, satisfying the total-action bound with `T = 1`.  That
escape assumes the observer can **jump to an arbitrarily high boundary in one step**.

This file forbids that by charging the spike its **amortized cost**: we add the explicit **locality**
hypothesis that the boundary grows by at most `r` per observer step,

```
B_{τ+1} ≤ B_τ + r        (bounded read-rate / bounded fan-in / bounded write per step)
```

— a real restricted-machine assumption (a step reads/writes a bounded amount, so it cannot acquire more than
`r` new bits of boundary).  Under it `B_τ ≤ B_0 + r·τ`, so reaching the boundary needed to separate a
fooling set of size `|P|` **takes time proportional to `log|P|`**: the spike can no longer be instant.  This
is the amortized statement "a machine cannot briefly raise boundary and erase all debt cheaply — the spike
itself pays full cost," made precise.

## Proved (clean axioms, no `sorry`)

* `boundary_le_of_growth` — bounded growth `B_{τ+1} ≤ B_τ + r` gives `B_τ ≤ B_0 + r·τ`.
* `burst_boundary_time_lower_bound` — a correct observer with bounded boundary growth `r`, deciding a
  fooling-set-`P` instance, satisfies `|P| ≤ (T + 1) · 2^{B_0 + r·T}`.  For `|P| = 2^{Ω(n)}`, `B_0 = O(log n)`,
  `r = O(1)` this forces `r·T ≥ Ω(n)`, i.e. **`T = Ω(n/r)`** — a genuine *time* lower bound the instant-spike
  escape cannot dodge.
* `burst_boundary_low_resource_fails` — separation form: if `(T + 1) · 2^{B_0 + r·T} < |P|` the observer
  cannot clear its debt (`debt T ≠ 0`) — it errs.

## Honest scope — `r` is the new restriction (and the open core stays open)

The locality bound `r` is an **explicit hypothesis**, a genuine restriction: it is precisely the
"boundary cannot spike instantly" assumption, true of bounded-fan-in / bounded-read-rate machines (and the
natural local model), **false in general** for a machine allowed to read many input bits or grow a large
configuration in one step.  So this is the honest form of item 3 — the burst escape is closed *exactly on
the bounded-growth class*, where the spike's height is paid for in time.  It is **not** `P ≠ NP`: a general
poly-time decider's per-step boundary growth is bounded only by `poly` (it may read `poly` bits per step),
so `r = poly` makes `2^{B_0 + r·T}` exponential and the bound vacuous.  Closing the unbounded-growth case
(spike with `r = poly`) is the same linear-to-poly-boundary regime the fooling-debt mechanism cannot reach —
the open quantifier, named not faked.
-/

namespace PallLean.Paper93.DeepMath.PathB.BoundaryDebt

open scoped BigOperators

variable {X : Type*} [DecidableEq X]

/-- **Bounded growth ⇒ linear boundary bound.**  If the boundary grows by at most `r` per step
(`B_{τ+1} ≤ B_τ + r`), then `B_τ ≤ B_0 + r·τ`. -/
theorem boundary_le_of_growth (B : ℕ → ℕ) (r : ℕ) (hgrow : ∀ t, B (t + 1) ≤ B t + r) :
    ∀ t, B t ≤ B 0 + r * t := by
  intro t
  induction t with
  | zero => simp
  | succ k ih =>
      calc B (k + 1) ≤ B k + r := hgrow k
        _ ≤ (B 0 + r * k) + r := by omega
        _ = B 0 + r * (k + 1) := by ring

/-- **Amortized burst time lower bound (proved).**  A correct observer (debt cleared by `T`) with boundary
growth bounded by `r` per step, deciding a fooling-set-`P` instance, satisfies
`|P| ≤ (T + 1) · 2^{B_0 + r·T}`.  The spike's height enters the exponent through `r·T`, so reaching the
capacity to separate `|P|` continuations costs time `T ≳ (log|P| − B_0)/r` — the instant spike is forbidden. -/
theorem burst_boundary_time_lower_bound
    (P : Finset X) (F : Finset (X × X))
    (hfool : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → (x, y) ∈ F)
    (B : ℕ → ℕ) (r : ℕ) (view0 : X → Fin (2 ^ B 0))
    (debt : ℕ → ℕ) (T : ℕ)
    (hinit : debt 0 = debtCount F view0)
    (hservice : ∀ t, debt t ≤ debt (t + 1) + 2 ^ B t)
    (hgrow : ∀ t, B (t + 1) ≤ B t + r)
    (hcleared : debt T = 0) :
    P.card ≤ (T + 1) * 2 ^ (B 0 + r * T) := by
  have hBle := boundary_le_of_growth B r hgrow
  -- total service capacity, each term capped by the max boundary `2^{B_0 + r·T}`
  have hsum : ∑ t ∈ Finset.range T, 2 ^ B t ≤ T * 2 ^ (B 0 + r * T) := by
    calc ∑ t ∈ Finset.range T, 2 ^ B t
        ≤ ∑ _t ∈ Finset.range T, 2 ^ (B 0 + r * T) := by
          apply Finset.sum_le_sum
          intro t ht
          apply Nat.pow_le_pow_right (by norm_num)
          have h1 : B t ≤ B 0 + r * t := hBle t
          have h2 : t ≤ T := le_of_lt (Finset.mem_range.mp ht)
          have h3 : r * t ≤ r * T := Nat.mul_le_mul_left r h2
          omega
      _ = T * 2 ^ (B 0 + r * T) := by
          rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have havg := average_boundary_tradeoff P F hfool B view0 debt T hinit hservice hcleared
  have h2B0 : 2 ^ B 0 ≤ 2 ^ (B 0 + r * T) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have key : (T + 1) * 2 ^ (B 0 + r * T) = 2 ^ (B 0 + r * T) + T * 2 ^ (B 0 + r * T) := by ring
  rw [key]
  omega

/-- **Separation form (proved): under bounded growth, a low-resource observer errs.**  If
`(T + 1) · 2^{B_0 + r·T} < |P|`, the observer cannot clear its debt (`debt T ≠ 0`): no correct observer with
boundary growth `≤ r` per step decides a fooling-set-`P` instance within these resources. -/
theorem burst_boundary_low_resource_fails
    (P : Finset X) (F : Finset (X × X))
    (hfool : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → (x, y) ∈ F)
    (B : ℕ → ℕ) (r : ℕ) (view0 : X → Fin (2 ^ B 0))
    (debt : ℕ → ℕ) (T : ℕ)
    (hinit : debt 0 = debtCount F view0)
    (hservice : ∀ t, debt t ≤ debt (t + 1) + 2 ^ B t)
    (hgrow : ∀ t, B (t + 1) ≤ B t + r)
    (hlow : (T + 1) * 2 ^ (B 0 + r * T) < P.card) :
    debt T ≠ 0 := by
  intro hcleared
  have h := burst_boundary_time_lower_bound P F hfool B r view0 debt T hinit hservice hgrow hcleared
  omega

end PallLean.Paper93.DeepMath.PathB.BoundaryDebt

#print axioms PallLean.Paper93.DeepMath.PathB.BoundaryDebt.boundary_le_of_growth
#print axioms PallLean.Paper93.DeepMath.PathB.BoundaryDebt.burst_boundary_time_lower_bound
#print axioms PallLean.Paper93.DeepMath.PathB.BoundaryDebt.burst_boundary_low_resource_fails
