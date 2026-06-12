import PallLean.Paper93.DeepMath.PathB.ComputationalDepthFoolingDebt
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthObserverTimeDebt

/-!
# Average / total-action boundary tradeoff (proved): boundary spikes allowed, total service bounded

The bounded-boundary-throughout result fixed `B_τ = B` for *every* `τ`.  This file proves the stronger
**time-varying** version: the boundary may **spike** at individual steps, and only the **total service
capacity** `∑_τ 2^{B_τ}` is constrained.  This is much closer to real machines (which may briefly use a large
configuration), and is the next climb toward the full wall.

## Proved (clean axioms, no `sorry`)

* `average_boundary_tradeoff` — a correct observer (debt cleared by time `T`) with time-varying boundary
  `B_τ` (servicing rate `≤ 2^{B_τ}` per step) deciding a fooling-set-`P` instance satisfies
  **`|P| ≤ 2^{B_0} + ∑_{τ<T} 2^{B_τ}`** — the total service capacity (plus the initial `2^{B_0}`) must cover
  the fooling set.  Proof: `foolingSet_forces_debt` at step 0 (`debt 0 ≥ |P| − 2^{B_0}`) +
  `debt_conservation_varying` (`debt 0 ≤ ∑_τ 2^{B_τ}`).
* `average_boundary_low_action_fails` — separation form: if `2^{B_0} + ∑_τ 2^{B_τ} < |P|` (total action below
  the fooling set), the observer **cannot clear its debt** (`debt T ≠ 0`) — it errs.

So a correct observer's **total boundary action must be `≥ |P| − 2^{B_0}`**, regardless of how it
distributes boundary across observer time — occasional spikes are allowed, but the integral is conserved.

## Honest scope — still restricted (where the escape now lives)

This allows boundary spikes but bounds the **total** `∑_τ 2^{B_τ}`.  The remaining escape (and the open
`P ≠ NP` core) is a **single huge spike**: one step with `2^{B_τ} ≥ |P|` (boundary `≥ log|P| ≈ cn`, i.e.
linear space) makes the total `≥ |P|` by itself, so the bound is satisfied with no time cost — the
brute-force "read everything into a large configuration" decider.  Ruling that out is again the
linear-to-poly-boundary regime the fooling-debt mechanism cannot reach (`2^{B} ≥ |P|` ⇒ enough states to
separate the fooling set).  So this is the **bounded-total-action** restricted lower bound — strictly larger
than bounded-boundary-throughout (spikes allowed) — with the single-spike / poly-space case the open core.
The hierarchy `B = O(1), O(log n), O(log^k n), n^ε` (item 1) follows by specialising `B_τ`: e.g. `B_τ ≤ B`
gives `|P| ≤ (T+1)·2^B` (the throughout case).
-/

namespace PallLean.Paper93.DeepMath.PathB.BoundaryDebt

open PallLean.Paper93.DeepMath.PathB.ObserverTimeDebt
open scoped BigOperators

variable {X : Type*} [DecidableEq X]

/-- **Average / total-action tradeoff (proved).**  A correct observer with time-varying boundary `B_τ`
(servicing rate `≤ 2^{B_τ}`, debt cleared by time `T`) deciding a fooling-set-`P` instance satisfies
`|P| ≤ 2^{B_0} + ∑_{τ<T} 2^{B_τ}`: the total service capacity covers the fooling set.  Boundary spikes are
allowed; the integral is conserved. -/
theorem average_boundary_tradeoff (P : Finset X) (F : Finset (X × X))
    (hfool : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → (x, y) ∈ F)
    (B : ℕ → ℕ) (view0 : X → Fin (2 ^ B 0))
    (debt : ℕ → ℕ) (T : ℕ)
    (hinit : debt 0 = debtCount F view0)
    (hservice : ∀ t, debt t ≤ debt (t + 1) + 2 ^ B t)
    (hcleared : debt T = 0) :
    P.card ≤ 2 ^ B 0 + ∑ t ∈ Finset.range T, 2 ^ B t := by
  have h1 : P.card - 2 ^ B 0 ≤ debt 0 := by
    rw [hinit]; exact foolingSet_forces_debt P view0 F hfool
  have h2 : debt 0 ≤ ∑ t ∈ Finset.range T, 2 ^ B t := by
    have hc := debt_conservation_varying debt (fun t => 2 ^ B t) hservice T
    rw [hcleared] at hc
    simpa using hc
  omega

/-- **Separation form (proved): a low-total-action observer errs.**  If the total service capacity
`2^{B_0} + ∑_{τ<T} 2^{B_τ}` is below the fooling set `|P|`, the observer cannot clear its debt (`debt T ≠ 0`):
it errs.  No correct observer has total action below `|P|`. -/
theorem average_boundary_low_action_fails (P : Finset X) (F : Finset (X × X))
    (hfool : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → (x, y) ∈ F)
    (B : ℕ → ℕ) (view0 : X → Fin (2 ^ B 0))
    (debt : ℕ → ℕ) (T : ℕ)
    (hinit : debt 0 = debtCount F view0)
    (hservice : ∀ t, debt t ≤ debt (t + 1) + 2 ^ B t)
    (hlow : 2 ^ B 0 + ∑ t ∈ Finset.range T, 2 ^ B t < P.card) :
    debt T ≠ 0 := by
  intro hcleared
  have h := average_boundary_tradeoff P F hfool B view0 debt T hinit hservice hcleared
  omega

end PallLean.Paper93.DeepMath.PathB.BoundaryDebt

#print axioms PallLean.Paper93.DeepMath.PathB.BoundaryDebt.average_boundary_tradeoff
#print axioms PallLean.Paper93.DeepMath.PathB.BoundaryDebt.average_boundary_low_action_fails
