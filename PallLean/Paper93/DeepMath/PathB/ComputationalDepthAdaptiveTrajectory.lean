import PallLean.Paper93.DeepMath.PathB.ComputationalDepthAverageBoundaryDebt
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderFoolingInstance

/-!
# Item 5: adaptive trajectories — decomposition changing over observer time

The previous results allowed the boundary to vary, but the debt was tracked against essentially one
decomposition.  An **adaptive trajectory** is the real escape route: at *each* observer step the observer may
use a **different decomposition** `decomp τ : X → Fin (2^{B_τ})` (a different cut / set of observables).  This
is exactly how EQUALITY dodges the prefix-cut fooling set — it streams under an *interleaved* decomposition.

The honest content of this file is to locate, precisely, where adaptivity does and does not help:

1. **Adaptivity does not beat the budget (proved).**  The total-action bound `|P| ≤ 2^{B_0} + ∑_τ 2^{B_τ}` is
   **agnostic to which decomposition is used at each step** — the accounting refers only to the per-step
   boundary capacity `2^{B_τ}`, not to *which* observables realise it.  So merely changing decomposition over
   time does not escape the bound.
2. **No single decomposition resolves a fooling set cheaply (proved).**  A decomposition that separates a
   fooling set of size `|P|` in one shot (`debtCount F view = 0`) needs `2^B ≥ |P|`.  So the escape "switch
   to a free perfect decomposition" is impossible at the single-view level.
3. **The load-bearing assumption is `Local` (locality), not adaptivity.**  What an adaptive observer *can* do
   is violate `Local`: a single step can un-merge *exponentially many* must-separate pairs (reading one bit
   splits all inputs differing in it).  EQUALITY's streaming escape lives **exactly here** — it is a *non-local*
   trajectory, not merely an adaptive one.  So the debt framework lower-bounds **locality-respecting** adaptive
   trajectories; `Local` is precisely the restriction separating the result from `P ≠ NP`.

## Proved (clean axioms, no `sorry`)

* `adaptive_total_action` — a `Local`, correct adaptive trajectory deciding a fooling-set-`P` instance
  satisfies `|P| ≤ 2^{B_0} + ∑_τ 2^{B_τ}`, regardless of how the decomposition changes over time.
* `single_decomposition_resolving_fooling_needs_full_boundary` — a single view with `debtCount F view = 0`
  on a fooling set `P` has `|P| ≤ m` (boundary `≥ log|P|`).
* `hypercube_adaptive_total_action` — concrete: a `Local`, correct adaptive observer of the `2^n` hypercube
  family needs total action `2^n ≤ 2^{B_0} + ∑_τ 2^{B_τ}` — adaptivity gives **no advantage** on a genuine
  fooling family.

## Honest scope — `Local` is the frontier, and the min over non-local trajectories is `P ≠ NP`

`Local` (`debt τ ≤ debt (τ+1) + 2^{B_τ}`: per-step debt reduction bounded by the boundary capacity) is an
**explicit hypothesis** and the genuine restriction.  It holds for step-local / bounded-progress observers; it
is **false** for a machine that resolves many distinctions in one step (the streaming escape).  So this is the
honest terminus of the adaptive analysis: adaptivity (decomposition change) is fully accounted for and does
not help, and the residual is whether SAT can be decided by a **non-local** low-action trajectory — equivalently
whether SAT's witness-distinguishability can be resolved faster than locality permits.  That min over all
(including non-local) trajectories is the all-decompositions quantifier = `P ≠ NP`, named not faked.  Nothing
here proves it; the contribution is to drag the load-bearing assumption (`Local`) fully into the light.
-/

namespace PallLean.Paper93.DeepMath.PathB.BoundaryDebt

open scoped BigOperators

variable {X : Type*} [DecidableEq X]

/-- An **adaptive trajectory**: at each observer step `t` the observer may use a *different* decomposition
`decomp t : X → Fin (2 ^ B t)` (a different cut / set of observables), with its own boundary `B t`.  `debt t`
is the cumulative merged must-separate debt at step `t`. -/
structure AdaptiveTrajectory (X : Type*) where
  /-- boundary (log-#states) at observer step `t`. -/
  B : ℕ → ℕ
  /-- the decomposition (observable map) used at step `t` — may change every step. -/
  decomp : (t : ℕ) → (X → Fin (2 ^ B t))
  /-- cumulative merged must-separate debt at step `t`. -/
  debt : ℕ → ℕ

/-- **Locality** (the load-bearing restriction): per observer step, the merged debt drops by at most the
boundary capacity `2^{B_t}` — the observer cannot un-merge more must-separate pairs than its boundary indexes.
True of step-local / bounded-progress observers; *false* for a step that resolves many distinctions at once. -/
def AdaptiveTrajectory.Local (τ : AdaptiveTrajectory X) : Prop :=
  ∀ t, τ.debt t ≤ τ.debt (t + 1) + 2 ^ τ.B t

/-- **Correct at time `T`**: all merged must-separate debt is cleared. -/
def AdaptiveTrajectory.CorrectAt (τ : AdaptiveTrajectory X) (T : ℕ) : Prop :=
  τ.debt T = 0

/-- **Adaptivity does not beat the budget (proved).**  A `Local`, correct adaptive trajectory whose initial
debt is the genuine merged debt under its initial decomposition, deciding a fooling-set-`P` instance,
satisfies `|P| ≤ 2^{B_0} + ∑_{τ<T} 2^{B_τ}` — *however the decomposition changes over observer time*.  The
accounting is agnostic to which observables are used; only the per-step boundary capacity enters. -/
theorem adaptive_total_action (P : Finset X) (F : Finset (X × X))
    (hfool : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → (x, y) ∈ F)
    (τ : AdaptiveTrajectory X) (T : ℕ)
    (hinit : τ.debt 0 = debtCount F (τ.decomp 0))
    (hloc : τ.Local) (hcorr : τ.CorrectAt T) :
    P.card ≤ 2 ^ τ.B 0 + ∑ t ∈ Finset.range T, 2 ^ τ.B t :=
  average_boundary_tradeoff P F hfool τ.B (τ.decomp 0) τ.debt T hinit hloc hcorr

/-- **No single decomposition resolves a fooling set cheaply (proved).**  If a view separates every
must-separate pair of a fooling set `P` in one shot (`debtCount F view = 0`), it needs `|P| ≤ m` boundary
states — boundary `≥ log₂|P|`.  So "switch to a free perfect low-boundary decomposition" is impossible. -/
theorem single_decomposition_resolving_fooling_needs_full_boundary {m : ℕ}
    (P : Finset X) (view : X → Fin m) (F : Finset (X × X))
    (hfool : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → (x, y) ∈ F)
    (hresolve : debtCount F view = 0) :
    P.card ≤ m := by
  have h := foolingSet_forces_debt P view F hfool
  rw [hresolve] at h
  omega

/-- **Concrete: adaptivity gives no advantage on the `2^n` hypercube family (proved).**  A `Local`, correct
adaptive observer that must distinguish all `2^n` hypercube points needs total action
`2^n ≤ 2^{B_0} + ∑_{τ<T} 2^{B_τ}`, no matter how it changes decomposition. -/
theorem hypercube_adaptive_total_action (n : ℕ)
    (τ : AdaptiveTrajectory (Fin n → Bool)) (T : ℕ)
    (hinit : τ.debt 0 = debtCount (hypercubeFool n) (τ.decomp 0))
    (hloc : τ.Local) (hcorr : τ.CorrectAt T) :
    2 ^ n ≤ 2 ^ τ.B 0 + ∑ t ∈ Finset.range T, 2 ^ τ.B t := by
  have h := adaptive_total_action (Finset.univ : Finset (Fin n → Bool)) (hypercubeFool n)
    (hypercube_fool n) τ T hinit hloc hcorr
  rwa [hypercube_card] at h

end PallLean.Paper93.DeepMath.PathB.BoundaryDebt

#print axioms PallLean.Paper93.DeepMath.PathB.BoundaryDebt.adaptive_total_action
#print axioms PallLean.Paper93.DeepMath.PathB.BoundaryDebt.single_decomposition_resolving_fooling_needs_full_boundary
#print axioms PallLean.Paper93.DeepMath.PathB.BoundaryDebt.hypercube_adaptive_total_action
