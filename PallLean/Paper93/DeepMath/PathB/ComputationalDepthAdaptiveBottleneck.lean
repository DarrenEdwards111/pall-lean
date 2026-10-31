import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderNoHiding

/-!
# Step 4: the adaptive bottleneck — a cheap trajectory must contain a cheap step (proved)

The expander no-hiding lemma (`surjective_residual_forces_debt`) forces super-log debt *at a step whose
boundary is small*.  An adaptive observer with low **total** action need not have small boundary at every step
— but it must have a small boundary at **some** step.  This file proves that bottleneck extraction (a clean
pigeonhole) and uses it to locate the open core precisely.

## Proved (clean axioms, no `sorry`)

* `adaptive_bottleneck_exists` — **the pigeonhole**: if the total per-step action `∑_{τ<T} cost τ ≤ A`, then
  there is a step `τ` with `T · cost τ ≤ A` (its action is at most the average).  The minimum step is cheap.
* `cheap_trajectory_has_residual_debt_bottleneck` — **the reduction (step 4)**: for an adaptive trajectory
  with total boundary action `∑_{τ<T} 2^{B_τ} ≤ A` whose residual map is non-collapsing at every step
  (`hnoncollapse`, surjective onto `Fin (2^r)`), there is a bottleneck step `τ` carrying residual debt
  `2^r − A ≤ debtCount (residualFooling (residual τ)) (view τ)`.  For `r = Ω(n)` and `A` sub-`2^{Ω(n)}` (e.g.
  poly) this is super-logarithmic.

## Honest scope — exactly which quantifier is left

Combining with `expander_residual_forces_debt` (which proves `hnoncollapse` for the **read-set** decomposition),
this says: *a cheap adaptive observer of expander Tseitin that stays within the read-set decomposition class
has a bottleneck step with super-log residual debt.*  The single remaining open input is `hnoncollapse` **for
the observer's own (possibly non-read-set) decompositions** — i.e. *residual non-collapse under every cheap
adaptive decomposition*.  That is the min-over-decompositions quantifier = `P ≠ NP` (HAL's step 5: a cheap
decomposition cannot align with all expander constraints to collapse residuals).  This file proves everything
*around* that one property: the bottleneck always exists, and non-collapse at the bottleneck mechanically
yields the debt.  The breakthrough lemma (non-collapse under adaptive coordinate choices) is named, not faked.
-/

namespace PallLean.Paper93.DeepMath.PathB.BoundaryDebt

open scoped BigOperators

/-- **Bottleneck pigeonhole (proved).**  If the total per-step cost over `T > 0` steps is at most `A`, some
step's cost is at most the average: `∃ τ < T, T · cost τ ≤ A`.  (Take the minimising step; `T` copies of its
cost underestimate the sum.) -/
theorem adaptive_bottleneck_exists (cost : ℕ → ℕ) (T A : ℕ) (hT : 0 < T)
    (hsum : ∑ τ ∈ Finset.range T, cost τ ≤ A) :
    ∃ τ, τ < T ∧ T * cost τ ≤ A := by
  obtain ⟨τ0, hτ0mem, hτ0min⟩ :=
    Finset.exists_min_image (Finset.range T) cost ⟨0, Finset.mem_range.mpr hT⟩
  refine ⟨τ0, Finset.mem_range.mp hτ0mem, ?_⟩
  calc T * cost τ0
      = ∑ _τ ∈ Finset.range T, cost τ0 := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    _ ≤ ∑ τ ∈ Finset.range T, cost τ := Finset.sum_le_sum (fun τ hτ => hτ0min τ hτ)
    _ ≤ A := hsum

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- **Step 4 reduction (proved).**  Consider an adaptive trajectory over `T > 0` steps with per-step boundary
`B τ`, view `view τ : C → Fin (2 ^ B τ)`, and residual map `residual τ : C → Fin (2 ^ r)`.  If the total
boundary action is at most `A` (`∑_{τ<T} 2^{B_τ} ≤ A`) and the residual is **non-collapsing** at every step
(surjective), then some bottleneck step `τ` carries residual debt `2^r − A ≤ debtCount (residualFooling
(residual τ)) (view τ)`.

The non-collapse hypothesis is the only open input; everything else is forced. -/
theorem cheap_trajectory_has_residual_debt_bottleneck {r : ℕ}
    (B : ℕ → ℕ) (view : (τ : ℕ) → C → Fin (2 ^ B τ)) (residual : ℕ → C → Fin (2 ^ r))
    (T A : ℕ) (hT : 0 < T)
    (hsum : ∑ τ ∈ Finset.range T, 2 ^ B τ ≤ A)
    (hnoncollapse : ∀ τ, Function.Surjective (residual τ)) :
    ∃ τ, τ < T ∧ 2 ^ r - A ≤ debtCount (residualFooling (residual τ)) (view τ) := by
  obtain ⟨τ, hτT, hτcheap⟩ := adaptive_bottleneck_exists (fun τ => 2 ^ B τ) T A hT hsum
  -- the bottleneck boundary is below the total budget
  have hBA : 2 ^ B τ ≤ A := le_trans (Nat.le_mul_of_pos_left _ hT) hτcheap
  -- expander no-hiding at the bottleneck step
  have hdebt := surjective_residual_forces_debt (residual τ) (hnoncollapse τ) (view τ)
  exact ⟨τ, hτT, by omega⟩

end PallLean.Paper93.DeepMath.PathB.BoundaryDebt

#print axioms PallLean.Paper93.DeepMath.PathB.BoundaryDebt.adaptive_bottleneck_exists
#print axioms PallLean.Paper93.DeepMath.PathB.BoundaryDebt.cheap_trajectory_has_residual_debt_bottleneck
