import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Existence of a positive `α` with `α (α + n)^(n-1) = 1` via the IVT (general `n`)

This file generalises `N3IVTExistence`, `N4IVTExistence`, and
`N5IVTExistence` to arbitrary `n ≥ 2`. The §28.3 gauge condition
`det(compiledGadget α n) = 1` reduces to finding a positive real root
of the polynomial

```
α (α + n)^(n-1) = 1.
```

Mathlib does not provide a closed form for this root, but its existence
in `(0, 1]` is a direct consequence of the **Intermediate Value
Theorem**: the function `f(α) = α (α + n)^(n-1)` is continuous on `ℝ`,
with `f(0) = 0 < 1` and `f(1) = (1+n)^(n-1) ≥ 3` for `n ≥ 2`.

This file provides:

* `alpha_alpha_plus_n_pow_continuous`: continuity of `f`.
* `alpha_alpha_plus_n_pow_at_zero`: `f(0) = 0`.
* `alpha_alpha_plus_n_pow_at_one_ge_one`: `1 ≤ (1+n)·(1+n)^(n-2)` for `n ≥ 2`.
* `exists_alpha_general_n_det_one`: existence of `α ∈ (0, 1]` with
  `α (α + n)^(n-1) = 1`, via `intermediate_value_Icc`.

All results are kernel-only (axioms: `propext`, `Classical.choice`,
`Quot.sound`).

Namespace: `PallLean.Paper93.DeepMath.PathB.Positroid`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- The function `f(α) = α (α + n)^(n-1)` is continuous on `ℝ`. -/
theorem alpha_alpha_plus_n_pow_continuous (n : ℕ) :
    Continuous (fun α : ℝ => α * (α + n)^(n - 1)) := by
  apply Continuous.mul
  · exact continuous_id
  · exact (continuous_id.add continuous_const).pow _

/-- `f(0) = 0` for any `n ≥ 1`. -/
theorem alpha_alpha_plus_n_pow_at_zero (n : ℕ) (hn : 1 ≤ n) :
    (0 : ℝ) * (0 + n)^(n - 1) = 0 := by ring

/-- For `n ≥ 2`, `(1+n)·(1+n)^(n-2) ≥ 1`.

This is the key positivity step: rewriting `(1+n)^(n-1)` as
`(1+n) · (1+n)^(n-2)` and using `1 ≤ 1+n` plus `1 ≤ (1+n)^(n-2)`. -/
theorem alpha_alpha_plus_n_pow_at_one_ge_one (n : ℕ) (hn : 2 ≤ n) :
    (1 : ℝ) ≤ (1 + (n : ℝ)) * ((1 + (n : ℝ))^(n - 2)) := by
  have h1 : (1 : ℝ) ≤ 1 + (n : ℝ) := by
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have h2 : (1 : ℝ) ≤ (1 + (n : ℝ))^(n - 2) := one_le_pow₀ h1
  nlinarith [h1, h2]

/-- **Existence of `α ∈ (0, 1]` with `α (α + n)^(n-1) = 1`** for `n ≥ 2`,
via the Intermediate Value Theorem.

Proof sketch: `f(α) = α (α + n)^(n-1)` is continuous on `ℝ` (hence on
`[0, 1]`); `f(0) = 0 ≤ 1` and `f(1) = (1+n)^(n-1) ≥ 1` for `n ≥ 2`.
The IVT (`intermediate_value_Icc`) gives `α ∈ [0, 1]` with `f(α) = 1`.
Since `f(0) = 0 ≠ 1`, the witness `α` is strictly positive.

Note: this is the **existence form** of the result; no closed-form
expression for `α` is asserted (none is currently available in
Mathlib for this polynomial in general `n`). -/
theorem exists_alpha_general_n_det_one (n : ℕ) (hn : 2 ≤ n) :
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ α * (α + n)^(n-1) = 1 := by
  have h_cont : Continuous (fun α : ℝ => α * (α + n)^(n - 1)) :=
    alpha_alpha_plus_n_pow_continuous n
  have h_f0 : (fun α : ℝ => α * (α + n)^(n - 1)) 0 = 0 := by simp
  have h_f1 : (fun α : ℝ => α * (α + n)^(n - 1)) 1 = (1 + (n : ℝ))^(n-1) := by
    simp
  -- (1+n)^(n-1) ≥ 1 for n ≥ 2
  have h_ge_one : (1 : ℝ) ≤ (1 + (n : ℝ))^(n - 1) := by
    have hone_le : (1 : ℝ) ≤ 1 + (n : ℝ) := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    exact one_le_pow₀ hone_le
  have h_ivt := intermediate_value_Icc
    (by norm_num : (0:ℝ) ≤ 1) h_cont.continuousOn
  have h_in : (1 : ℝ) ∈ Set.Icc ((fun α : ℝ => α * (α + n)^(n - 1)) 0)
                                  ((fun α : ℝ => α * (α + n)^(n - 1)) 1) := by
    rw [h_f0, h_f1]
    exact ⟨by norm_num, h_ge_one⟩
  obtain ⟨α, hα_mem, hα_eq⟩ := h_ivt h_in
  refine ⟨α, ?_, hα_mem.2, hα_eq⟩
  by_contra h_neg
  push_neg at h_neg
  have h_eq_0 : α = 0 := le_antisymm h_neg hα_mem.1
  rw [h_eq_0] at hα_eq
  simp at hα_eq

end PallLean.Paper93.DeepMath.PathB.Positroid
