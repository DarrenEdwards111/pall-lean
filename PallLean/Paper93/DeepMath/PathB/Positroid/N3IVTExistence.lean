import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Existence of a positive `α` with `α (α + 3)² = 1` via the IVT

The §28.3 `compiledGadget α 3` has determinant `α (α + 3)²`. Solving
the gauge condition `det = 1` therefore reduces to finding a positive
real root of the cubic

```
α (α + 3)² = 1.
```

Mathlib does not currently provide a closed-form rational/algebraic
expression for this root, but its existence in the open interval
`(0, 1)` is a direct consequence of the **Intermediate Value Theorem**:
the function `f(α) = α (α + 3)²` is continuous on `ℝ`, with
`f(0) = 0 < 1` and `f(1) = 1 · 16 = 16 > 1`, so by IVT there is
`α ∈ (0, 1)` with `f(α) = 1`.

This file provides:

* `alpha_alpha_plus_3_sq_continuous`: continuity of `f`.
* `alpha_alpha_plus_3_sq_at_zero`: `f(0) = 0`.
* `alpha_alpha_plus_3_sq_at_one`: `f(1) = 16`.
* `alpha_alpha_plus_3_sq_at_one_lt_one`: combined boundary data
  `0 < 1`, `f(1) = 16`, `16 > 1`.
* `exists_alpha_n3_det_one`: existence of `α ∈ (0, 1)` with
  `α (α + 3)² = 1`, via `intermediate_value_Icc`.

All results are kernel-only (axioms: `propext`, `Classical.choice`,
`Quot.sound`).

Namespace: `PallLean.Paper93.DeepMath.PathB.Positroid`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- The function `f(α) = α (α + 3)²` is continuous on `ℝ`. -/
theorem alpha_alpha_plus_3_sq_continuous :
    Continuous (fun α : ℝ => α * (α + 3)^2) := by
  apply Continuous.mul
  · exact continuous_id
  · exact (continuous_id.add continuous_const).pow 2

/-- `f(0) = 0`. -/
theorem alpha_alpha_plus_3_sq_at_zero :
    (0 : ℝ) * (0 + 3)^2 = 0 := by ring

/-- `f(1) = 16`. -/
theorem alpha_alpha_plus_3_sq_at_one :
    (1 : ℝ) * (1 + 3)^2 = 16 := by norm_num

/-- Boundary data: `0 < 1`, `f(1) = 16`, and `16 > 1`. This packages
the comparisons used in the IVT step. -/
theorem alpha_alpha_plus_3_sq_at_one_lt_one :
    (0 : ℝ) < 1 ∧ (1 : ℝ) * (1 + 3)^2 = 16 ∧ (16 : ℝ) > 1 := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · norm_num

/-- **Existence of `α ∈ (0, 1)` with `α (α + 3)² = 1`**, via the
Intermediate Value Theorem.

Proof sketch: `f(α) = α (α + 3)²` is continuous on `ℝ` (hence on
`[0, 1]`); `f(0) = 0 < 1 < 16 = f(1)`. The IVT
(`intermediate_value_Icc`) gives `α ∈ [0, 1]` with `f(α) = 1`. Since
`f(0) = 0 ≠ 1` and `f(1) = 16 ≠ 1`, the witness `α` actually lies in
the open interval `(0, 1)`.

Note: this is the **existence form** of the result; no closed-form
expression for `α` is asserted (none is currently available in
Mathlib for this cubic). -/
theorem exists_alpha_n3_det_one :
    ∃ α : ℝ, 0 < α ∧ α < 1 ∧ α * (α + 3)^2 = 1 := by
  -- f(0) = 0 < 1 and f(1) = 16 > 1, so by IVT there's α ∈ (0, 1) with f(α) = 1.
  have h_cont : Continuous (fun α : ℝ => α * (α + 3)^2) :=
    alpha_alpha_plus_3_sq_continuous
  have h0 : (fun α : ℝ => α * (α + 3)^2) 0 = 0 := by simp
  have h1 : (fun α : ℝ => α * (α + 3)^2) 1 = 16 := by norm_num
  -- Apply IVT on [0, 1]
  have h_ivt := intermediate_value_Icc
    (by norm_num : (0:ℝ) ≤ 1) h_cont.continuousOn
  -- 1 ∈ Set.Icc (f 0) (f 1) = Set.Icc 0 16
  have h_in : (1 : ℝ) ∈ Set.Icc ((fun α : ℝ => α * (α + 3)^2) 0)
                                ((fun α : ℝ => α * (α + 3)^2) 1) := by
    rw [h0, h1]
    constructor <;> norm_num
  obtain ⟨α, hα_mem, hα_eq⟩ := h_ivt h_in
  -- Need to refine α to be strictly in (0, 1) — the IVT gives [0,1] but we know
  -- f(0) = 0 ≠ 1 and f(1) = 16 ≠ 1, so α ∈ (0, 1).
  refine ⟨α, ?_, ?_, hα_eq⟩
  · -- 0 < α: since f(α) = 1 ≠ 0 = f(0), α ≠ 0
    by_contra h_neg
    push_neg at h_neg
    have h_eq_0 : α = 0 := le_antisymm h_neg hα_mem.1
    rw [h_eq_0] at hα_eq
    norm_num at hα_eq
  · -- α < 1: since f(α) = 1 ≠ 16 = f(1), α ≠ 1
    by_contra h_neg
    push_neg at h_neg
    have h_eq_1 : α = 1 := le_antisymm hα_mem.2 h_neg
    rw [h_eq_1] at hα_eq
    norm_num at hα_eq

end PallLean.Paper93.DeepMath.PathB.Positroid
