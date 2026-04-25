import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Existence of a positive `α` with `α (α + 7)⁶ = 1` via the IVT

The `n = 7` analogue of the §28.3 gauge condition: solving
`det = 1` for `compiledGadget α 7` reduces to finding a positive real
root of the septic

```
α (α + 7)⁶ = 1.
```

Mathlib does not currently provide a closed-form rational/algebraic
expression for this root, but its existence in the open interval
`(0, 1)` is a direct consequence of the **Intermediate Value Theorem**:
the function `f(α) = α (α + 7)⁶` is continuous on `ℝ`, with
`f(0) = 0 < 1` and `f(1) = 1 · 8⁶ = 262144 > 1`, so by IVT there is
`α ∈ (0, 1)` with `f(α) = 1`.

This file provides:

* `alpha_alpha_plus_7_sextic_continuous`: continuity of `f`.
* `alpha_alpha_plus_7_sextic_at_zero`: `f(0) = 0`.
* `alpha_alpha_plus_7_sextic_at_one`: `f(1) = 262144`.
* `exists_alpha_n7_det_one`: existence of `α ∈ (0, 1)` with
  `α (α + 7)⁶ = 1`, via `intermediate_value_Icc`.

All results are kernel-only (axioms: `propext`, `Classical.choice`,
`Quot.sound`).

Namespace: `PallLean.Paper93.DeepMath.PathB.Positroid`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- The function `f(α) = α (α + 7)⁶` is continuous on `ℝ`. -/
theorem alpha_alpha_plus_7_sextic_continuous :
    Continuous (fun α : ℝ => α * (α + 7)^6) := by
  apply Continuous.mul
  · exact continuous_id
  · exact (continuous_id.add continuous_const).pow 6

/-- `f(0) = 0`. -/
theorem alpha_alpha_plus_7_sextic_at_zero :
    (0 : ℝ) * (0 + 7)^6 = 0 := by ring

/-- `f(1) = 262144`. -/
theorem alpha_alpha_plus_7_sextic_at_one :
    (1 : ℝ) * (1 + 7)^6 = 262144 := by norm_num

/-- **Existence of `α ∈ (0, 1)` with `α (α + 7)⁶ = 1`**, via the
Intermediate Value Theorem.

Proof sketch: `f(α) = α (α + 7)⁶` is continuous on `ℝ` (hence on
`[0, 1]`); `f(0) = 0 < 1 < 262144 = f(1)`. The IVT
(`intermediate_value_Icc`) gives `α ∈ [0, 1]` with `f(α) = 1`. Since
`f(0) = 0 ≠ 1` and `f(1) = 262144 ≠ 1`, the witness `α` actually lies in
the open interval `(0, 1)`.

Note: this is the **existence form** of the result; no closed-form
expression for `α` is asserted (none is currently available in
Mathlib for this septic). -/
theorem exists_alpha_n7_det_one :
    ∃ α : ℝ, 0 < α ∧ α < 1 ∧ α * (α + 7)^6 = 1 := by
  have h_cont : Continuous (fun α : ℝ => α * (α + 7)^6) :=
    alpha_alpha_plus_7_sextic_continuous
  have h0 : (fun α : ℝ => α * (α + 7)^6) 0 = 0 := by simp
  have h1 : (fun α : ℝ => α * (α + 7)^6) 1 = 262144 := by norm_num
  have h_ivt := intermediate_value_Icc
    (by norm_num : (0:ℝ) ≤ 1) h_cont.continuousOn
  have h_in : (1 : ℝ) ∈ Set.Icc ((fun α : ℝ => α * (α + 7)^6) 0)
                                ((fun α : ℝ => α * (α + 7)^6) 1) := by
    rw [h0, h1]
    exact ⟨by norm_num, by norm_num⟩
  obtain ⟨α, hα_mem, hα_eq⟩ := h_ivt h_in
  refine ⟨α, ?_, ?_, hα_eq⟩
  · -- 0 < α
    by_contra h_neg
    push_neg at h_neg
    have h_eq_0 : α = 0 := le_antisymm h_neg hα_mem.1
    rw [h_eq_0] at hα_eq
    norm_num at hα_eq
  · -- α < 1
    by_contra h_neg
    push_neg at h_neg
    have h_eq_1 : α = 1 := le_antisymm hα_mem.2 h_neg
    rw [h_eq_1] at hα_eq
    norm_num at hα_eq

end PallLean.Paper93.DeepMath.PathB.Positroid
