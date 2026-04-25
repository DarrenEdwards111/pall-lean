import PallLean.Paper93.DeepMath.PathB.Positroid.BoundedAffinePerm
import PallLean.Paper93.DeepMath.PathB.Positroid.BAPShiftPropertyGeneral
import PallLean.Paper93.DeepMath.PathB.Positroid.BAPCyclicCompositionAttempt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Further iteration / composition properties of bounded affine permutations

This file collects additional structural facts about iterations and
compositions of bounded affine permutations (BAPs).

Building on:
* `BAPShiftPropertyGeneral` — the iterated shift property
  `b.toFun (i + k * n) = b.toFun i + k * n`,
* `BAPCyclicCompositionAttempt` — composition preserves the shift
  property and gives the bounds `i ≤ (b₁ ∘ b₂)(i) ≤ i + 2n`,

we record:
1. iterated shift property under composition (k-fold lift),
2. composition at multiples of `n` (analog of `BAP_shift_at_zero`),
3. triple composition preserves the n-shift property,
4. triple composition lower bound `i ≤ b₃(b₂(b₁(i)))`,
5. triple composition upper bound `b₃(b₂(b₁(i))) ≤ i + 3n`.

This file is kernel-only: no `sorry`, no custom `axiom`, only the kernel
axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- Iterated shift property under composition: applying `b₂ ∘ b₁` to `i + k*n`
yields `(b₂ ∘ b₁)(i) + k*n`, for any natural number of shifts `k`. -/
theorem BAP_compose_shift_iter {n : ℕ} (b₁ b₂ : BoundedAffinePerm n)
    (i : ℤ) (k : ℕ) :
    b₂.toFun (b₁.toFun (i + k * n)) = b₂.toFun (b₁.toFun i) + k * n := by
  rw [BAP_shift_property_iter b₁ i k]
  rw [BAP_shift_property_iter b₂ (b₁.toFun i) k]

/-- Composition evaluated at a multiple of `n`: `b₂(b₁(k*n)) = b₂(b₁(0)) + k*n`. -/
theorem BAP_compose_shift_at_zero {n : ℕ} (b₁ b₂ : BoundedAffinePerm n) (k : ℕ) :
    b₂.toFun (b₁.toFun (k * n)) = b₂.toFun (b₁.toFun 0) + k * n := by
  have := BAP_compose_shift_iter b₁ b₂ 0 k
  rw [zero_add] at this
  exact this

/-- Triple composition preserves the n-shift property (one shift). -/
theorem BAP_triple_compose_shift_property {n : ℕ}
    (b₁ b₂ b₃ : BoundedAffinePerm n) (i : ℤ) :
    b₃.toFun (b₂.toFun (b₁.toFun (i + n))) =
      b₃.toFun (b₂.toFun (b₁.toFun i)) + n := by
  rw [b₁.shift_property, b₂.shift_property, b₃.shift_property]

/-- Triple composition lower bound: `i ≤ b₃(b₂(b₁(i)))`. -/
theorem BAP_triple_compose_lower_bound {n : ℕ}
    (b₁ b₂ b₃ : BoundedAffinePerm n) (i : ℤ) :
    i ≤ b₃.toFun (b₂.toFun (b₁.toFun i)) := by
  have h1 : i ≤ b₁.toFun i := b₁.lower_bound i
  have h2 : b₁.toFun i ≤ b₂.toFun (b₁.toFun i) := b₂.lower_bound _
  have h3 : b₂.toFun (b₁.toFun i) ≤ b₃.toFun (b₂.toFun (b₁.toFun i)) :=
    b₃.lower_bound _
  linarith

/-- Triple composition upper bound: `b₃(b₂(b₁(i))) ≤ i + 3n`. -/
theorem BAP_triple_compose_upper_bound {n : ℕ}
    (b₁ b₂ b₃ : BoundedAffinePerm n) (i : ℤ) :
    b₃.toFun (b₂.toFun (b₁.toFun i)) ≤ i + 3 * n := by
  have h1 : b₁.toFun i ≤ i + n := b₁.upper_bound i
  have h2 : b₂.toFun (b₁.toFun i) ≤ b₁.toFun i + n := b₂.upper_bound _
  have h3 : b₃.toFun (b₂.toFun (b₁.toFun i)) ≤ b₂.toFun (b₁.toFun i) + n :=
    b₃.upper_bound _
  linarith

end PallLean.Paper93.DeepMath.PathB.Positroid
