import PallLean.Paper93.DeepMath.PathB.Positroid.BoundedAffinePerm
import Mathlib.Tactic.Linarith

/-!
# Composition of bounded affine permutations modulo `n`

A *bounded affine permutation* of order `n` is a bijection `f : ℤ → ℤ` such that
`f(i + n) = f(i) + n` and `i ≤ f(i) ≤ i + n` for all `i ∈ ℤ`.

Pure composition of two such permutations preserves the `n`-shift property and
the lower bound `i ≤ f(g(i))`, but only yields the upper bound
`f(g(i)) ≤ i + 2n`.  Thus the composition `f ∘ g` is naturally a bounded
affine permutation of order `2n`, not `n`.

This file makes that fact explicit at the kernel level, exploring the
composition structure on bounded affine permutations modulo `n`.

This file is kernel-only: no `sorry`, no custom `axiom`, only the kernel
axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- Composition of two BAPs preserves the `n`-shift property. -/
theorem BAP_compose_shift_property {n : ℕ} (b₁ b₂ : BoundedAffinePerm n) (i : ℤ) :
    (b₁.toFun.trans b₂.toFun) (i + n) = (b₁.toFun.trans b₂.toFun) i + n := by
  show b₂.toFun (b₁.toFun (i + n)) = b₂.toFun (b₁.toFun i) + n
  rw [b₁.shift_property]
  exact b₂.shift_property _

/-- Composition of BAPs preserves the lower bound `i ≤ f(g(i))`. -/
theorem BAP_compose_lower_bound {n : ℕ} (b₁ b₂ : BoundedAffinePerm n) (i : ℤ) :
    i ≤ (b₁.toFun.trans b₂.toFun) i := by
  show i ≤ b₂.toFun (b₁.toFun i)
  have h1 : i ≤ b₁.toFun i := b₁.lower_bound i
  have h2 : b₁.toFun i ≤ b₂.toFun (b₁.toFun i) := b₂.lower_bound _
  linarith

/-- Composition of BAPs gives the upper bound `f(g(i)) ≤ i + 2n`. -/
theorem BAP_compose_upper_bound {n : ℕ} (b₁ b₂ : BoundedAffinePerm n) (i : ℤ) :
    (b₁.toFun.trans b₂.toFun) i ≤ i + 2 * n := by
  show b₂.toFun (b₁.toFun i) ≤ i + 2 * n
  have h1 : b₁.toFun i ≤ i + n := b₁.upper_bound i
  have h2 : b₂.toFun (b₁.toFun i) ≤ b₁.toFun i + n := b₂.upper_bound _
  linarith

end PallLean.Paper93.DeepMath.PathB.Positroid
