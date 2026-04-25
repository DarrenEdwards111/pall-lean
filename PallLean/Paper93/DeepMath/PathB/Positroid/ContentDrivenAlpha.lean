import PallLean.Paper93.DeepMath.PathB.Positroid.SATDeciderTableauToy
import PallLean.Paper93.DeepMath.PathB.Positroid.TableauTraceCoupling
import Mathlib.Algebra.Order.Group.Abs

/-!
# Content-driven coupling α from tableau entries

This file defines a **content-driven coupling** `contentDrivenAlpha` that
maps a `SATDeciderTableau m n` to a strictly positive real number whose
value depends on the tableau's actual entries via the
`tableauTraceCoupling` functional.

The simplest construction guaranteeing `α > 0` is
`1 + |tableauTraceCoupling T|`, which is always at least `1`.

For specific tableaus we record refined evaluations:
- `contentDrivenAlpha (zero m n) = 1`,
- `contentDrivenAlpha (allOnes m n) = 1 + m * n`,
and a distinguishability lemma when `m * n ≥ 1`.

Kernel-only: only `propext`, `Classical.choice`, `Quot.sound` are used.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- A **content-driven coupling** that depends on the tableau's entries. -/
noncomputable def contentDrivenAlpha {m n : ℕ} (T : SATDeciderTableau m n) : ℝ :=
  1 + |tableauTraceCoupling T|

/-- The content-driven coupling is at least 1 (hence strictly positive). -/
theorem contentDrivenAlpha_ge_one {m n : ℕ} (T : SATDeciderTableau m n) :
    1 ≤ contentDrivenAlpha T := by
  unfold contentDrivenAlpha
  have : 0 ≤ |tableauTraceCoupling T| := abs_nonneg _
  linarith

/-- The content-driven coupling is strictly positive. -/
theorem contentDrivenAlpha_pos {m n : ℕ} (T : SATDeciderTableau m n) :
    0 < contentDrivenAlpha T := by
  have h := contentDrivenAlpha_ge_one T
  linarith

/-- The content-driven coupling for the zero tableau equals 1. -/
theorem contentDrivenAlpha_zero (m n : ℕ) :
    contentDrivenAlpha (SATDeciderTableau.zero m n) = 1 := by
  unfold contentDrivenAlpha
  rw [tableauTraceCoupling_zero]
  simp

/-- The content-driven coupling for the all-ones tableau equals 1 + m*n. -/
theorem contentDrivenAlpha_allOnes (m n : ℕ) :
    contentDrivenAlpha (SATDeciderTableau.allOnes m n) = 1 + (m : ℝ) * n := by
  unfold contentDrivenAlpha
  rw [tableauTraceCoupling_allOnes]
  simp [abs_of_nonneg (by exact mul_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n) : (0:ℝ) ≤ m * n)]

/-- Content-driven alphas for zero vs all-ones differ when m*n ≥ 1. -/
theorem contentDrivenAlpha_distinguishes (m n : ℕ) (h : 1 ≤ m * n) :
    contentDrivenAlpha (SATDeciderTableau.zero m n) ≠
    contentDrivenAlpha (SATDeciderTableau.allOnes m n) := by
  rw [contentDrivenAlpha_zero, contentDrivenAlpha_allOnes]
  have : (1 : ℝ) ≤ (m : ℝ) * n := by exact_mod_cast h
  linarith

end PallLean.Paper93.DeepMath.PathB.Positroid
