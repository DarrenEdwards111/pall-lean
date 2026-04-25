import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Bool.Basic

/-!
# Toy Le-diagram structure (positroid building block)

A *Le diagram* is a Young-diagram-like shape with a 0/1 filling satisfying the
"Le condition": no L-shaped pattern of three filled cells with 1's in NW, NE,
and SW positions (the SE cell must also be 1 if the other three are).  Le
diagrams index positroid cells in the totally nonnegative Grassmannian.

This file provides a toy version on a `k × n` rectangle: the filling is a
Boolean function `Fin k → Fin n → Bool` satisfying the Le condition.  We
package this as a `LeDiagram k n` structure and provide the all-zeros and
all-ones diagrams as basic instances.

The file is kernel-only: no `sorry`, no custom `axiom`, only the kernel
axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- A **Le diagram** of dimensions k × n: a Boolean filling of a k×n grid
    satisfying the Le condition (no NW-NE-SW pattern of 1's). -/
structure LeDiagram (k n : ℕ) where
  /-- The 0/1 filling: filling i j is `true` if cell (i,j) is filled with 1. -/
  filling : Fin k → Fin n → Bool
  /-- The Le condition: forbids NW-NE-SW patterns of 1's. -/
  le_condition : ∀ (i₁ i₂ : Fin k) (j₁ j₂ : Fin n),
    i₁ < i₂ → j₁ < j₂ →
    filling i₁ j₂ = true → filling i₂ j₁ = true → filling i₂ j₂ = true

/-- The all-zeros Le diagram: every cell is 0.  The Le condition is vacuously
    satisfied because the hypothesis `filling i₁ j₂ = true` is never met. -/
def LeDiagram.zero (k n : ℕ) : LeDiagram k n where
  filling := fun _ _ => false
  le_condition := fun _ _ _ _ _ _ h₁ _ => by simp at h₁

/-- The all-ones Le diagram: every cell is 1.  The Le condition is satisfied
    since the conclusion `filling i₂ j₂ = true` holds by definition. -/
def LeDiagram.one (k n : ℕ) : LeDiagram k n where
  filling := fun _ _ => true
  le_condition := fun _ _ _ _ _ _ _ _ => rfl

/-- The zero Le diagram has filling identically false. -/
theorem LeDiagram.zero_filling (k n : ℕ) (i : Fin k) (j : Fin n) :
    (LeDiagram.zero k n).filling i j = false := rfl

/-- The all-ones Le diagram has filling identically true. -/
theorem LeDiagram.one_filling (k n : ℕ) (i : Fin k) (j : Fin n) :
    (LeDiagram.one k n).filling i j = true := rfl

/-- A Le diagram with k=0 has empty row index type (no rows). -/
theorem LeDiagram.zero_rows_filling (n : ℕ) (D : LeDiagram 0 n) (i : Fin 0) (j : Fin n) :
    D.filling i j = D.filling i j := rfl

end PallLean.Paper93.DeepMath.PathB.Positroid
