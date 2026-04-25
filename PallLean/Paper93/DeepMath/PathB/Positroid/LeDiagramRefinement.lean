import PallLean.Paper93.DeepMath.PathB.Positroid.LeDiagramDef
import Mathlib.Data.Bool.Basic

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- A diagonal Le diagram (filling i j = (i = j)) for square cases satisfies the Le condition. -/
def LeDiagram.diagonal (n : ℕ) [DecidableEq (Fin n)] : LeDiagram n n where
  filling := fun i j => i = j
  le_condition := by
    intros i₁ i₂ j₁ j₂ hi hj h1 h2
    -- h1 : (i₁ = j₂) = true, so i₁ = j₂
    -- h2 : (i₂ = j₁) = true, so i₂ = j₁
    -- We need (i₂ = j₂) = true
    have hi1j2 : i₁ = j₂ := by
      simpa using h1
    have hi2j1 : i₂ = j₁ := by
      simpa using h2
    -- From hi : i₁ < i₂ and hi1j2 + hi2j1: i₁ = j₂ and i₂ = j₁
    -- And hj : j₁ < j₂. So i₂ = j₁ < j₂ = i₁ < i₂. Contradiction.
    rw [hi1j2] at hi
    rw [hi2j1] at hi
    exact absurd hi (not_lt.mpr (le_of_lt hj))

/-- The all-zeros Le diagram has zero filled cells. -/
theorem LeDiagram.zero_no_filled_cells (k n : ℕ) (i : Fin k) (j : Fin n) :
    (LeDiagram.zero k n).filling i j = false := rfl

/-- The all-ones Le diagram has all cells filled. -/
theorem LeDiagram.one_all_filled (k n : ℕ) (i : Fin k) (j : Fin n) :
    (LeDiagram.one k n).filling i j = true := rfl

/-- The all-ones Le diagram is total: every cell is filled. -/
theorem LeDiagram.one_universal (k n : ℕ) :
    ∀ (i : Fin k) (j : Fin n), (LeDiagram.one k n).filling i j = true :=
  LeDiagram.one_all_filled k n

end PallLean.Paper93.DeepMath.PathB.Positroid
