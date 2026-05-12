import PallLean.Paper93.DeepMath.PathB.Positroid.CyclicShift
import Mathlib.Tactic.FinCases

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-! # Cyclic shift powers at `n = 5` and `n = 6`

This file extends the pattern of `CyclicShiftN4Powers` to the cases
`n = 5` and `n = 6`.  The key fact is that the cyclic shift `σ` on
`Fin n` satisfies `σ^n = id`, established here by case analysis on the
finite domain.

This file is kernel-only: no `sorry`, no custom `axiom`, no `True`
placeholders.  Only the kernel axioms `propext`, `Classical.choice`,
`Quot.sound` are permitted.
-/

/-- σ at 0 on Fin 5 is 1. -/
theorem cyclicShiftPos_n5_zero (hn : (0 : ℕ) < 5) :
    (cyclicShiftPos 5 hn) ⟨0, hn⟩ = ⟨1, by omega⟩ := by
  apply Fin.ext
  show ((0 : ℕ) + 1) % 5 = 1
  omega

/-- σ at 4 on Fin 5 is 0 (cyclic). -/
theorem cyclicShiftPos_n5_four (hn : (0 : ℕ) < 5) :
    (cyclicShiftPos 5 hn) ⟨4, by omega⟩ = ⟨0, hn⟩ := by
  apply Fin.ext
  show ((4 : ℕ) + 1) % 5 = 0
  omega

/-- σ⁵ = id on Fin 5. -/
theorem cyclicShiftPos_n5_fifth (hn : (0 : ℕ) < 5) (i : Fin 5) :
    (cyclicShiftPos 5 hn) ((cyclicShiftPos 5 hn) ((cyclicShiftPos 5 hn)
      ((cyclicShiftPos 5 hn) ((cyclicShiftPos 5 hn) i)))) = i := by
  fin_cases i
  · apply Fin.ext
    show ((((((0 : ℕ) + 1) % 5 + 1) % 5 + 1) % 5 + 1) % 5 + 1) % 5 = 0
    omega
  · apply Fin.ext
    show ((((((1 : ℕ) + 1) % 5 + 1) % 5 + 1) % 5 + 1) % 5 + 1) % 5 = 1
    omega
  · apply Fin.ext
    show ((((((2 : ℕ) + 1) % 5 + 1) % 5 + 1) % 5 + 1) % 5 + 1) % 5 = 2
    omega
  · apply Fin.ext
    show ((((((3 : ℕ) + 1) % 5 + 1) % 5 + 1) % 5 + 1) % 5 + 1) % 5 = 3
    omega
  · apply Fin.ext
    show ((((((4 : ℕ) + 1) % 5 + 1) % 5 + 1) % 5 + 1) % 5 + 1) % 5 = 4
    omega

/-- σ at 0 on Fin 6 is 1. -/
theorem cyclicShiftPos_n6_zero (hn : (0 : ℕ) < 6) :
    (cyclicShiftPos 6 hn) ⟨0, hn⟩ = ⟨1, by omega⟩ := by
  apply Fin.ext
  show ((0 : ℕ) + 1) % 6 = 1
  omega

/-- σ at 5 on Fin 6 is 0 (cyclic). -/
theorem cyclicShiftPos_n6_five (hn : (0 : ℕ) < 6) :
    (cyclicShiftPos 6 hn) ⟨5, by omega⟩ = ⟨0, hn⟩ := by
  apply Fin.ext
  show ((5 : ℕ) + 1) % 6 = 0
  omega

/-- σ⁶ = id on Fin 6. -/
theorem cyclicShiftPos_n6_sixth (hn : (0 : ℕ) < 6) (i : Fin 6) :
    (cyclicShiftPos 6 hn) ((cyclicShiftPos 6 hn) ((cyclicShiftPos 6 hn)
      ((cyclicShiftPos 6 hn) ((cyclicShiftPos 6 hn)
        ((cyclicShiftPos 6 hn) i))))) = i := by
  fin_cases i
  · apply Fin.ext
    show (((((((0 : ℕ) + 1) % 6 + 1) % 6 + 1) % 6 + 1) % 6 + 1) % 6 + 1) % 6 = 0
    omega
  · apply Fin.ext
    show (((((((1 : ℕ) + 1) % 6 + 1) % 6 + 1) % 6 + 1) % 6 + 1) % 6 + 1) % 6 = 1
    omega
  · apply Fin.ext
    show (((((((2 : ℕ) + 1) % 6 + 1) % 6 + 1) % 6 + 1) % 6 + 1) % 6 + 1) % 6 = 2
    omega
  · apply Fin.ext
    show (((((((3 : ℕ) + 1) % 6 + 1) % 6 + 1) % 6 + 1) % 6 + 1) % 6 + 1) % 6 = 3
    omega
  · apply Fin.ext
    show (((((((4 : ℕ) + 1) % 6 + 1) % 6 + 1) % 6 + 1) % 6 + 1) % 6 + 1) % 6 = 4
    omega
  · apply Fin.ext
    show (((((((5 : ℕ) + 1) % 6 + 1) % 6 + 1) % 6 + 1) % 6 + 1) % 6 + 1) % 6 = 5
    omega

end PallLean.Paper93.DeepMath.PathB.Positroid
