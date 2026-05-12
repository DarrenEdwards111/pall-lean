import PallLean.Paper93.DeepMath.PathB.Positroid.CyclicShift
import Mathlib.Tactic.FinCases

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- σ at 0 on Fin 4 is 1. -/
theorem cyclicShiftPos_n4_zero (hn : (0 : ℕ) < 4) :
    (cyclicShiftPos 4 hn) ⟨0, hn⟩ = ⟨1, by omega⟩ := by
  apply Fin.ext
  show ((0 : ℕ) + 1) % 4 = 1
  omega

/-- σ at 3 on Fin 4 is 0 (cyclic). -/
theorem cyclicShiftPos_n4_three (hn : (0 : ℕ) < 4) :
    (cyclicShiftPos 4 hn) ⟨3, by omega⟩ = ⟨0, hn⟩ := by
  apply Fin.ext
  show ((3 : ℕ) + 1) % 4 = 0
  omega

/-- σ⁴ = id on Fin 4. -/
theorem cyclicShiftPos_n4_fourth (hn : (0 : ℕ) < 4) (i : Fin 4) :
    (cyclicShiftPos 4 hn) ((cyclicShiftPos 4 hn) ((cyclicShiftPos 4 hn) ((cyclicShiftPos 4 hn) i))) = i := by
  fin_cases i
  · apply Fin.ext; show (((((0:ℕ) + 1) % 4 + 1) % 4 + 1) % 4 + 1) % 4 = 0; omega
  · apply Fin.ext; show (((((1:ℕ) + 1) % 4 + 1) % 4 + 1) % 4 + 1) % 4 = 1; omega
  · apply Fin.ext; show (((((2:ℕ) + 1) % 4 + 1) % 4 + 1) % 4 + 1) % 4 = 2; omega
  · apply Fin.ext; show (((((3:ℕ) + 1) % 4 + 1) % 4 + 1) % 4 + 1) % 4 = 3; omega

end PallLean.Paper93.DeepMath.PathB.Positroid
