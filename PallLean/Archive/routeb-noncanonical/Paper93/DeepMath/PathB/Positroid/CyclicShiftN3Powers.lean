import PallLean.Paper93.DeepMath.PathB.Positroid.CyclicShift
import Mathlib.Tactic.FinCases

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- The cyclic shift on Fin 3 applied 3 times is the identity. -/
theorem cyclicShiftPos_n3_cubed (hn : (0 : ℕ) < 3) (i : Fin 3) :
    (cyclicShiftPos 3 hn) ((cyclicShiftPos 3 hn) ((cyclicShiftPos 3 hn) i)) = i := by
  fin_cases i
  · apply Fin.ext
    show ((((0 : ℕ) + 1) % 3 + 1) % 3 + 1) % 3 = 0
    omega
  · apply Fin.ext
    show ((((1 : ℕ) + 1) % 3 + 1) % 3 + 1) % 3 = 1
    omega
  · apply Fin.ext
    show ((((2 : ℕ) + 1) % 3 + 1) % 3 + 1) % 3 = 2
    omega

/-- σ at 0 is 1 on Fin 3. -/
theorem cyclicShiftPos_n3_zero (hn : (0 : ℕ) < 3) :
    (cyclicShiftPos 3 hn) ⟨0, hn⟩ = ⟨1, by omega⟩ := by
  apply Fin.ext
  show ((0 : ℕ) + 1) % 3 = 1
  omega

end PallLean.Paper93.DeepMath.PathB.Positroid
