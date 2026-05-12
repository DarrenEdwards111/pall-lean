import PallLean.Paper93.DeepMath.PathB.Positroid.CyclicShift
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.FinCases

/-!
# Iterated cyclic shift powers on `Fin n`

This file collects structural identities for iterated cyclic shifts on
`Fin n`, including involution behaviour at small `n`.

This file is kernel-only: no `sorry`, no custom `axiom`, no `True`
placeholders.  Only the kernel axioms `propext`, `Classical.choice`,
`Quot.sound` are permitted.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- The cyclic shift on Fin 1 is the identity (since (0+1) mod 1 = 0). -/
theorem cyclicShiftPos_n1_eq_id (hn : (0 : ℕ) < 1) :
    ∀ i : Fin 1, (cyclicShiftPos 1 hn) i = i :=
  cyclicShiftPos_n_one hn

/-- For n=2, applying cyclic shift twice gives the identity. -/
theorem cyclicShiftPos_n2_squared (hn : (0 : ℕ) < 2) (i : Fin 2) :
    (cyclicShiftPos 2 hn) ((cyclicShiftPos 2 hn) i) = i := by
  fin_cases i
  · -- i = 0; σ(0) = 1; σ(1) = 0
    apply Fin.ext
    show (((0 : ℕ) + 1) % 2 + 1) % 2 = 0
    omega
  · -- i = 1; σ(1) = 0; σ(0) = 1
    apply Fin.ext
    show (((1 : ℕ) + 1) % 2 + 1) % 2 = 1
    omega

/-- The cyclic shift inverse on Fin 2 equals the cyclic shift itself (involution). -/
theorem cyclicShiftPos_n2_self_inverse (hn : (0 : ℕ) < 2) (i : Fin 2) :
    (cyclicShiftPos 2 hn).symm i = (cyclicShiftPos 2 hn) i := by
  fin_cases i
  · apply Fin.ext
    show ((0 : ℕ) + (2 - 1)) % 2 = ((0 : ℕ) + 1) % 2
    omega
  · apply Fin.ext
    show ((1 : ℕ) + (2 - 1)) % 2 = ((1 : ℕ) + 1) % 2
    omega

end PallLean.Paper93.DeepMath.PathB.Positroid
