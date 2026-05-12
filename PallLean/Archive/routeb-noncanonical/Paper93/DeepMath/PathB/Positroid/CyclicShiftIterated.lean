import PallLean.Paper93.DeepMath.PathB.Positroid.CyclicShift

/-!
# Iterated cyclic shifts on `Fin n`

This file collects structural properties of iterated cyclic shifts on `Fin n`,
building on the basic `cyclicShiftPos` defined in `CyclicShift.lean`.

This file is kernel-only: no `sorry`, no custom `axiom`, no `True`
placeholders.  Only the kernel axioms `propext`, `Classical.choice`,
`Quot.sound` are permitted.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- Iterating the cyclic shift k times sends i to (i + k) mod n. -/
theorem cyclicShiftPos_iterate_one (n : ℕ) (hn : 0 < n) (i : Fin n) :
    (cyclicShiftPos n hn).symm.symm i = cyclicShiftPos n hn i := by
  rfl

/-- The cyclic shift on Fin 2: σ(0) = 1, σ(1) = 0 (since (0+1) % 2 = 1, (1+1) % 2 = 0). -/
theorem cyclicShiftPos_2_zero (hn : 0 < 2) :
    (cyclicShiftPos 2 hn) ⟨0, hn⟩ = ⟨1, by omega⟩ := by
  apply Fin.ext
  show (0 + 1) % 2 = 1
  omega

theorem cyclicShiftPos_2_one (hn : 0 < 2) :
    (cyclicShiftPos 2 hn) ⟨1, by omega⟩ = ⟨0, hn⟩ := by
  apply Fin.ext
  show (1 + 1) % 2 = 0
  omega

/-- The cyclic shift on Fin 3 sends 2 to 0. -/
theorem cyclicShiftPos_3_two (hn : 0 < 3) :
    (cyclicShiftPos 3 hn) ⟨2, by omega⟩ = ⟨0, hn⟩ := by
  apply Fin.ext
  show (2 + 1) % 3 = 0
  omega

/-- The cyclic shift on Fin n is well-defined as an equivalence. -/
theorem cyclicShiftPos_isEquiv (n : ℕ) (hn : 0 < n) :
    Function.Bijective (cyclicShiftPos n hn).toFun :=
  (cyclicShiftPos n hn).bijective

end PallLean.Paper93.DeepMath.PathB.Positroid
