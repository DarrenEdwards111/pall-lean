/-
  PallLean/Paper93/Paper283/TseitinCharge.lean

  Paper §28.3 — Tseitin charge `χ : V_n → {±1}`.

  ## Scope

  This file records the Paper §28.3 line 6870 *Tseitin charge* as a map
  assigning `+1` or `−1` to each vertex of the expander. We provide:

    * `TseitinCharge N` — the type of Tseitin charges on `Fin N`;
    * `chargesSum χ`    — the integer sum of the charges;
    * `IsOddCharge χ`   — odd-parity predicate on the sum (the Tseitin
                           CNF is unsatisfiable precisely when the
                           charge is odd);
    * `constOneCharge N` — the constant `+1` charge;
    * `constOneCharge_sum` — its sum equals `N` (so odd on odd `N`).

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  ## Paper citations

    * §28.3 line 6870 — Tseitin charge `χ : V_n → {±1}`.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Ring.Int.Defs

namespace PallLean.Paper93.Paper283

open scoped BigOperators

/-- Tseitin charge: assigns +1 or -1 to each vertex of the expander.
    Paper §28.3 line 6870. -/
def TseitinCharge (N : ℕ) := Fin N → ({-1, 1} : Set ℤ)

/-- Sum of charges = total parity (must be odd for unsatisfiable Tseitin). -/
noncomputable def chargesSum {N : ℕ} (χ : TseitinCharge N) : ℤ :=
  ∑ v, (χ v).val

/-- Odd-charge characterization: for parity-odd, sum is odd, making
    Tseitin CNF unsatisfiable. -/
def IsOddCharge {N : ℕ} (χ : TseitinCharge N) : Prop := Odd (chargesSum χ)

/-- Concrete instance: constant `+1` charge. On odd `N` this gives an
    odd sum (see `constOneCharge_sum`). -/
noncomputable def constOneCharge (N : ℕ) : TseitinCharge N :=
  fun _ => ⟨1, by simp⟩

/-- The sum of the constant `+1` charge over `Fin N` equals `N`. -/
theorem constOneCharge_sum (N : ℕ) : chargesSum (constOneCharge N) = N := by
  unfold chargesSum constOneCharge
  simp

end PallLean.Paper93.Paper283
