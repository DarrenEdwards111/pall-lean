import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Equiv.Basic

/-!
# Cyclic shift on `Fin n`

The cyclic shift on `Fin n` sends `i ↦ i + 1 (mod n)`, giving a permutation of
order `n`.  This is fundamental to positroid theory: positroid cells are
invariant (in a structured sense) under cyclic shifts, providing the `ℤ/n`
cyclic-symmetry of the Grassmannian stratification.

This file is kernel-only: no `sorry`, no custom `axiom`, no `True`
placeholders.  Only the kernel axioms `propext`, `Classical.choice`,
`Quot.sound` are permitted.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- The cyclic shift on `Fin n` for `n ≥ 1`: `σ(i) = (i + 1) mod n`. -/
def cyclicShiftPos (n : ℕ) (hn : 0 < n) : Fin n ≃ Fin n where
  toFun i := ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩
  invFun i := ⟨(i.val + (n - 1)) % n, Nat.mod_lt _ hn⟩
  left_inv := by
    intro i
    apply Fin.ext
    show ((i.val + 1) % n + (n - 1)) % n = i.val
    have hi : i.val < n := i.isLt
    -- Case split on whether i.val + 1 = n or i.val + 1 < n
    rcases Nat.lt_or_ge (i.val + 1) n with hlt | hge
    · -- i.val + 1 < n, so (i.val + 1) % n = i.val + 1
      rw [Nat.mod_eq_of_lt hlt]
      -- Now need: (i.val + 1 + (n - 1)) % n = i.val
      -- i.val + 1 + (n - 1) = i.val + n
      have : i.val + 1 + (n - 1) = i.val + n := by omega
      rw [this]
      -- (i.val + n) % n = i.val % n = i.val
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt hi]
    · -- i.val + 1 ≥ n, combined with i.val < n means i.val + 1 = n
      have heq : i.val + 1 = n := by omega
      rw [heq]
      rw [Nat.mod_self]
      -- Now (0 + (n - 1)) % n = i.val, i.e., (n - 1) % n = i.val
      simp only [Nat.zero_add]
      rw [Nat.mod_eq_of_lt (by omega : n - 1 < n)]
      omega
  right_inv := by
    intro i
    apply Fin.ext
    show ((i.val + (n - 1)) % n + 1) % n = i.val
    have hi : i.val < n := i.isLt
    -- Case split on whether i.val = 0 or i.val ≥ 1
    rcases Nat.eq_zero_or_pos i.val with h0 | hpos
    · -- i.val = 0, so i.val + (n - 1) = n - 1
      rw [h0]
      simp only [Nat.zero_add]
      rw [Nat.mod_eq_of_lt (by omega : n - 1 < n)]
      -- Now (n - 1 + 1) % n = 0
      have : n - 1 + 1 = n := by omega
      rw [this, Nat.mod_self]
    · -- i.val ≥ 1, so i.val + (n - 1) ≥ n, and i.val + (n - 1) < 2n
      -- i.val + (n - 1) = (i.val - 1) + n, so mod n = i.val - 1
      have hsplit : i.val + (n - 1) = (i.val - 1) + n := by omega
      rw [hsplit]
      rw [Nat.add_mod_right]
      rw [Nat.mod_eq_of_lt (by omega : i.val - 1 < n)]
      -- Now (i.val - 1 + 1) % n = i.val
      have : i.val - 1 + 1 = i.val := by omega
      rw [this, Nat.mod_eq_of_lt hi]

/-- The cyclic shift sends `0` to `1` (when `n ≥ 2`). -/
theorem cyclicShiftPos_zero (n : ℕ) (hn : 0 < n) (h2 : 2 ≤ n) :
    (cyclicShiftPos n hn) ⟨0, hn⟩ = ⟨1, by omega⟩ := by
  apply Fin.ext
  show (0 + 1) % n = 1
  rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega : 1 < n)]

/-- The cyclic shift on `Fin 1` is the identity (since `(0+1) % 1 = 0`). -/
theorem cyclicShiftPos_n_one (hn : 0 < 1) (i : Fin 1) :
    (cyclicShiftPos 1 hn) i = i := by
  apply Fin.ext
  show (i.val + 1) % 1 = i.val
  have hi : i.val < 1 := i.isLt
  have : i.val = 0 := by omega
  rw [this, Nat.mod_one]

/-- The inverse of the cyclic shift sends `1` to `0` (when `n ≥ 2`). -/
theorem cyclicShiftPos_symm_one (n : ℕ) (hn : 0 < n) (h2 : 2 ≤ n) :
    (cyclicShiftPos n hn).symm ⟨1, by omega⟩ = ⟨0, hn⟩ := by
  apply Fin.ext
  show (1 + (n - 1)) % n = 0
  have : 1 + (n - 1) = n := by omega
  rw [this, Nat.mod_self]

end PallLean.Paper93.DeepMath.PathB.Positroid
