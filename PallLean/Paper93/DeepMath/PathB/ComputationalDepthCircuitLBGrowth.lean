import Mathlib.Tactic

/-!
# `2^n` is not polynomially bounded — the poly-vs-exp fact, formalized

Several wall-face bricks used `PolyBounded T := ∃ c d, ∀ n, T n ≤ c·(n+1)^d` and worked *around* the
fact that `2^n` exceeds every polynomial (e.g. `SequentialAccessFace` proved only that padding a poly
bound stays poly).  This file proves the fact itself: `¬ PolyBounded (fun n => 2^n)`.

The concrete claim was pre-checked in SymPy (via mikoshilang) before formalizing: `lim 2^n/(c(n+1)^d) =
∞`, with explicit witnesses (`c=1000, d=5` first fails at `n=37`).  Only *then* was it proved in Lean —
so the corpus never formalizes a concrete claim the symbolic engine hasn't confirmed.

## What is proved

* **`lin_le_two_pow`** — `2^m` dominates any linear `a·m + 1` once `m ≥ a²`.  (Split `2^m = 2^a·2^{m-a}`
  and use `k < 2^k` on each factor.)
* **`two_pow_not_polyBounded`** — `¬ PolyBounded (fun n => 2^n)`.  Reduce the polynomial to the linear
  case via `n = (d+1)·m`, so `2^n = (2^m)^{d+1}`, and pick `m ≥ max((d+1)², c)`.

## Honest scope

An elementary growth fact, machine-checked, that the corpus previously side-stepped.  It is not about
`P` vs `NP`; it is the poly-vs-exp arithmetic that underlies the scale-bridge and sequential-access
faces.  Nothing here is a separation.
-/

namespace PallLean.Paper93.DeepMath.PathB.CircuitLBGrowth

/-- Polynomial boundedness (as used in the wall-face bricks). -/
def PolyBounded (T : ℕ → ℕ) : Prop := ∃ c d : ℕ, ∀ n, T n ≤ c * (n + 1) ^ d

/-- **`2^m` dominates any linear function (proved).**  For `m ≥ a·a`, `a·m + 1 ≤ 2^m`.  Proof: split
`2^m = 2^a · 2^{m-a}` and apply `k < 2^k` (i.e. `k + 1 ≤ 2^k`) to each factor. -/
theorem lin_le_two_pow (a m : ℕ) (hm : a * a ≤ m) : a * m + 1 ≤ 2 ^ m := by
  have ham : a ≤ m := by
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · exact Nat.zero_le m
    · exact le_trans (Nat.le_mul_of_pos_left a ha) hm
  obtain ⟨j, rfl⟩ : ∃ j, m = a + j := ⟨m - a, by omega⟩
  have h1 : a + 1 ≤ 2 ^ a := Nat.lt_two_pow_self
  have h2 : j + 1 ≤ 2 ^ j := Nat.lt_two_pow_self
  have hmul : (a + 1) * (j + 1) ≤ 2 ^ a * 2 ^ j := Nat.mul_le_mul h1 h2
  have hkey : a * (a + j) + 1 ≤ (a + 1) * (j + 1) := by nlinarith [hm]
  calc a * (a + j) + 1 ≤ (a + 1) * (j + 1) := hkey
    _ ≤ 2 ^ a * 2 ^ j := hmul
    _ = 2 ^ (a + j) := (pow_add 2 a j).symm

/-- **`2^n` is not polynomially bounded (proved).**  Pre-checked in SymPy (`lim 2^n/(c(n+1)^d) = ∞`);
proved here by reducing the polynomial to the linear case at `n = (d+1)·m`. -/
theorem two_pow_not_polyBounded : ¬ PolyBounded (fun n => 2 ^ n) := by
  rintro ⟨c, d, h⟩
  set m := max ((d + 1) * (d + 1)) c with hmdef
  have hm1 : (d + 1) * (d + 1) ≤ m := le_max_left _ _
  have hmc : c ≤ m := le_max_right _ _
  have hc2 : c < 2 ^ m := lt_of_le_of_lt hmc Nat.lt_two_pow_self
  have hlin : (d + 1) * m + 1 ≤ 2 ^ m := lin_le_two_pow (d + 1) m hm1
  have hpoly : ((d + 1) * m + 1) ^ d ≤ (2 ^ m) ^ d := Nat.pow_le_pow_left hlin d
  have hpos : 0 < (2 ^ m) ^ d := pow_pos (pow_pos (by norm_num) m) d
  have hstrict : c * ((d + 1) * m + 1) ^ d < 2 ^ ((d + 1) * m) := by
    calc c * ((d + 1) * m + 1) ^ d
        ≤ c * (2 ^ m) ^ d := Nat.mul_le_mul (le_refl c) hpoly
      _ < 2 ^ m * (2 ^ m) ^ d := by
          have := (Nat.mul_lt_mul_right hpos).mpr hc2
          simpa [Nat.mul_comm] using this
      _ = (2 ^ m) ^ (d + 1) := by rw [pow_succ]; ring
      _ = 2 ^ ((d + 1) * m) := by rw [← pow_mul, Nat.mul_comm]
  have hle : 2 ^ ((d + 1) * m) ≤ c * ((d + 1) * m + 1) ^ d := h ((d + 1) * m)
  omega

end PallLean.Paper93.DeepMath.PathB.CircuitLBGrowth

#print axioms PallLean.Paper93.DeepMath.PathB.CircuitLBGrowth.two_pow_not_polyBounded
