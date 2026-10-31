import Mathlib.Data.Nat.Choose.Central
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Mathlib extraction candidates

Two self-contained, generally-useful `ℕ` lemmas isolated from the Razborov–Smolensky `AC⁰[p]`
development.  This file imports **only Mathlib** (no project dependencies), so each lemma can be lifted
into a Mathlib PR as-is.

* `Nat.centralBinom_sq_mul_le` — the integer form of the classical refinement
  `centralBinom m ≤ 4^m / √(2m+1)`, i.e. `(2m+1)·(centralBinom m)² ≤ 4^{2m}`.
* `Nat.exists_poly_lt_pow` — "exponential eventually dominates polynomial": for a base `p ≥ 2` and any
  polynomial `A·nᶜ + B`, some `n` has `A·nᶜ + B < pⁿ`.
-/

namespace Nat

/-- **Central binomial `√n` bound (integer form).**  `(2m+1)·(centralBinom m)² ≤ 4^{2m}`.

This is the integer-arithmetic form of the standard refinement `centralBinom m ≤ 4^m / √(2m+1)` of the
crude `centralBinom m ≤ 4^m`.  Proved by induction using `Nat.succ_mul_centralBinom_succ`
(`(m+1)·centralBinom (m+1) = 2(2m+1)·centralBinom m`) and the step `(2m+3)(2m+1) ≤ 4(m+1)²`. -/
theorem centralBinom_sq_mul_le : ∀ m : ℕ, (2 * m + 1) * (centralBinom m) ^ 2 ≤ 4 ^ (2 * m)
  | 0 => by simp [Nat.centralBinom_zero]
  | m + 1 => by
      have ih := centralBinom_sq_mul_le m
      have hrec := Nat.succ_mul_centralBinom_succ m
      set c := centralBinom m
      set c' := centralBinom (m + 1)
      have e1 : (m + 1) ^ 2 * c' ^ 2 = 4 * (2 * m + 1) ^ 2 * c ^ 2 := by
        rw [← mul_pow, hrec]; ring
      have key : (m + 1) ^ 2 * ((2 * (m + 1) + 1) * c' ^ 2)
          ≤ (m + 1) ^ 2 * 4 ^ (2 * (m + 1)) := by
        have h4 : (4 : ℕ) ^ (2 * (m + 1)) = 16 * 4 ^ (2 * m) := by
          rw [show 2 * (m + 1) = 2 * m + 2 from by ring, pow_add]; ring
        calc (m + 1) ^ 2 * ((2 * (m + 1) + 1) * c' ^ 2)
            = (2 * (m + 1) + 1) * ((m + 1) ^ 2 * c' ^ 2) := by ring
          _ = (2 * (m + 1) + 1) * (4 * (2 * m + 1) ^ 2 * c ^ 2) := by rw [e1]
          _ = 4 * (2 * (m + 1) + 1) * (2 * m + 1) * ((2 * m + 1) * c ^ 2) := by ring
          _ ≤ 4 * (2 * (m + 1) + 1) * (2 * m + 1) * 4 ^ (2 * m) := Nat.mul_le_mul_left _ ih
          _ ≤ (m + 1) ^ 2 * 16 * 4 ^ (2 * m) := Nat.mul_le_mul_right _ (by nlinarith)
          _ = (m + 1) ^ 2 * 4 ^ (2 * (m + 1)) := by rw [h4]; ring
      exact Nat.le_of_mul_le_mul_left key (by positivity)

open Asymptotics Filter in
/-- **Exponential dominates polynomial.**  For a base `p ≥ 2` and any `A, C, B : ℕ`, there is `n` (indeed
some `n ≥ 1`) with `A·nᶜ + B < pⁿ`.

Proved by `Asymptotics.isLittleO_pow_const_const_pow_of_one_lt`: `(A+B)·nᶜ = o(pⁿ)`, so eventually
`(A+B)·nᶜ ≤ ½·pⁿ`, and `A·nᶜ + B ≤ (A+B)·nᶜ` for `n ≥ 1`. -/
theorem exists_poly_lt_pow {p : ℕ} (hp : 2 ≤ p) (A C B : ℕ) :
    ∃ n : ℕ, 1 ≤ n ∧ A * n ^ C + B < p ^ n := by
  have hr : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hlo : (fun n : ℕ => ((A + B : ℕ) : ℝ) * (n : ℝ) ^ C) =o[atTop] (fun n : ℕ => (p : ℝ) ^ n) :=
    (isLittleO_pow_const_const_pow_of_one_lt C hr).const_mul_left _
  have hev : ∀ᶠ n : ℕ in atTop,
      ((A + B : ℕ) : ℝ) * (n : ℝ) ^ C ≤ (1 / 2) * (p : ℝ) ^ n := by
    have h := (isLittleO_iff.mp hlo) (show (0 : ℝ) < 1 / 2 by norm_num)
    refine h.mono (fun n hn => ?_)
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity)] at hn
  rw [eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  refine ⟨N + 1, Nat.le_add_left 1 N, ?_⟩
  have hb := hN (N + 1) (Nat.le_succ N)
  have hcastpos : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 N
  have hpow1 : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) ^ C := one_le_pow₀ hcastpos
  have hppos : (0 : ℝ) < (p : ℝ) ^ (N + 1) := by positivity
  have hBle : (B : ℝ) ≤ (B : ℝ) * ((N + 1 : ℕ) : ℝ) ^ C := le_mul_of_one_le_right (by positivity) hpow1
  have hstep1 : (A : ℝ) * ((N + 1 : ℕ) : ℝ) ^ C + (B : ℝ)
      ≤ ((A + B : ℕ) : ℝ) * ((N + 1 : ℕ) : ℝ) ^ C := by
    have hd : ((A + B : ℕ) : ℝ) * ((N + 1 : ℕ) : ℝ) ^ C
        = (A : ℝ) * ((N + 1 : ℕ) : ℝ) ^ C + (B : ℝ) * ((N + 1 : ℕ) : ℝ) ^ C := by push_cast; ring
    rw [hd]; linarith [hBle]
  have hreal : ((A * (N + 1) ^ C + B : ℕ) : ℝ) < ((p ^ (N + 1) : ℕ) : ℝ) := by
    push_cast at hb hstep1 hppos ⊢; linarith
  exact_mod_cast hreal

end Nat

#print axioms Nat.centralBinom_sq_mul_le
#print axioms Nat.exists_poly_lt_pow
