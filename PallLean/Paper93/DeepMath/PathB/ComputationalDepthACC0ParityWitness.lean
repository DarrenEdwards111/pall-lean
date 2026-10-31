import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SymAndForm
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0Multilinearize

/-!
# Brick (parity witness) — an explicit function with no low-degree `F_p` representation (proved)

The explicit Razborov–Smolensky witness, for the cleanest case: the **sign / `±1`-parity** function `signWt x = ∏ᵢ (−1)^{xᵢ}`
over `F_p` with `p` odd (the `{±1}` form of `MOD_2`).  For `D < n` it has **no** degree-`≤D` `F_p` representation — an
*explicit* not-low-degree witness, in contrast to the counting (Shannon) witness.

The proof is the sign-functional `Dsign f = ∑ₓ signWt(x) · f(x)`:
* `Dsign` kills every degree-`≤D` polynomial (`D < n`): each monomial is an `AND` over a proper subset `S ⊊ univ`, and
  toggling a bit outside `S` is a sign-flipping involution, so the sum cancels (`Dsign_andVal_zero`).
* `Dsign(signWt) = 2^n ≠ 0` over `F_p` (`p` odd), since `signWt² = 1` (`Dsign_signWt_ne`).

A degree-`≤D` representation of `signWt` would give `Dsign = 0` and `Dsign = 2^n`, a contradiction.

## What is proved (clean axioms, no `sorry`)

* **`signWt_sq`** (PROVED) — `signWt x * signWt x = 1`.
* **`Dsign_andVal_zero`** (PROVED) — `S ≠ univ → ∑ₓ signWt x · andVal S x = 0` (toggle-bit involution).
* **`signWt_no_lowdeg_repr`** (PROVED) — `p ≠ 2 → D < n → ¬∃ P, P.totalDegree ≤ D ∧ ∀ x, eval(bv∘x) P = signWt x`.

## Honest scope

This is the **explicit** witness for the sign-parity (`MOD_2`-sign) function over odd `p`.  It does **not** cover general
`MOD_q` (`q > 2`) — the full RS lower bound — nor wrap it as a Boolean barrier instance (the Boolean parity follows via
`signWt = 1 − 2·parity`, an affine transform, not packaged here).  General YBT and `NEXP ⊄ ACC⁰` remain open.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ParityWitness

open MvPolynomial Finset
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitRepr (bv)
open PallLean.Paper93.DeepMath.PathB.ACC0Multilinearize (support_card_le_totalDegree)
open PallLean.Paper93.DeepMath.PathB.ACC0SymAndForm (andVal eval_eq_sum_andTerms)

variable {n p : ℕ} [Fact p.Prime]

/-- The per-bit sign: `-1` for a set bit, `1` otherwise. -/
def hsign (p : ℕ) (b : Bool) : ZMod p := if b then -1 else 1

theorem hsign_neg (b : Bool) : hsign p (!b) = - hsign p b := by cases b <;> simp [hsign]

/-- The sign / `±1`-parity function `∏ᵢ (−1)^{xᵢ}` over `F_p`. -/
def signWt (p : ℕ) (x : Fin n → Bool) : ZMod p := ∏ i, hsign p (x i)

theorem signWt_sq (x : Fin n → Bool) : signWt p x * signWt p x = 1 := by
  unfold signWt
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one (fun i _ => by cases x i <;> simp [hsign])

theorem signWt_toggle (i₀ : Fin n) (x : Fin n → Bool) :
    signWt p (Function.update x i₀ (!x i₀)) = - signWt p x := by
  have e1 : signWt p (Function.update x i₀ (!x i₀))
      = hsign p (!x i₀) * ∏ i ∈ univ.erase i₀, hsign p (x i) := by
    unfold signWt
    rw [← Finset.mul_prod_erase univ _ (mem_univ i₀), Function.update_self]
    congr 1
    exact Finset.prod_congr rfl (fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)])
  have e2 : signWt p x = hsign p (x i₀) * ∏ i ∈ univ.erase i₀, hsign p (x i) := by
    unfold signWt; rw [← Finset.mul_prod_erase univ _ (mem_univ i₀)]
  rw [e1, e2, hsign_neg]; ring

omit [Fact p.Prime] in
theorem andVal_toggle {S : Finset (Fin n)} {i₀ : Fin n} (hi₀ : i₀ ∉ S) (x : Fin n → Bool) :
    (andVal S (Function.update x i₀ (!x i₀)) : ZMod p) = andVal S x := by
  unfold andVal
  exact Finset.prod_congr rfl (fun i hi => by rw [Function.update_of_ne (ne_of_mem_of_not_mem hi hi₀)])

/-- `2 ≠ 0` over `F_p` for odd `p`. -/
theorem two_ne (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro hc
  have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast hc
  rw [ZMod.natCast_eq_zero_iff] at this
  exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp this)

/-- **`Dsign` kills a proper `AND`-monomial (PROVED): the toggle-bit involution cancels.** -/
theorem Dsign_andVal_zero (hp2 : p ≠ 2) {S : Finset (Fin n)} (hS : S ≠ Finset.univ) :
    (∑ x : Fin n → Bool, signWt p x * andVal S x) = 0 := by
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, i₀ ∉ S := by
    by_contra hc; push_neg at hc; exact hS (Finset.eq_univ_of_forall hc)
  set τ : Equiv.Perm (Fin n → Bool) :=
    (Function.Involutive.toPerm (fun x => Function.update x i₀ (!x i₀))
      (fun x => by funext j; by_cases hj : j = i₀ <;> simp [Function.update, hj])) with hτ
  have hflip : ∑ x : Fin n → Bool, signWt p x * andVal S x
      = - ∑ x : Fin n → Bool, signWt p x * andVal S x := by
    calc ∑ x, signWt p x * andVal S x
        = ∑ x, signWt p (τ x) * andVal S (τ x) := (Equiv.sum_comp τ _).symm
      _ = ∑ x, - (signWt p x * andVal S x) := by
            refine Finset.sum_congr rfl (fun x _ => ?_)
            show signWt p (Function.update x i₀ (!x i₀)) * andVal S (Function.update x i₀ (!x i₀)) = _
            rw [signWt_toggle, andVal_toggle hi₀]; ring
      _ = - ∑ x, signWt p x * andVal S x := by rw [Finset.sum_neg_distrib]
  have h2 : (2 : ZMod p) * (∑ x : Fin n → Bool, signWt p x * andVal S x) = 0 := by
    rw [two_mul]; nth_rewrite 2 [hflip]; ring
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd h (two_ne hp2)
  · exact h

/-- **`Dsign(signWt) = 2^n ≠ 0` over odd `F_p` (PROVED).** -/
theorem Dsign_signWt_ne (hp2 : p ≠ 2) : (∑ x : Fin n → Bool, signWt p x * signWt p x) ≠ 0 := by
  have hval : (∑ x : Fin n → Bool, signWt p x * signWt p x) = ((2 ^ n : ℕ) : ZMod p) := by
    rw [Finset.sum_congr rfl (fun x _ => signWt_sq x), Finset.sum_const, Finset.card_univ,
      Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [hval]
  intro hc
  rw [ZMod.natCast_eq_zero_iff] at hc
  exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp
    ((Fact.out : p.Prime).dvd_of_dvd_pow hc))

/-- **The explicit witness (PROVED): the sign-parity function has no low-degree `F_p` representation.** -/
theorem signWt_no_lowdeg_repr (hp2 : p ≠ 2) {D : ℕ} (hn : D < n) :
    ¬ ∃ P : MvPolynomial (Fin n) (ZMod p),
        P.totalDegree ≤ D ∧ ∀ x, eval (fun i => (bv (x i) : ZMod p)) P = signWt p x := by
  rintro ⟨P, hdeg, hP⟩
  -- Dsign applied to the (representing) polynomial is 0 …
  have h0 : (∑ x : Fin n → Bool, signWt p x * eval (fun i => (bv (x i) : ZMod p)) P) = 0 := by
    simp_rw [eval_eq_sum_andTerms, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero (fun e he => ?_)
    have hsupp : e.support ≠ Finset.univ := by
      intro hc
      have hle := support_card_le_totalDegree P e he
      rw [hc, Finset.card_univ, Fintype.card_fin] at hle
      omega
    calc ∑ x, signWt p x * (coeff e P * andVal e.support x)
        = coeff e P * ∑ x, signWt p x * andVal e.support x := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun x _ => by ring)
      _ = coeff e P * 0 := by rw [Dsign_andVal_zero hp2 hsupp]
      _ = 0 := mul_zero _
  -- … but equals `Dsign(signWt) ≠ 0`.
  rw [Finset.sum_congr rfl (fun x _ => by rw [hP x])] at h0
  exact Dsign_signWt_ne hp2 h0

/-!
**The explicit witness, proved.**  The sign-parity function `signWt` over odd `F_p` has no degree-`<n` `F_p` representation —
an explicit Razborov–Smolensky witness (for `MOD_2` in `±1` form).  General `MOD_q` (`q > 2`) is the full RS bound (tree's
`Layer4`); the Boolean barrier instance follows via the affine `signWt = 1 − 2·parity`.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0ParityWitness

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ParityWitness.signWt_no_lowdeg_repr
