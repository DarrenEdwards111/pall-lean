import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ParityWitness

/-!
# Brick (char witness) — the `MOD_q` character has no low-degree `F_p` representation (proved)

The general-`q` Razborov–Smolensky witness: for any `ζ ≠ 1` in `F_p` (`p` odd), the `q`-ary character `charWt_ζ(x) = ∏ᵢ
(if xᵢ then ζ else 1) = ζ^{weight(x)}` has **no** degree-`<n` `F_p` representation.  For `ζ` a primitive `q`-th root of unity
(which lives in `F_p` exactly when `q ∣ p−1`), this is the `MOD_q` character — the building block of `MOD_q = (1/q) ∑ⱼ
charWt_{ζ^j}` — generalising the parity (`q=2`, `ζ=−1`) witness.

The proof reuses the parity sign-functional `Dsign f = ∑ₓ signWt(x)·f(x)` (Brick parity witness): `Dsign` kills every
degree-`<n` polynomial (toggle-bit involution, `Dsign_andVal_zero`), while `Dsign(charWt_ζ) = (1−ζ)^n ≠ 0` (a product
factorisation over the Boolean cube).  So `charWt_ζ` is not degree-`<n`.

## What is proved (clean axioms, no `sorry`)

* **`charWt`** — the `q`-ary character `ζ^{weight}`.
* **`Dsign_charWt`** (PROVED) — `∑ₓ signWt x · charWt ζ x = (1−ζ)^n`.
* **`charWt_no_lowdeg_repr`** (PROVED) — `p≠2, ζ≠1, D<n → ¬∃ P, P.totalDegree ≤ D ∧ ∀ x, eval(bv∘x) P = charWt ζ x`.

## Honest scope

This is the explicit witness for every `MOD_q` *character* (`ζ ≠ 1`) over odd `F_p` — the general-`q` generalisation of the
parity witness.  It does **not** package the *Boolean* `MOD_q` indicator (`= (1/q)∑ⱼ charWt_{ζ^j}`), whose own degree needs
the character-sum `∑ⱼ (1−ζ^j)^n ≠ 0` (the harder part), nor the Williams cash-out.  General YBT and `NEXP ⊄ ACC⁰` remain open.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0CharWitness

open MvPolynomial Finset
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitRepr (bv)
open PallLean.Paper93.DeepMath.PathB.ACC0Multilinearize (support_card_le_totalDegree)
open PallLean.Paper93.DeepMath.PathB.ACC0SymAndForm (andVal eval_eq_sum_andTerms)
open PallLean.Paper93.DeepMath.PathB.ACC0ParityWitness (signWt hsign Dsign_andVal_zero)

variable {n p : ℕ} [Fact p.Prime]

/-- The `q`-ary character `ζ^{weight(x)} = ∏ᵢ (if xᵢ then ζ else 1)`. -/
def charWt (ζ : ZMod p) (x : Fin n → Bool) : ZMod p := ∏ i, (if x i then ζ else 1)

/-- **`Dsign(charWt_ζ) = (1−ζ)^n` (PROVED).** -/
theorem Dsign_charWt (ζ : ZMod p) :
    (∑ x : Fin n → Bool, signWt p x * charWt ζ x) = (1 - ζ) ^ n := by
  have key : (∑ x : Fin n → Bool, signWt p x * charWt ζ x)
      = ∏ i : Fin n, ∑ b : Bool, (if b then -ζ else (1 : ZMod p)) := by
    rw [show (∑ x : Fin n → Bool, signWt p x * charWt ζ x)
          = ∑ x : Fin n → Bool, ∏ i, (if x i then -ζ else (1 : ZMod p)) from
        Finset.sum_congr rfl (fun x _ => by
          unfold signWt charWt
          rw [← Finset.prod_mul_distrib]
          exact Finset.prod_congr rfl (fun i _ => by unfold hsign; cases x i <;> simp))]
    rw [Finset.prod_univ_sum]; congr 1
  rw [key]
  have hb : ∀ i : Fin n, (∑ b : Bool, (if b then -ζ else (1 : ZMod p))) = 1 - ζ := by
    intro i; rw [Fintype.sum_bool]; simp; ring
  rw [Finset.prod_congr rfl (fun i _ => hb i), Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- `Dsign` kills every degree-`<n` polynomial (PROVED). -/
theorem Dsign_eval_zero (hp2 : p ≠ 2) {D : ℕ} (P : MvPolynomial (Fin n) (ZMod p))
    (hdeg : P.totalDegree ≤ D) (hn : D < n) :
    (∑ x : Fin n → Bool, signWt p x * eval (fun i => (bv (x i) : ZMod p)) P) = 0 := by
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

/-- **The general `MOD_q`-character witness (PROVED): `charWt_ζ` (`ζ≠1`) has no low-degree `F_p` representation.** -/
theorem charWt_no_lowdeg_repr (hp2 : p ≠ 2) (ζ : ZMod p) (hζ : ζ ≠ 1) {D : ℕ} (hn : D < n) :
    ¬ ∃ P : MvPolynomial (Fin n) (ZMod p),
        P.totalDegree ≤ D ∧ ∀ x, eval (fun i => (bv (x i) : ZMod p)) P = charWt ζ x := by
  rintro ⟨P, hdeg, hP⟩
  have h0 := Dsign_eval_zero hp2 P hdeg hn
  rw [Finset.sum_congr rfl (fun x _ => by rw [hP x]), Dsign_charWt] at h0
  exact pow_ne_zero n (sub_ne_zero.mpr (Ne.symm hζ)) h0

/-!
**The general `MOD_q`-character witness, proved.**  Every `MOD_q` character `ζ^{weight}` (`ζ≠1`) over odd `F_p` has no
degree-`<n` representation — the general-`q` generalisation of the parity witness, via the same sign-functional with
`Dsign(charWt_ζ) = (1−ζ)^n ≠ 0`.  Remaining (open, not faked): the Boolean `MOD_q` indicator's degree (character-sum
nonvanishing) and the Williams cash-out.  Not `NEXP ⊄ ACC⁰`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0CharWitness

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CharWitness.charWt_no_lowdeg_repr
