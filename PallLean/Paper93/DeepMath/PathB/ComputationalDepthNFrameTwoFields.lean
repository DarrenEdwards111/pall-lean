import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameCompositeMOD

/-!
# The multi-prime composite barrier: the char-matching modulus is a low-degree blind spot

C14 killed the naive `P(∑∏)`-over-`F_ℓ` route for a composite `MOD_m` (`m ∤ ℓ`).  The escape (C11) is a *root-of-unity*
arithmetisation, which works for a **prime-power** modulus.  A genuine multi-prime `m = p₁ᵉ¹⋯` (the `MOD_6` case) needs
one root of unity per prime-power factor, and the single-field polynomial method fails.  This file formalises *why*.

The structural reason is the **two-fields blind spot**: over a field of characteristic `ℓ`, the modulus that *matches*
the characteristic is **low** N-Frame complexity, while a *coprime* modulus is high.

  `charModFn` — `MOD_ℓ` (the char-matching modulus): the Boolean function `[∑ xᵢ ≡ 0 in F]`.
  `charModFn_eq_boolFn` — Fermat: on the cube `[∑ xᵢ = 0 in F] = 1 − (∑Xᵢ)^{|F|−1}`, a degree-`(|F|−1)` polynomial.
  `nframeComplexity_charModFn_le` — hence `NFrameComplexity (MOD_ℓ) ≤ |F| − 1` (LOW).
  `two_fields_blindspot` — over `F`, `NFrameComplexity (MOD_ℓ) < NFrameComplexity (MOD_q)` for a coprime `MOD_q` (C11),
        once `|F| − 1 < ⌈n/2⌉`.

So for a `MOD_6` circuit (using `MOD_2` and `MOD_3` gates): over `F_2` the `MOD_2` gates are low-degree (invisible to the
`F_2` polynomial argument) while `MOD_3` is high; over `F_3` it is the reverse.  **No single field makes all the moduli
of a multi-prime circuit hard** — each field has a blind spot at its own characteristic.  That is exactly why the
single-field polynomial method cannot prove multi-prime composite `MOD` lower bounds, and why `MOD_6` is open.

## Honest scope

This formalises the *obstruction*, not a crossing: it proves the char-matching modulus is a genuine low-complexity blind
spot (`nframeComplexity_charModFn_le`, from Fermat), so the single-field method provably has a gap for every field.
Crossing it needs a multi-field / non-polynomial argument (Williams' route, or something new) — not built here.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameACC0

open MvPolynomial Finset
open PallLean.Paper93.DeepMath.PathB.ModQReduction (omegaFn)

variable {n : ℕ} {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The char-matching modulus polynomial: `1 − (∑ Xᵢ)^{|F|−1}` (Fermat form of `[∑ = 0 in F]`). -/
noncomputable def charModPoly (n : ℕ) (F : Type*) [Field F] [Fintype F] : MvPolynomial (Fin n) F :=
  1 - (∑ i, X i) ^ (Fintype.card F - 1)

/-- `MOD_ℓ` (char-matching modulus) as a Boolean function: `[∑ xᵢ ≡ 0 in F]` (weight ≡ 0 mod `char`). -/
noncomputable def charModFn (n : ℕ) (F : Type*) [Field F] [Fintype F] [DecidableEq F] : (Fin n → Bool) → F :=
  fun x => if (∑ i, (if x i then (1 : F) else 0)) = 0 then 1 else 0

theorem totalDegree_charModPoly_le : (charModPoly n F).totalDegree ≤ Fintype.card F - 1 := by
  refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
  rw [MvPolynomial.totalDegree_one]
  refine max_le (Nat.zero_le _) (le_trans (MvPolynomial.totalDegree_pow _ _) ?_)
  refine le_trans (Nat.mul_le_mul (le_refl _)
    (le_trans (MvPolynomial.totalDegree_finset_sum _ _)
      (Finset.sup_le (fun i _ => by rw [MvPolynomial.totalDegree_X])))) ?_
  omega

/-- **Fermat form (proved)**: on the cube, `MOD_ℓ` is the degree-`(|F|−1)` polynomial `1 − (∑Xᵢ)^{|F|−1}`. -/
theorem charModFn_eq_boolFn : charModFn n F = boolFn (charModPoly n F) := by
  funext x
  rw [charModFn, boolFn, charModPoly]
  simp only [map_sub, map_one, map_pow, map_sum, MvPolynomial.eval_X]
  by_cases hS : (∑ i, (if x i then (1 : F) else 0)) = 0
  · rw [if_pos hS, hS, zero_pow (Nat.sub_ne_zero_of_lt Fintype.one_lt_card), sub_zero]
  · rw [if_neg hS, FiniteField.pow_card_sub_one_eq_one _ hS, sub_self]

/-- **The char-matching modulus is low N-Frame complexity (proved)**: `NFrameComplexity (MOD_ℓ) ≤ |F| − 1`.  This is the
blind spot — over `F` the modulus matching the characteristic is degree `≤ |F|−1`, invisible to the polynomial method. -/
theorem nframeComplexity_charModFn_le : NFrameComplexity F (charModFn n F) ≤ Fintype.card F - 1 := by
  rw [charModFn_eq_boolFn]
  exact le_trans (nframeComplexity_boolFn_le _) totalDegree_charModPoly_le

/-- **The two-fields blind spot (proved)**: over `F`, the char-matching modulus `MOD_ℓ` has strictly *lower* N-Frame
complexity than a coprime `MOD_q` (`ω` of order `q`), once `|F| − 1 < ⌈n/2⌉`.  So no single field makes both hard — the
structural reason the single-field polynomial method fails for multi-prime composite modulus. -/
theorem two_fields_blindspot {q : ℕ} (ω : F) (hω : orderOf ω = q) (hq2 : 2 ≤ q)
    (hn : Fintype.card F - 1 < n - n / 2) :
    NFrameComplexity F (charModFn n F) < NFrameComplexity F (omegaFn ω (Finset.univ : Finset (Fin n))) :=
  lt_of_le_of_lt nframeComplexity_charModFn_le
    (lt_of_lt_of_le hn (nframeComplexity_omegaFn_univ_ge ω hω hq2))

end PallLean.Paper93.DeepMath.PathB.NFrameACC0

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameACC0.nframeComplexity_charModFn_le
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameACC0.two_fields_blindspot
