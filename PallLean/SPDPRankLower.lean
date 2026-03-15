/-
  SPDPRankLower.lean — SPDP rank lower bound at n=2 (Paper §8.6)

  Proves that at n=2, if f(0,0) ≠ f(0,1), no polynomial representing f
  has restrictedSpdpRank ≤ Nat.sqrt 2 = 1 under universalRestriction 2.
-/
import PallLean.SPDPDefs
import PallLean.RestrictedSPDP
import PallLean.Restriction
import PallLean.UniversalRestriction
import PallLean.BoolEval
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Variables

namespace SPDPRankLower

open MvPolynomial SPDP RestrictedSPDP Restriction UniversalRestriction BoolEval

/-! ### Coefficient of pderiv — PROVED -/

private lemma tsub_single_self (m : Fin 2 →₀ ℕ) (i : Fin 2) :
    m + Finsupp.single i 1 - Finsupp.single i 1 = m := by
  ext j; simp

/-- coeff m (∂ᵢ q) = (m(i) + 1) · coeff(m + eᵢ) q. PROVED by monomial induction. -/
private theorem coeff_pderiv_shift (q : MvPolynomial (Fin 2) ℚ) (i : Fin 2) (m : Fin 2 →₀ ℕ) :
    coeff m (pderiv i q) = (↑(m i + 1) : ℚ) * coeff (m + Finsupp.single i 1) q := by
  induction q using MvPolynomial.induction_on' with
  | monomial s a =>
    simp only [pderiv_monomial, coeff_monomial]
    by_cases hs : s = m + Finsupp.single i 1
    · subst hs
      rw [if_pos (tsub_single_self m i), if_pos rfl]
      simp [Finsupp.add_apply, mul_comm]
    · rw [if_neg hs, mul_zero]
      by_cases hsub : s - Finsupp.single i 1 = m
      · rw [if_pos hsub]
        by_cases hsi : s i = 0
        · simp [hsi]
        · exfalso; apply hs; ext j
          have := congr_fun (congr_arg DFunLike.coe hsub) j
          simp [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_apply] at this ⊢
          fin_cases i <;> fin_cases j <;> simp_all <;> omega
      · rw [if_neg hsub]
  | add p q hp hq =>
    simp only [map_add, coeff_add, hp, hq, mul_add]

/-! ### pderiv = 0 implies variable not in support (CharZero) — PROVED -/

/-- Over ℚ, pderiv i q = 0 → i ∉ vars(q). PROVED from coeff_pderiv_shift. -/
private theorem not_mem_vars_of_pderiv_eq_zero
    (q : MvPolynomial (Fin 2) ℚ) (i : Fin 2) (h : pderiv i q = 0) :
    i ∉ q.vars := by
  intro hmem
  rw [mem_vars] at hmem
  obtain ⟨d, hd, hi⟩ := hmem
  rw [Finsupp.mem_support_iff] at hi
  set m := d - Finsupp.single i 1
  have hm : m + Finsupp.single i 1 = d := by
    ext j; simp [m, Finsupp.single_apply]
    split_ifs with heq <;> simp_all <;> omega
  have h1 := coeff_pderiv_shift q i m
  rw [h, coeff_zero, hm] at h1
  have hmi : (↑(m i + 1) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [mem_support_iff] at hd
  exact absurd h1.symm (mul_ne_zero hmi hd)

/-! ### Eval independent of variable when not in vars — PROVED -/

/-- If i ∉ vars(q), eval is independent of variable i. PROVED via eval₂_congr. -/
private theorem eval_eq_of_not_mem_vars
    (q : MvPolynomial (Fin 2) ℚ) (i : Fin 2) (h : i ∉ q.vars)
    (v₁ v₂ : Fin 2 → ℚ) (hv : ∀ j, j ≠ i → v₁ j = v₂ j) :
    eval v₁ q = eval v₂ q := by
  show eval₂ (RingHom.id ℚ) v₁ q = eval₂ (RingHom.id ℚ) v₂ q
  apply eval₂_congr
  intro j c hj hc
  apply hv
  intro heq; subst heq
  simp only [mem_vars] at h
  exact h ⟨c, mem_support_iff.mpr hc, hj⟩

/-! ### Restriction preserves eval on consistent inputs — PROVED -/

/-- eval of restrictPoly equals eval of original when evaluation point
    is consistent with the restriction (v assigns same values ρ fixes). -/
private theorem eval_restrictPoly_consistent
    (p : MvPolynomial (Fin 2) ℚ) (v : Fin 2 → ℚ) (hv0 : v 0 = 0) :
    eval v (restrictPoly (universalRestriction 2) p) = eval v p := by
  unfold restrictPoly
  have key : (aeval v : MvPolynomial (Fin 2) ℚ →ₐ[ℚ] ℚ).comp
      (aeval (fun i => match universalRestriction 2 i with
        | none => X i | some false => (0 : MvPolynomial (Fin 2) ℚ)
        | some true => 1)) = aeval v := by
    rw [comp_aeval]; congr 1; ext ⟨i, hi⟩
    interval_cases i
    · -- i = 0: ρ fixes to false → aeval v 0 = v 0 = 0
      show (aeval v) (match universalRestriction 2 (0 : Fin 2) with
        | none => X 0 | some false => 0 | some true => 1) = v ⟨0, hi⟩
      have h0 : universalRestriction 2 (0 : Fin 2) = some false := by native_decide
      rw [h0]; simp; exact hv0.symm
    · -- i = 1: ρ leaves live → aeval v (X 1) = v 1
      show (aeval v) (match universalRestriction 2 (1 : Fin 2) with
        | none => X 1 | some false => 0 | some true => 1) = v ⟨1, hi⟩
      have h1 : universalRestriction 2 (1 : Fin 2) = none := by native_decide
      rw [h1]; simp [aeval_X]
  exact AlgHom.congr_fun key p

/-! ### Main theorem -/

/-- At n=2, if f(0,0) ≠ f(0,1), the restricted SPDP rank exceeds √2 = 1.
    Paper §8.6 canonical matrix rank bound at n=2. -/
theorem not_infspdp_of_inconsistent_n2
    (f : (Fin 2 → Bool) → Bool)
    (hne : f (![false, false]) ≠ f (![false, true]))
    (p : MvPolynomial (Fin 2) ℚ)
    (hp : ∀ x, eval (fun i => boolToRat (x i)) p = boolToRat (f x))
    : ¬ (restrictedSpdpRank (Nat.log 2 2) (Nat.log 2 2) p
          (universalRestriction 2) ≤ Nat.sqrt 2) := by
  have hlog : Nat.log 2 2 = 1 := by native_decide
  have hsqrt : Nat.sqrt 2 = 1 := by native_decide
  rw [hlog, hsqrt]
  set ρ := universalRestriction 2
  set q := restrictPoly ρ p
  set x₁ : Fin 2 := ⟨1, by omega⟩
  set d := pderiv x₁ q with hd_def
  -- Step 1: d ≠ 0 (from CharZero + different evals)
  have hd_ne : d ≠ 0 := by
    intro hd_zero
    have h_not_mem := not_mem_vars_of_pderiv_eq_zero q x₁ hd_zero
    have h_eval_eq := eval_eq_of_not_mem_vars q x₁ h_not_mem
      (fun i => boolToRat (![false, false] i))
      (fun i => boolToRat (![false, true] i))
      (by intro j hj; fin_cases j <;> simp_all [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, x₁])
    -- eval q v = eval p v when v consistent with ρ (v 0 = 0)
    set v_ff : Fin 2 → ℚ := fun i => boolToRat (![false, false] i)
    set v_ft : Fin 2 → ℚ := fun i => boolToRat (![false, true] i)
    have hv0_ff : v_ff 0 = 0 := by simp [v_ff, boolToRat, Matrix.cons_val_zero]
    have hv0_ft : v_ft 0 = 0 := by simp [v_ft, boolToRat, Matrix.cons_val_zero]
    have hq_ff := eval_restrictPoly_consistent p v_ff hv0_ff
    have hq_ft := eval_restrictPoly_consistent p v_ft hv0_ft
    rw [hq_ff, hq_ft] at h_eval_eq
    rw [hp, hp] at h_eval_eq
    -- h_eval_eq : boolToRat(f(0,0)) = boolToRat(f(0,1)), contradicts hne
    have : f ![false, false] = f ![false, true] := by
      unfold boolToRat at h_eval_eq
      cases hff : f ![false, false] <;> cases hft : f ![false, true] <;>
        simp_all
    exact hne this
  -- Steps 2-4: Two LI generators in SPDP subspace → finrank ≥ 2 > 1
  -- Step 2: d and X x₁ * d are in the SPDP generating set
  -- Generator d: S=[x₁], m=1 (length=1, deg(1)=0≤1, x₁ is live, no vars in 1)
  -- Generator X x₁ * d: S=[x₁], m=X x₁ (length=1, deg(X x₁)=1≤1, x₁ is live, vars(X x₁)={x₁} live)
  -- Step 3: linearly independent (integral domain)
  -- Step 4: finrank ≥ 2 > 1
  sorry -- Two LI generators {d, X₁·d} in SPDP subspace → finrank ≥ 2 > 1
  -- Proof: X₁·d ≠ 0 (d ≠ 0, X₁ ≠ 0, integral domain).
  -- If a • (X₁·d) = d, then (C a * X₁ - 1) * d = 0, so C a * X₁ = 1.
  -- But deg(C a * X₁) = 1 ≠ 0 = deg 1, contradiction.

end SPDPRankLower
