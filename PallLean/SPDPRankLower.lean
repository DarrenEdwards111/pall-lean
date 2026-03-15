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
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

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

/-! ### Univariate degree-1 polynomial decomposition — PROVED -/

/-- If s ∉ {0, single x₁ 1} then coeff s m = 0 for m with deg ≤ 1, vars ⊆ {x₁}. -/
private theorem coeff_zero_of_not_in_support (m : MvPolynomial (Fin 2) ℚ) (x₁ : Fin 2) (s : Fin 2 →₀ ℕ)
    (hdeg : m.totalDegree ≤ 1) (hvars : ∀ v ∈ m.vars, v = x₁)
    (hs0 : s ≠ 0) (hs1 : s ≠ Finsupp.single x₁ 1) : coeff s m = 0 := by
  by_contra hc
  have hs_supp : s ∈ m.support := mem_support_iff.mpr hc
  have hs_vars : ∀ v, v ∈ s.support → v = x₁ := by
    intro v hv; apply hvars; rw [mem_vars]; exact ⟨s, hs_supp, hv⟩
  have hs_deg : s.sum (fun _ n => n) ≤ 1 := by
    exact le_trans (Finset.le_sup (f := fun s => s.sum fun _ n => n) hs_supp) hdeg
  have hs_form : s = Finsupp.single x₁ (s x₁) := by
    ext v; simp only [Finsupp.single_apply]
    split_ifs with h
    · exact h ▸ rfl
    · by_contra hne; exact h (hs_vars v (Finsupp.mem_support_iff.mpr hne)).symm
  have hsx1 : s x₁ ≤ 1 := by
    rw [hs_form] at hs_deg; simpa [Finsupp.sum_single_index] using hs_deg
  interval_cases (s x₁)
  · exact hs0 (by rw [hs_form]; simp)
  · exact hs1 (by rw [hs_form])

/-- A polynomial with totalDegree ≤ 1 and vars ⊆ {x₁} decomposes as
    m = C(a₀) + C(a₁) * X x₁. PROVED by ext + support constraint. -/
private theorem poly_deg1_decomp (m : MvPolynomial (Fin 2) ℚ) (x₁ : Fin 2)
    (hdeg : m.totalDegree ≤ 1) (hvars : ∀ v ∈ m.vars, v = x₁) :
    m = C (coeff 0 m) + C (coeff (Finsupp.single x₁ 1) m) * X x₁ := by
  ext s
  simp only [coeff_add, coeff_C, coeff_C_mul, coeff_X', mul_ite, mul_one, mul_zero]
  by_cases hs0 : s = 0
  · subst hs0
    have : Finsupp.single x₁ 1 ≠ (0 : Fin 2 →₀ ℕ) := Finsupp.single_ne_zero.mpr one_ne_zero
    simp [Ne.symm this]
  · by_cases hs1 : s = Finsupp.single x₁ 1
    · subst hs1
      have : (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single x₁ 1 :=
        Ne.symm (Finsupp.single_ne_zero.mpr one_ne_zero)
      simp [this]
    · have hne : ¬(Finsupp.single x₁ 1 = s) := fun h => hs1 h.symm
      have hne0 : ¬(0 = s) := fun h => hs0 h.symm
      simp only [hne0, hne, ↓reduceIte, zero_add, add_zero]
      exact coeff_zero_of_not_in_support m x₁ s hdeg hvars hs0 hs1

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
  -- Step 2: d is in the SPDP generating set (S=[x₁], m=1)
  have x₁_live : x₁ ∈ liveVars ρ := by
    simp [liveVars, ρ, universalRestriction]; native_decide
  set W := Submodule.span ℚ
    { g | ∃ (S : List (Fin 2)) (m : MvPolynomial (Fin 2) ℚ),
        S.length = 1 ∧ m.totalDegree ≤ 1 ∧
        (∀ i ∈ S, i ∈ liveVars ρ) ∧
        (∀ v ∈ m.vars, v ∈ liveVars ρ) ∧
        g = m * iterDerivList S q }
  have hd_in : d ∈ (W : Set (MvPolynomial (Fin 2) ℚ)) := by
    apply Submodule.subset_span
    exact ⟨[x₁], 1, rfl, by simp [totalDegree_one],
      fun i hi => by simp [List.mem_singleton] at hi; rw [hi]; exact x₁_live,
      fun v hv => by simp at hv,
      by simp only [iterDerivList, List.foldl, one_mul]; rfl⟩
  -- Step 2b: X x₁ * d is in the SPDP generating set (S=[x₁], m=X x₁)
  have hXd_in : X x₁ * d ∈ (W : Set (MvPolynomial (Fin 2) ℚ)) := by
    apply Submodule.subset_span
    exact ⟨[x₁], X x₁, rfl, by simp [totalDegree_X],
      fun i hi => by simp [List.mem_singleton] at hi; rw [hi]; exact x₁_live,
      fun v hv => by rw [vars_X] at hv; simp at hv; rw [hv]; exact x₁_live,
      by simp only [iterDerivList, List.foldl]; rfl⟩
  -- Step 3: linear independence via integral domain
  have hli : ∀ (a : ℚ), a • (X x₁ * d) ≠ d := by
    intro a ha
    rw [smul_eq_C_mul] at ha
    have h1 : (C a * X x₁ - 1) * d = 0 := by
      rw [sub_mul, one_mul, mul_assoc]
      exact sub_eq_zero_of_eq ha
    rcases mul_eq_zero.mp h1 with h | h
    · have h3 : C a * X x₁ = 1 := sub_eq_zero.mp h
      by_cases ha0 : a = 0
      · simp [ha0] at h3
      · have htd : totalDegree (C a * X x₁) ≥ 1 := by
          rw [C_mul_X_eq_monomial, totalDegree_monomial]
          · simp [Finsupp.sum_single_index]
          · exact ha0
        rw [h3] at htd; simp [totalDegree_one] at htd
    · exact hd_ne h
  have hXd_ne : X x₁ * d ≠ 0 := mul_ne_zero (X_ne_zero _) hd_ne
  -- Step 4: finrank ≥ 2 > 1
  intro h_le
  -- W is finite-dimensional: every generator is a ℚ-linear combo of {d, X x₁ * d}
  -- (S must be [x₁], m has degree ≤ 1 in x₁ only, so m * d ∈ span{d, X x₁ * d})
  -- Sorry for this finite-dimensionality claim (standard, not on critical path)
  have hW_fin : Module.Finite ℚ W := by
    set W2 := Submodule.span ℚ ({d, X x₁ * d} : Set (MvPolynomial (Fin 2) ℚ))
    have hW2_fin : FiniteDimensional ℚ W2 :=
      Module.Finite.span_of_finite ℚ (Set.toFinite _)
    exact Submodule.finiteDimensional_of_le (show W ≤ W2 from by
      apply Submodule.span_le.mpr
      intro g hg
      obtain ⟨S, m, hlen, hdeg, hS, hm, hgdef⟩ := hg
      subst hgdef
      -- S = [s] for some s. Since s ∈ liveVars and liveVars = {x₁}, s = x₁.
      obtain ⟨s, rfl⟩ : ∃ s, S = [s] := by
        rcases S with _ | ⟨s, t⟩
        · simp at hlen
        · exact ⟨s, by simp at hlen; simp [hlen]⟩
      simp [List.length_singleton] at hlen
      -- s ∈ liveVars, and liveVars = {x₁}
      have hs : s = x₁ := by
        have hmem := hS s (List.mem_singleton.mpr rfl)
        simp [liveVars, ρ, universalRestriction, Finset.mem_filter] at hmem
        fin_cases s
        · exfalso; revert hmem; native_decide
        · rfl
      subst hs
      -- iterDerivList [x₁] q = pderiv x₁ q = d
      simp only [iterDerivList, List.foldl]
      -- m * d ∈ span{d, X x₁ * d}
      -- m = C a + C b * X x₁ (degree ≤ 1, vars ⊆ {x₁})
      -- m has deg ≤ 1 and vars ⊆ {x₁}
      have hm_vars : ∀ v ∈ m.vars, v = x₁ := by
        intro v hv; have hmem := hm v hv; simp [liveVars, ρ, universalRestriction, Finset.mem_filter] at hmem
        fin_cases v
        · exfalso; revert hmem; native_decide
        · rfl
      set a := coeff 0 m
      set b := coeff (Finsupp.single x₁ 1) m
      have hm_eq : m = C a + C b * X x₁ := poly_deg1_decomp m x₁ hdeg hm_vars
      rw [hm_eq, add_mul, mul_assoc, C_mul', C_mul']
      exact Submodule.add_mem _
        (Submodule.smul_mem _ a (Submodule.subset_span (Set.mem_insert _ _)))
        (Submodule.smul_mem _ b (Submodule.subset_span (Set.mem_insert_iff.mpr (Or.inr rfl)))))
  -- Construct LI family of size 2 in W
  have hli2 : LinearIndependent ℚ (fun i : Fin 2 =>
      (⟨![d, X x₁ * d] i, by fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;> assumption⟩ : W)) := by
    rw [linearIndependent_fin2]
    constructor
    · intro h; exact hXd_ne (Subtype.ext_iff.mp h)
    · intro a h; exact hli a (Subtype.ext_iff.mp h)
  have h2 := hli2.fintype_card_le_finrank
  simp [Fintype.card_fin] at h2
  -- h2 : 2 ≤ Module.finrank ℚ W
  -- Need to connect W to restrictedSpdpRank
  -- restrictedSpdpRank 1 1 p ρ = Module.finrank ℚ (Submodule.span ℚ {the same set})
  -- W is definitionally this span
  -- So h_le : Module.finrank ℚ W ≤ 1
  -- restrictedSpdpRank 1 1 p ρ = Module.finrank ℚ W by definition
  unfold restrictedSpdpRank at h_le
  -- h_le should now be: Module.finrank ℚ (Submodule.span ℚ {...}) ≤ 1
  -- h2 : 2 ≤ Module.finrank ℚ W
  -- W is set to exactly this span
  exact absurd (le_trans h2 h_le) (by omega)

end SPDPRankLower
