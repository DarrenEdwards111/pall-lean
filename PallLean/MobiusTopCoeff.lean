/-
  MobiusTopCoeff.lean -- Proving mobiusL_eq_top_coeff

  Paper reference: §8.6, Codimension-One Lemma.
  Key identity: mobiusL n (evalVec f) = coeff(liveTopMonomial)(restrictPoly ρ (multilinearInterp f))
-/
import PallLean.PneqNP_Defs
import PallLean.ProperSubspaceGeneral
import PallLean.Restriction
import PallLean.UniversalRestriction
import PallLean.BoolEval
import PallLean.Depth4Simulation
import PallLean.RestrictIndicator
import PallLean.MobiusInversion
import Mathlib.Tactic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing

namespace MobiusTopCoeff

open MvPolynomial Restriction BoolEval Depth4Simulation UniversalRestriction
open ProperSubspaceGeneral RestrictIndicator PneqNP_Defs
open Finset

variable {n : ℕ}

/-! ## Coefficient infrastructure -/

lemma coeff_zero_of_var_not {p : MvPolynomial (Fin n) ℚ} {m : (Fin n) →₀ ℕ}
    {j : Fin n} (hj : j ∈ m.support) (hjp : j ∉ p.vars) :
    coeff m p = 0 := by
  by_contra h; exact hjp ((mem_vars j).mpr ⟨m, mem_support_iff.mpr h, hj⟩)

/-! ## Multilinear factor and top monomial -/

noncomputable def mlFactor (i : Fin n) (b : Bool) : MvPolynomial (Fin n) ℚ :=
  if b then X i else 1 - X i

noncomputable def topMon (L : Finset (Fin n)) : (Fin n) →₀ ℕ :=
  ∑ i ∈ L, Finsupp.single i 1

lemma topMon_cons {j : Fin n} {L : Finset (Fin n)} (hj : j ∉ L) :
    topMon (cons j L hj) = topMon L + Finsupp.single j 1 := by
  unfold topMon; rw [sum_cons]; abel

lemma vars_mlFactor (i : Fin n) (b : Bool) : (mlFactor i b).vars ⊆ {i} := by
  unfold mlFactor; cases b with
  | false =>
    calc (1 - X i : MvPolynomial (Fin n) ℚ).vars
        ⊆ (1 : MvPolynomial (Fin n) ℚ).vars ∪ (X i).vars := vars_sub_subset _
      _ = ∅ ∪ {i} := by rw [vars_one, @vars_X ℚ _ i _ _]
      _ = {i} := empty_union _
  | true => simp only [ite_true]; rw [@vars_X ℚ _ i _ _]

lemma vars_prod_mlFactor (L : Finset (Fin n)) (a : Fin n → Bool) :
    (∏ i ∈ L, mlFactor i (a i)).vars ⊆ ↑L := by
  calc (∏ i ∈ L, mlFactor i (a i)).vars
      ⊆ L.biUnion (fun i => (mlFactor i (a i)).vars) := vars_prod _
    _ ⊆ L.biUnion (fun i => ({i} : Finset (Fin n))) :=
        biUnion_mono (fun i _ => vars_mlFactor i (a i))
    _ = ↑L := by ext j; simp

lemma coeff_X_mul (j : Fin n) (m : (Fin n) →₀ ℕ) (p : MvPolynomial (Fin n) ℚ) :
    coeff (m + Finsupp.single j 1) (X j * p) = coeff m p := by
  show coeff (m + Finsupp.single j 1) (monomial (Finsupp.single j 1) (1 : ℚ) * p) = _
  rw [add_comm, coeff_monomial_mul, one_mul]

/-! ## Core: coefficient of top monomial in product of mlFactors -/

theorem coeff_topMon_prod (L : Finset (Fin n)) (a : Fin n → Bool) :
    coeff (topMon L) (∏ i ∈ L, mlFactor i (a i)) =
    (-1 : ℚ) ^ (L.filter (fun i => a i = false)).card := by
  induction L using cons_induction with
  | empty => simp [topMon, prod_empty, coeff_one]
  | cons j L hj ih =>
    rw [prod_cons, topMon_cons hj]
    set p := ∏ i ∈ L, mlFactor i (a i)
    have hpv : p.vars ⊆ ↑L := vars_prod_mlFactor L a
    cases haj : a j with
    | true =>
      show coeff (topMon L + Finsupp.single j 1) (mlFactor j true * p) = _
      unfold mlFactor; rw [if_pos rfl, coeff_X_mul, ih, filter_cons, if_neg (by rw [haj]; decide)]
    | false =>
      show coeff (topMon L + Finsupp.single j 1) (mlFactor j false * p) = _
      unfold mlFactor; rw [if_neg Bool.false_ne_true]
      have h1 : (1 - X j : MvPolynomial (Fin n) ℚ) * p = p - X j * p := by ring
      rw [h1, MvPolynomial.coeff_sub]
      have h_zero : coeff (topMon L + Finsupp.single j 1) p = 0 :=
        coeff_zero_of_var_not
          (by rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply, if_pos rfl]; omega)
          (fun habs => hj (mem_coe.mp (hpv habs)))
      rw [h_zero, coeff_X_mul, zero_sub, ih, filter_cons, if_pos haj, card_cons, pow_succ]; ring

/-! ## Inconsistent → restricted indicator = 0 -/

theorem restrictPoly_boolIndicator_inconsistent' (ρ : Restriction.Restriction n)
    (a : Fin n → Bool) (h : ∃ i b, ρ i = some b ∧ a i ≠ b) :
    restrictPoly ρ (boolIndicator a) = 0 := by
  obtain ⟨i, b, hρ, ha⟩ := h
  unfold boolIndicator; rw [restrictPoly_prod]
  apply prod_eq_zero (mem_univ i)
  cases hai : a i <;> cases hb : b <;> simp_all [restrictPoly_X, restrictPoly_one_sub_X]

/-! ## Consistent → product over live vars -/

lemma boolIndicator_eq_prod_mlFactor (a : Fin n → Bool) :
    boolIndicator a = ∏ i : Fin n, mlFactor i (a i) := by
  unfold boolIndicator mlFactor; rfl

theorem restrictPoly_boolIndicator_consistent' (ρ : Restriction.Restriction n)
    (a : Fin n → Bool) (hcons : ∀ i b, ρ i = some b → a i = b) :
    restrictPoly ρ (boolIndicator a) = ∏ i ∈ liveVars ρ, mlFactor i (a i) := by
  rw [boolIndicator_eq_prod_mlFactor, restrictPoly_prod]
  -- Split product: fixed vars contribute 1, live vars contribute mlFactor
  -- Use: ∏_{univ} = ∏_{fixed} * ∏_{live}
  -- where fixed = {i | ρ i ≠ none}, live = liveVars ρ = {i | ρ i = none}
  have h_eq : ∀ i : Fin n, i ∈ liveVars ρ →
      restrictPoly ρ (mlFactor i (a i)) = mlFactor i (a i) := by
    intro i hi; simp [liveVars, mem_filter] at hi
    show restrictPoly ρ (if a i then X i else 1 - X i) = if a i then X i else 1 - X i
    split <;> (first | rw [restrictPoly_X, hi] | rw [restrictPoly_one_sub_X, hi])
  have h_one : ∀ i : Fin n, i ∉ liveVars ρ →
      restrictPoly ρ (mlFactor i (a i)) = 1 := by
    intro i hi; simp [liveVars, mem_filter] at hi
    obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hi
    have hab := hcons i b hb
    show restrictPoly ρ (if a i then X i else 1 - X i) = 1
    rw [hab]
    revert hb; cases b <;> intro hb <;> simp [restrictPoly_one_sub_X, restrictPoly_X, hb]
  -- Transform: ∏_{univ} restrictPoly ρ (mlFactor i (a i)) = ∏_{liveVars} mlFactor i (a i)
  -- by showing non-live factors are 1 and live factors are preserved
  conv_lhs =>
    arg 2; ext i
    rw [show restrictPoly ρ (mlFactor i (a i)) =
      if i ∈ liveVars ρ then mlFactor i (a i) else 1
      from by split_ifs with h <;> [exact h_eq i h; exact h_one i h]]
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one]
  congr 1; ext i; simp

/-! ## Exponent matching -/

lemma liveVars_filter_false_card (ρ : Restriction.Restriction n) (a : Fin n → Bool) :
    (liveVars ρ).card - ((liveVars ρ).filter (fun i => a i = true)).card =
    ((liveVars ρ).filter (fun i => a i = false)).card := by
  have hunion : (liveVars ρ).filter (fun i => a i = true) ∪
         (liveVars ρ).filter (fun i => a i = false) = liveVars ρ := by
    ext i; simp only [mem_union, mem_filter]; constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h; rcases Bool.eq_false_or_eq_true (a i) with ha | ha <;> simp [h, ha]
  have hdisj : Disjoint ((liveVars ρ).filter (fun i => a i = true))
      ((liveVars ρ).filter (fun i => a i = false)) := by
    rw [disjoint_filter]; intro i _ ht hf; rw [ht] at hf; exact Bool.noConfusion hf
  have hcard := card_union_of_disjoint hdisj
  rw [hunion] at hcard; omega

lemma w_sub_liveTrue_eq (a : Fin n → Bool) :
    w n - liveTrue n a =
    ((liveVars (universalRestriction n)).filter (fun i => a i = false)).card := by
  unfold w liveTrue
  have h_eq : (univ.filter (fun i : Fin n =>
    (universalRestriction n) i = none ∧ a i = true)) =
    (liveVars (universalRestriction n)).filter (fun i => a i = true) := by
    ext i; simp [mem_filter, mem_univ, liveVars]
  rw [h_eq]
  exact liveVars_filter_false_card (universalRestriction n) a

/-! ## Main theorem -/

/-- Helper: coeff of topMon in restricted multilinearInterp via linearity. -/
private lemma coeff_topMon_restricted_multilinearInterp (f : BoolFun n) :
    coeff (topMon (liveVars (universalRestriction n)))
      (restrictPoly (universalRestriction n) (multilinearInterp f)) =
    ∑ a : Fin n → Bool,
      if f a = true then
        coeff (topMon (liveVars (universalRestriction n)))
          (restrictPoly (universalRestriction n) (boolIndicator a))
      else 0 := by
  unfold multilinearInterp restrictPoly
  rw [map_sum]  -- distribute aeval over the sum
  rw [show coeff (topMon (liveVars (universalRestriction n)))
    (∑ a ∈ univ.filter (fun a => f a), _) =
    ∑ a ∈ univ.filter (fun a => f a),
      coeff (topMon (liveVars (universalRestriction n))) _
    from map_sum (MvPolynomial.coeffAddMonoidHom _) _ _]
  rw [sum_filter]

/-- Helper: per-boolIndicator coefficient. -/
private lemma coeff_per_indicator (a : Fin n → Bool) :
    coeff (topMon (liveVars (universalRestriction n)))
      (restrictPoly (universalRestriction n) (boolIndicator a)) =
    if isConsistent n a
    then (-1 : ℚ) ^ ((liveVars (universalRestriction n)).filter (fun i => a i = false)).card
    else 0 := by
  split_ifs with hc
  · rw [restrictPoly_boolIndicator_consistent' _ a hc]
    exact coeff_topMon_prod _ a
  · -- hc : ¬isConsistent n a, i.e., ∃ i b, ρ i = some b ∧ a i ≠ b
    change ¬(∀ i b, (universalRestriction n) i = some b → a i = b) at hc
    push_neg at hc; obtain ⟨i, b, hρ, hab⟩ := hc
    rw [restrictPoly_boolIndicator_inconsistent' _ a ⟨i, b, hρ, hab⟩]; simp [coeff_zero]

theorem mobiusL_eq_top_coeff_proved (n : ℕ) (hn : n ≥ 2) (f : BoolFun n) :
    mobiusL n (evalVec f) =
    coeff (topMon (liveVars (universalRestriction n)))
      (restrictPoly (universalRestriction n) (multilinearInterp f)) := by
  rw [coeff_topMon_restricted_multilinearInterp]
  -- Expand mobiusL
  unfold mobiusL; simp only [LinearMap.coe_mk, AddHom.coe_mk]
  congr 1; ext a
  rw [coeff_per_indicator]
  by_cases hc : isConsistent n a <;> by_cases hf : f a = true
  · -- consistent, f = true
    simp only [if_pos hc, if_pos hf]
    unfold evalVec boolToRat; simp [hf, w_sub_liveTrue_eq]
  · -- consistent, f = false
    have hf' : ¬(f a = true) := hf
    simp only [if_pos hc, if_neg hf']
    unfold evalVec boolToRat
    have hfa : f a = false := Bool.eq_false_iff.mpr hf
    rw [hfa]; simp
  · -- inconsistent, f = true
    simp only [if_neg hc, if_pos hf]
  · -- inconsistent, f = false
    simp only [if_neg hc, if_neg hf]

end MobiusTopCoeff
