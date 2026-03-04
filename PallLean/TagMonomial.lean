import PallLean.Tseitin
import Mathlib.Tactic
/-!
# Tag Monomial Property — Pall §9.2

Each clause gadget V_C = (1-ℓ₁)(1-ℓ₂)(1-ℓ₃) has a tag monomial
τ_C = X_{v1}·X_{v2}·X_{v3} with coefficient ±1.
-/

namespace TagMonomial

open MvPolynomial Finsupp Tseitin

variable {σ : Type*} [DecidableEq σ] {F : Type*} [CommRing F] [Nontrivial F]

set_option linter.unusedSimpArgs false

/-! ## Support membership -/

lemma v3_mem_tag (v1 v2 v3 : σ) (h13 : v1 ≠ v3) (h23 : v2 ≠ v3) :
    v3 ∈ (single v1 1 + single v2 1 + single v3 1 : σ →₀ ℕ).support := by
  rw [Finsupp.mem_support_iff]
  simp [Finsupp.add_apply, Finsupp.single_apply, h13.symm, h23.symm]

lemma v2_mem_sum12 (v1 v2 : σ) (h12 : v1 ≠ v2) :
    v2 ∈ (single v1 1 + single v2 1 : σ →₀ ℕ).support := by
  rw [Finsupp.mem_support_iff]
  simp [Finsupp.add_apply, Finsupp.single_apply, h12.symm]

/-! ## Finsupp subtraction -/

lemma tag_sub_v3 (v1 v2 v3 : σ) (h13 : v1 ≠ v3) (h23 : v2 ≠ v3) :
    (single v1 1 + single v2 1 + single v3 1 : σ →₀ ℕ) - single v3 1 =
    single v1 1 + single v2 1 := by
  ext x; simp [Finsupp.add_apply, Finsupp.single_apply, Finsupp.tsub_apply]

lemma sum12_sub_v2 (v1 v2 : σ) (h12 : v1 ≠ v2) :
    (single v1 1 + single v2 1 : σ →₀ ℕ) - single v2 1 = single v1 1 := by
  ext x; simp [Finsupp.add_apply, Finsupp.single_apply, Finsupp.tsub_apply]

/-! ## Coefficient lemmas -/

lemma coeff_X_single (v : σ) :
    coeff (single v 1) (X v : MvPolynomial σ F) = 1 := by
  rw [MvPolynomial.coeff_X']; simp

lemma coeff_one_sub_X_single (v : σ) :
    coeff (single v 1) ((1 : MvPolynomial σ F) - X v) = -1 := by
  rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_one, MvPolynomial.coeff_X']
  simp [show (0 : σ →₀ ℕ) ≠ single v 1 from
    Ne.symm (Finsupp.single_ne_zero.mpr one_ne_zero)]

/-! ## Support and degree of 1 - X v -/

lemma support_one_sub_X (v : σ) :
    ((1 : MvPolynomial σ F) - X v).support ⊆ {0, single v 1} := by
  intro m hm
  have hsub : m ∈ (1 : MvPolynomial σ F).support ∪ (X v : MvPolynomial σ F).support :=
    Finsupp.support_sub hm
  rw [Finset.mem_union] at hsub
  rcases hsub with h1 | hX
  · -- 1 = C 1, support(C 1) = {0}
    classical
    rw [show (1 : MvPolynomial σ F) = C 1 from (map_one _).symm,
        MvPolynomial.support_C, if_neg one_ne_zero, Finset.mem_singleton] at h1
    exact Finset.mem_insert.mpr (Or.inl h1)
  · rw [MvPolynomial.support_X, Finset.mem_singleton] at hX
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr hX))

lemma totalDegree_one_sub_X_le (v : σ) :
    ((1 : MvPolynomial σ F) - X v).totalDegree ≤ 1 := by
  unfold MvPolynomial.totalDegree
  apply Finset.sup_le
  intro m hm
  have hmem := support_one_sub_X (F := F) v hm
  rw [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl
  · simp [Finsupp.sum]
  · simp [Finsupp.sum, Finsupp.support_single_ne_zero _ one_ne_zero,
          Finsupp.single_apply]

/-! ## Degree sum computations -/

/-- ∑ i ∈ (single v1 1 + single v2 1 + single v3 1).support, (single v1 1 + single v2 1 + single v3 1) i = 3 -/
lemma tag_degree_sum (v1 v2 v3 : σ) (h12 : v1 ≠ v2) (h13 : v1 ≠ v3) (h23 : v2 ≠ v3) :
    ∑ i ∈ (single v1 1 + single v2 1 + single v3 1 : σ →₀ ℕ).support,
      (single v1 1 + single v2 1 + single v3 1 : σ →₀ ℕ) i = 3 := by
  change (single v1 1 + single v2 1 + single v3 1 : σ →₀ ℕ).sum (fun _ n => n) = 3
  rw [Finsupp.sum_add_index (by simp) (by intros; ring)]
  rw [Finsupp.sum_add_index (by simp) (by intros; ring)]
  simp [Finsupp.sum_single_index]

/-- ∑ i ∈ (single v1 1 + single v2 1).support, ... = 2 -/
lemma sum12_degree_sum (v1 v2 : σ) (h12 : v1 ≠ v2) :
    ∑ i ∈ (single v1 1 + single v2 1 : σ →₀ ℕ).support,
      (single v1 1 + single v2 1 : σ →₀ ℕ) i = 2 := by
  -- Convert to Finsupp.sum and use sum_add_index
  change (single v1 1 + single v2 1 : σ →₀ ℕ).sum (fun _ n => n) = 2
  rw [Finsupp.sum_add_index (by simp) (by intros; ring)]
  simp [Finsupp.sum_single_index]

/-! ## Zero coefficient by degree -/

lemma coeff_sum12_factor_zero (v1 v2 : σ) (h12 : v1 ≠ v2) (s : Bool) :
    coeff (single v1 1 + single v2 1)
      (if s then (1 : MvPolynomial σ F) - X v1 else X v1) = 0 := by
  apply MvPolynomial.coeff_eq_zero_of_totalDegree_lt
  cases s <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · calc (X v1 : MvPolynomial σ F).totalDegree = 1 := MvPolynomial.totalDegree_X (R := F) (s := v1)
      _ < 2 := by omega
      _ = _ := by rw [← sum12_degree_sum v1 v2 h12]
  · calc ((1 : MvPolynomial σ F) - X v1).totalDegree ≤ 1 := totalDegree_one_sub_X_le v1
      _ < 2 := by omega
      _ = _ := by rw [← sum12_degree_sum v1 v2 h12]

/-! ## Coefficient of single v1 1 in factor -/

lemma coeff_single_factor (v1 : σ) (s1 : Bool) :
    coeff (single v1 1) (if s1 then (1 : MvPolynomial σ F) - X v1 else X v1) =
      if s1 then -1 else 1 := by
  cases s1 <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact coeff_X_single v1
  · exact coeff_one_sub_X_single v1

/-! ## Product coefficient: coeff_sum12_product -/

lemma coeff_sum12_product (v1 v2 : σ) (h12 : v1 ≠ v2) (s1 s2 : Bool) :
    coeff (single v1 1 + single v2 1)
      ((if s1 then (1 : MvPolynomial σ F) - X v1 else X v1) *
       (if s2 then (1 : MvPolynomial σ F) - X v2 else X v2)) =
      (if s1 then (-1 : F) else 1) * (if s2 then -1 else 1) := by
  set f1 := if s1 then (1 : MvPolynomial σ F) - X v1 else X v1
  set m12 := single v1 1 + single v2 1
  cases s2 <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · -- s2 = false: f2 = X v2
    rw [MvPolynomial.coeff_mul_X' (s := v2)]
    rw [if_pos (v2_mem_sum12 v1 v2 h12)]
    rw [sum12_sub_v2 v1 v2 h12]
    simp only [f1, coeff_single_factor, mul_one]
  · -- s2 = true: f2 = 1 - X v2
    -- f1 * (1 - X v2) = f1 - f1 * X v2
    have : f1 * ((1 : MvPolynomial σ F) - X v2) = f1 - f1 * X v2 := by ring
    rw [this, MvPolynomial.coeff_sub]
    rw [MvPolynomial.coeff_mul_X' (s := v2)]
    rw [if_pos (v2_mem_sum12 v1 v2 h12)]
    rw [sum12_sub_v2 v1 v2 h12]
    -- Need: coeff m12 f1 = 0
    have hzero : coeff m12 f1 = 0 := coeff_sum12_factor_zero (F := F) v1 v2 h12 s1
    rw [hzero, coeff_single_factor v1 s1]
    cases s1 <;> simp

/-! ## Main theorem -/

theorem coeff_tag_pm1 (v1 v2 v3 : σ) (h12 : v1 ≠ v2) (h13 : v1 ≠ v3) (h23 : v2 ≠ v3)
    (s1 s2 s3 : Bool) :
    let prod := (if s1 then (1 : MvPolynomial σ F) - X v1 else X v1) *
                (if s2 then (1 : MvPolynomial σ F) - X v2 else X v2) *
                (if s3 then (1 : MvPolynomial σ F) - X v3 else X v3)
    let τ := single v1 1 + single v2 1 + single v3 1
    coeff τ prod = 1 ∨ coeff τ prod = -1 := by
  simp only
  set f1 := if s1 then (1 : MvPolynomial σ F) - X v1 else X v1
  set f2 := if s2 then (1 : MvPolynomial σ F) - X v2 else X v2
  set τ := single v1 1 + single v2 1 + single v3 1
  cases s3 <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · -- s3 = false: f3 = X v3
    rw [MvPolynomial.coeff_mul_X' (s := v3)]
    rw [if_pos (v3_mem_tag v1 v2 v3 h13 h23)]
    rw [tag_sub_v3 v1 v2 v3 h13 h23]
    rw [show f1 * f2 = (if s1 then (1 : MvPolynomial σ F) - X v1 else X v1) *
        (if s2 then (1 : MvPolynomial σ F) - X v2 else X v2) from rfl]
    rw [coeff_sum12_product v1 v2 h12 s1 s2]
    cases s1 <;> cases s2 <;> simp
  · -- s3 = true: f3 = 1 - X v3
    have hmul : f1 * f2 * ((1 : MvPolynomial σ F) - X v3) = f1 * f2 - f1 * f2 * X v3 := by ring
    rw [hmul, MvPolynomial.coeff_sub]
    rw [MvPolynomial.coeff_mul_X' (s := v3)]
    rw [if_pos (v3_mem_tag v1 v2 v3 h13 h23)]
    rw [tag_sub_v3 v1 v2 v3 h13 h23]
    -- coeff τ (f1*f2) = 0 by degree argument
    have hzero : coeff τ (f1 * f2) = 0 := by
      apply MvPolynomial.coeff_eq_zero_of_totalDegree_lt
      have hd1 : f1.totalDegree ≤ 1 := by
        simp only [f1]; cases s1 <;> simp only [Bool.false_eq_true, ↓reduceIte]
        · exact le_of_eq (MvPolynomial.totalDegree_X (R := F) (s := _))
        · exact totalDegree_one_sub_X_le v1
      have hd2 : f2.totalDegree ≤ 1 := by
        simp only [f2]; cases s2 <;> simp only [Bool.false_eq_true, ↓reduceIte]
        · exact le_of_eq (MvPolynomial.totalDegree_X (R := F) (s := _))
        · exact totalDegree_one_sub_X_le v2
      have hprod := MvPolynomial.totalDegree_mul f1 f2
      rw [show τ = single v1 1 + single v2 1 + single v3 1 from rfl]
      rw [tag_degree_sum v1 v2 v3 h12 h13 h23]
      omega
    rw [hzero, zero_sub]
    rw [show f1 * f2 = (if s1 then (1 : MvPolynomial σ F) - X v1 else X v1) *
        (if s2 then (1 : MvPolynomial σ F) - X v2 else X v2) from rfl]
    rw [coeff_sum12_product v1 v2 h12 s1 s2]
    cases s1 <;> cases s2 <;> simp

end TagMonomial
