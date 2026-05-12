import PallLean.Paper93.Paper283.MultilinearCoefficientInfrastructure

/-!
# Atomic factor-pair pderiv helper lemmas for κ=2 Bridge A

This file collects atomic, reusable lemmas about second-order partial
derivatives `pderiv w (pderiv v F)` of the three Cook-Levin factor
shapes used in the κ=2 Bridge A interior-block analysis:

* **bool**:  `1 - X_a (1 - X_a)` (booleanity at index `a`)
* **adj**:   `1 - X_i · X_j` with `i ≠ j` (adjacency)
* **trans**: `1 - c · X_i · X_j` with `i ≠ j` (transition skeleton)

Together with a generic two-fold Leibniz expansion lemma for products
of two factors, these are the atomic building blocks the per-pair
bilinear-coefficient agent will compose to discharge the four
`coeff(probe·, mlProj(∂_{row·} Q_b))` identities.

## Hard rules (from project CLAUDE.md)

* No `sorry`.  No new axioms.

## Lemma families

* **Family A**: second derivatives of `1 - X_a (1 - X_a)`.
* **Family B**: second derivatives of `1 - C c · X_i · X_j`.
* **Family C**: generic two-fold Leibniz expansion.
* **Family D**: two-variable monomial coefficients of `factor * p`.
-/

namespace PallLean.Paper93.Paper283

open MvPolynomial
open PaperFaithfulSeparation
open MultilinearSPDP
open MultilinearCoefficientInfrastructure

attribute [local instance] Classical.dec

namespace BridgeAKappaTwoFactorPairLemmas

/-! ## Family A: second derivatives of `1 - X_a (1 - X_a)` -/

/-- The bool factor `1 - X_a · (1 - X_a)` as an `MvPolynomial`. -/
noncomputable def boolFactorPoly (n : ℕ) (a : Fin n) : MvPolynomial (Fin n) ℚ :=
  (1 : MvPolynomial (Fin n) ℚ) - MvPolynomial.X a * (1 - MvPolynomial.X a)

/-- First partial derivative of the bool factor: `pderiv a (1 - X_a(1-X_a)) = -1 + 2 X_a`. -/
theorem pderiv_one_sub_boolLC_factor_self {n : ℕ} (a : Fin n) :
    MvPolynomial.pderiv a (boolFactorPoly n a) =
      -1 + 2 * MvPolynomial.X a := by
  unfold boolFactorPoly
  rw [map_sub, MvPolynomial.pderiv_one, zero_sub, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_X_self, one_mul, map_sub, MvPolynomial.pderiv_one,
    zero_sub, MvPolynomial.pderiv_X_self]
  ring

/-- First partial derivative of the bool factor at a different variable: zero. -/
theorem pderiv_one_sub_boolLC_factor_of_ne {n : ℕ} (a v : Fin n) (hva : v ≠ a) :
    MvPolynomial.pderiv v (boolFactorPoly n a) = 0 := by
  unfold boolFactorPoly
  -- pderiv v (X_a) = 0 because v ≠ a, so we need a ≠ v: hva.symm
  rw [map_sub, MvPolynomial.pderiv_one, zero_sub, MvPolynomial.pderiv_mul]
  rw [MvPolynomial.pderiv_X_of_ne hva.symm]
  rw [map_sub, MvPolynomial.pderiv_one, MvPolynomial.pderiv_X_of_ne hva.symm,
    sub_self, mul_zero, zero_mul, add_zero, neg_zero]

/-- **Family A, case `v = w = a`**: result is `2`. -/
theorem pderiv_w_pderiv_v_one_sub_boolLC_factor_diag {n : ℕ} (a : Fin n) :
    MvPolynomial.pderiv a (MvPolynomial.pderiv a (boolFactorPoly n a)) =
      (2 : MvPolynomial (Fin n) ℚ) := by
  rw [pderiv_one_sub_boolLC_factor_self a]
  rw [map_add, map_neg, MvPolynomial.pderiv_one, neg_zero, zero_add]
  have h2 : (2 * MvPolynomial.X a : MvPolynomial (Fin n) ℚ) =
      MvPolynomial.C (2 : ℚ) * MvPolynomial.X a := by
    simp [map_ofNat]
  rw [h2, MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X_self]
  simp [map_ofNat]

/-- **Family A, case `v = a, w ≠ a`**: zero. -/
theorem pderiv_w_pderiv_v_one_sub_boolLC_factor_first_eq_diff {n : ℕ}
    (a w : Fin n) (hwa : w ≠ a) :
    MvPolynomial.pderiv w (MvPolynomial.pderiv a (boolFactorPoly n a)) = 0 := by
  rw [pderiv_one_sub_boolLC_factor_self a]
  rw [map_add, map_neg, MvPolynomial.pderiv_one, neg_zero, zero_add]
  have h2 : (2 * MvPolynomial.X a : MvPolynomial (Fin n) ℚ) =
      MvPolynomial.C (2 : ℚ) * MvPolynomial.X a := by
    simp [map_ofNat]
  rw [h2, MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X_of_ne hwa.symm,
    mul_zero]

/-- **Family A, case `v ≠ a`**: zero (inner derivative is zero). -/
theorem pderiv_w_pderiv_v_one_sub_boolLC_factor_first_diff {n : ℕ}
    (a v w : Fin n) (hva : v ≠ a) :
    MvPolynomial.pderiv w (MvPolynomial.pderiv v (boolFactorPoly n a)) = 0 := by
  rw [pderiv_one_sub_boolLC_factor_of_ne a v hva, map_zero]

/-- **Family A, master case-split**: returns `2` if `v = a ∧ w = a`, else `0`. -/
theorem pderiv_w_pderiv_v_one_sub_boolLC_factor {n : ℕ} (a v w : Fin n) :
    MvPolynomial.pderiv w (MvPolynomial.pderiv v (boolFactorPoly n a)) =
      if v = a ∧ w = a then (2 : MvPolynomial (Fin n) ℚ) else 0 := by
  by_cases hva : v = a
  · by_cases hwa : w = a
    · rw [hva, hwa]
      rw [pderiv_w_pderiv_v_one_sub_boolLC_factor_diag a]
      simp [hva, hwa]
    · rw [hva]
      rw [pderiv_w_pderiv_v_one_sub_boolLC_factor_first_eq_diff a w hwa]
      simp [hva, hwa]
  · rw [pderiv_w_pderiv_v_one_sub_boolLC_factor_first_diff a v w hva]
    simp [hva]

/-! ## Family B: second derivatives of `1 - C c · X_i · X_j` (i ≠ j) -/

/-- The cadj factor `1 - C c · X_i · X_j`. -/
noncomputable def cadjFactorPoly {n : ℕ} (c : ℚ) (i j : Fin n) :
    MvPolynomial (Fin n) ℚ :=
  (1 : MvPolynomial (Fin n) ℚ) - MvPolynomial.C c * (MvPolynomial.X i * MvPolynomial.X j)

/-- First derivative of the cadj factor at the first index `i`: `-c X_j`. -/
theorem pderiv_one_sub_C_X_mul_X_at_fst {n : ℕ}
    (c : ℚ) (i j : Fin n) (hij : i ≠ j) :
    MvPolynomial.pderiv i (cadjFactorPoly c i j) =
      -(MvPolynomial.C c * MvPolynomial.X j) := by
  unfold cadjFactorPoly
  rw [map_sub, MvPolynomial.pderiv_one, zero_sub]
  rw [MvPolynomial.pderiv_C_mul]
  rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X_self,
    MvPolynomial.pderiv_X_of_ne hij.symm, mul_zero, add_zero, one_mul]

/-- First derivative of the cadj factor at the second index `j`: `-c X_i`. -/
theorem pderiv_one_sub_C_X_mul_X_at_snd {n : ℕ}
    (c : ℚ) (i j : Fin n) (hij : i ≠ j) :
    MvPolynomial.pderiv j (cadjFactorPoly c i j) =
      -(MvPolynomial.C c * MvPolynomial.X i) := by
  unfold cadjFactorPoly
  rw [map_sub, MvPolynomial.pderiv_one, zero_sub]
  rw [MvPolynomial.pderiv_C_mul]
  rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X_self,
    MvPolynomial.pderiv_X_of_ne hij, zero_mul, zero_add, mul_one]

/-- First derivative of the cadj factor at a non-`{i, j}` index is `0`. -/
theorem pderiv_one_sub_C_X_mul_X_at_other {n : ℕ}
    (c : ℚ) (i j v : Fin n) (hvi : v ≠ i) (hvj : v ≠ j) :
    MvPolynomial.pderiv v (cadjFactorPoly c i j) = 0 := by
  unfold cadjFactorPoly
  rw [map_sub, MvPolynomial.pderiv_one, zero_sub]
  rw [MvPolynomial.pderiv_C_mul]
  -- pderiv v (X i) = 0 needs i ≠ v = hvi.symm; similarly for X j
  rw [MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_X_of_ne hvi.symm,
    MvPolynomial.pderiv_X_of_ne hvj.symm,
    zero_mul, mul_zero, add_zero, mul_zero, neg_zero]

/-- **Family B, case `(v, w) = (i, j)`**: second derivative is `-C c`. -/
theorem pderiv_w_pderiv_v_one_sub_C_X_mul_X_ij {n : ℕ}
    (c : ℚ) (i j : Fin n) (hij : i ≠ j) :
    MvPolynomial.pderiv j (MvPolynomial.pderiv i (cadjFactorPoly c i j)) =
      -(MvPolynomial.C c) := by
  rw [pderiv_one_sub_C_X_mul_X_at_fst c i j hij]
  rw [map_neg, MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X_self, mul_one]

/-- **Family B, case `(v, w) = (j, i)`**: second derivative is `-C c` (symmetric). -/
theorem pderiv_w_pderiv_v_one_sub_C_X_mul_X_ji {n : ℕ}
    (c : ℚ) (i j : Fin n) (hij : i ≠ j) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j (cadjFactorPoly c i j)) =
      -(MvPolynomial.C c) := by
  rw [pderiv_one_sub_C_X_mul_X_at_snd c i j hij]
  rw [map_neg, MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X_self, mul_one]

/-- **Family B, case `v = w = i`**: zero. -/
theorem pderiv_w_pderiv_v_one_sub_C_X_mul_X_ii {n : ℕ}
    (c : ℚ) (i j : Fin n) (hij : i ≠ j) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv i (cadjFactorPoly c i j)) = 0 := by
  rw [pderiv_one_sub_C_X_mul_X_at_fst c i j hij]
  -- pderiv i (X j) = 0 needs j ≠ i = hij.symm
  rw [map_neg, MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X_of_ne hij.symm,
    mul_zero, neg_zero]

/-- **Family B, case `v = w = j`**: zero. -/
theorem pderiv_w_pderiv_v_one_sub_C_X_mul_X_jj {n : ℕ}
    (c : ℚ) (i j : Fin n) (hij : i ≠ j) :
    MvPolynomial.pderiv j (MvPolynomial.pderiv j (cadjFactorPoly c i j)) = 0 := by
  rw [pderiv_one_sub_C_X_mul_X_at_snd c i j hij]
  -- pderiv j (X i) = 0 needs i ≠ j = hij
  rw [map_neg, MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X_of_ne hij,
    mul_zero, neg_zero]

/-- **Family B, case `v = i, w ∉ {i, j}`** (subset case): zero. -/
theorem pderiv_w_pderiv_v_one_sub_C_X_mul_X_subset_first {n : ℕ}
    (c : ℚ) (i j w : Fin n) (hij : i ≠ j) (hwj : w ≠ j) :
    MvPolynomial.pderiv w (MvPolynomial.pderiv i (cadjFactorPoly c i j)) = 0 := by
  rw [pderiv_one_sub_C_X_mul_X_at_fst c i j hij]
  -- pderiv w (X j) = 0 needs j ≠ w = hwj.symm
  rw [map_neg, MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X_of_ne hwj.symm,
    mul_zero, neg_zero]

/-- **Family B, case `v = j, w ∉ {i, j}`** (subset case): zero. -/
theorem pderiv_w_pderiv_v_one_sub_C_X_mul_X_subset_second {n : ℕ}
    (c : ℚ) (i j w : Fin n) (hij : i ≠ j) (hwi : w ≠ i) :
    MvPolynomial.pderiv w (MvPolynomial.pderiv j (cadjFactorPoly c i j)) = 0 := by
  rw [pderiv_one_sub_C_X_mul_X_at_snd c i j hij]
  rw [map_neg, MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X_of_ne hwi.symm,
    mul_zero, neg_zero]

/-- **Family B, case `v ∉ {i, j}`**: inner derivative already zero. -/
theorem pderiv_w_pderiv_v_one_sub_C_X_mul_X_outside {n : ℕ}
    (c : ℚ) (i j v w : Fin n) (hvi : v ≠ i) (hvj : v ≠ j) :
    MvPolynomial.pderiv w (MvPolynomial.pderiv v (cadjFactorPoly c i j)) = 0 := by
  rw [pderiv_one_sub_C_X_mul_X_at_other c i j v hvi hvj, map_zero]

/-- **Family B, master**: full case analysis. -/
theorem pderiv_w_pderiv_v_one_sub_C_X_mul_X {n : ℕ}
    (c : ℚ) (i j v w : Fin n) (hij : i ≠ j) :
    MvPolynomial.pderiv w (MvPolynomial.pderiv v (cadjFactorPoly c i j)) =
      if (v = i ∧ w = j) ∨ (v = j ∧ w = i) then -(MvPolynomial.C c) else 0 := by
  by_cases hvi : v = i
  · by_cases hwj : w = j
    · rw [hvi, hwj]
      rw [pderiv_w_pderiv_v_one_sub_C_X_mul_X_ij c i j hij]
      simp [hvi, hwj]
    · -- v = i, w ≠ j
      have hcase : ¬ ((v = i ∧ w = j) ∨ (v = j ∧ w = i)) := by
        intro h
        rcases h with ⟨_, hw⟩ | ⟨hv2, _⟩
        · exact hwj hw
        · -- v = j and v = i, but i ≠ j
          rw [hvi] at hv2
          exact hij hv2
      rw [if_neg hcase]
      by_cases hwi : w = i
      · -- v = i, w = i, so v = w
        rw [hvi]
        rw [hwi]
        exact pderiv_w_pderiv_v_one_sub_C_X_mul_X_ii c i j hij
      · -- v = i, w ≠ i, w ≠ j
        rw [hvi]
        exact pderiv_w_pderiv_v_one_sub_C_X_mul_X_subset_first c i j w hij hwj
  · by_cases hvj : v = j
    · by_cases hwi : w = i
      · rw [hvj, hwi]
        rw [pderiv_w_pderiv_v_one_sub_C_X_mul_X_ji c i j hij]
        simp [hvj, hwi]
      · have hcase : ¬ ((v = i ∧ w = j) ∨ (v = j ∧ w = i)) := by
          intro h
          rcases h with ⟨hv2, _⟩ | ⟨_, hw⟩
          · exact hvi hv2
          · exact hwi hw
        rw [if_neg hcase]
        by_cases hwj : w = j
        · rw [hvj, hwj]
          exact pderiv_w_pderiv_v_one_sub_C_X_mul_X_jj c i j hij
        · rw [hvj]
          exact pderiv_w_pderiv_v_one_sub_C_X_mul_X_subset_second c i j w hij hwi
    · have hcase : ¬ ((v = i ∧ w = j) ∨ (v = j ∧ w = i)) := by
        intro h
        rcases h with ⟨hv2, _⟩ | ⟨hv2, _⟩
        · exact hvi hv2
        · exact hvj hv2
      rw [if_neg hcase]
      exact pderiv_w_pderiv_v_one_sub_C_X_mul_X_outside c i j v w hvi hvj

/-! ## Family C: two-fold Leibniz expansion -/

/-- **Family C, two-fold Leibniz**: full Leibniz iteration on a product `f * g`. -/
theorem pderiv_w_pderiv_v_factor_pair {n : ℕ}
    (f g : MvPolynomial (Fin n) ℚ) (v w : Fin n) :
    MvPolynomial.pderiv w (MvPolynomial.pderiv v (f * g)) =
      (MvPolynomial.pderiv w (MvPolynomial.pderiv v f)) * g +
      (MvPolynomial.pderiv v f) * (MvPolynomial.pderiv w g) +
      (MvPolynomial.pderiv w f) * (MvPolynomial.pderiv v g) +
      f * (MvPolynomial.pderiv w (MvPolynomial.pderiv v g)) := by
  rw [MvPolynomial.pderiv_mul, map_add]
  rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul]
  ring

/-! ## Family D: two-variable monomial coefficients of `factor * p` -/

/-- **Family D, generic**: bilinear-coefficient extraction. -/
theorem coeff_X_v_X_w_factor_mul_generic {n : ℕ}
    (f p : MvPolynomial (Fin n) ℚ) (v w : Fin n) (hvw : v ≠ w) :
    MvPolynomial.coeff (Finsupp.single v 1 + Finsupp.single w 1) (f * p) =
      MvPolynomial.coeff (Finsupp.single v 1) f *
        MvPolynomial.coeff (Finsupp.single w 1) p +
      MvPolynomial.coeff (Finsupp.single w 1) f *
        MvPolynomial.coeff (Finsupp.single v 1) p +
      MvPolynomial.coeff (Finsupp.single v 1 + Finsupp.single w 1) f *
        MvPolynomial.coeff 0 p +
      MvPolynomial.coeff 0 f *
        MvPolynomial.coeff (Finsupp.single v 1 + Finsupp.single w 1) p :=
  coeff_two_mono_mul v w hvw f p

/-- Bilinear coefficient of the cadj factor at `(v, w)`. -/
theorem coeff_X_v_X_w_cadjFactorPoly {n : ℕ}
    (c : ℚ) (i j v w : Fin n) (hij : i ≠ j) (hvw : v ≠ w) :
    MvPolynomial.coeff (Finsupp.single v 1 + Finsupp.single w 1)
      (cadjFactorPoly c i j) =
      - (if (Finsupp.single i 1 + Finsupp.single j 1 : Fin n →₀ ℕ) =
           Finsupp.single v 1 + Finsupp.single w 1 then c else 0) := by
  unfold cadjFactorPoly
  exact coeff_two_mono_one_sub_C_X_mul_X v w i j hvw hij c

/-- Bilinear coefficient of the bool factor is always `0`. -/
theorem coeff_X_v_X_w_boolFactorPoly {n : ℕ}
    (a v w : Fin n) (hvw : v ≠ w) :
    MvPolynomial.coeff (Finsupp.single v 1 + Finsupp.single w 1)
      (boolFactorPoly n a) = 0 := by
  unfold boolFactorPoly
  have h : (1 : MvPolynomial (Fin n) ℚ) - MvPolynomial.X a * (1 - MvPolynomial.X a) =
      (1 : MvPolynomial (Fin n) ℚ) - (boolLC n a).poly := by
    rw [CompiledBoolFactorBridge.boolConstraint_factor_eq_boolFactor]
    rfl
  rw [h]
  exact coeff_two_mono_boolLC_factor v w a hvw

/-- Constant coefficient of the cadj factor is `1`. -/
theorem coeff_zero_cadjFactorPoly {n : ℕ}
    (c : ℚ) (i j : Fin n) :
    MvPolynomial.coeff 0 (cadjFactorPoly c i j) = 1 := by
  unfold cadjFactorPoly
  rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_one]
  rw [MvPolynomial.coeff_C_mul]
  -- coeff 0 (X i * X j) = 0
  have h : MvPolynomial.coeff (0 : Fin n →₀ ℕ)
      (MvPolynomial.X i * MvPolynomial.X j : MvPolynomial (Fin n) ℚ) = 0 := by
    show MvPolynomial.coeff (0 : Fin n →₀ ℕ)
        (MvPolynomial.monomial (Finsupp.single i 1) (1 : ℚ) *
         MvPolynomial.monomial (Finsupp.single j 1) (1 : ℚ)) = 0
    rw [MvPolynomial.monomial_mul, mul_one, MvPolynomial.coeff_monomial]
    rw [if_neg]
    intro h
    have hi := DFunLike.congr_fun h i
    rw [Finsupp.coe_zero, Pi.zero_apply, Finsupp.add_apply,
      Finsupp.single_apply, if_pos rfl] at hi
    omega
  rw [h, mul_zero, sub_zero, if_pos rfl]

/-- Constant coefficient of the bool factor is `1`. -/
theorem coeff_zero_boolFactorPoly {n : ℕ} (a : Fin n) :
    MvPolynomial.coeff 0 (boolFactorPoly n a) = 1 := by
  unfold boolFactorPoly
  rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_one]
  -- coeff 0 (X a * (1 - X a)) = 0
  have h : MvPolynomial.coeff (0 : Fin n →₀ ℕ)
      (MvPolynomial.X a * (1 - MvPolynomial.X a) : MvPolynomial (Fin n) ℚ) = 0 := by
    rw [mul_sub, mul_one, MvPolynomial.coeff_sub]
    have h1 : MvPolynomial.coeff (0 : Fin n →₀ ℕ)
        (MvPolynomial.X a : MvPolynomial (Fin n) ℚ) = 0 := by
      rw [MvPolynomial.coeff_X', if_neg]
      intro h
      have ha := DFunLike.congr_fun h a
      rw [Finsupp.single_apply, if_pos rfl, Finsupp.coe_zero, Pi.zero_apply] at ha
      omega
    have h2 : MvPolynomial.coeff (0 : Fin n →₀ ℕ)
        (MvPolynomial.X a * MvPolynomial.X a : MvPolynomial (Fin n) ℚ) = 0 := by
      show MvPolynomial.coeff (0 : Fin n →₀ ℕ)
          (MvPolynomial.monomial (Finsupp.single a 1) (1 : ℚ) *
           MvPolynomial.monomial (Finsupp.single a 1) (1 : ℚ)) = 0
      rw [MvPolynomial.monomial_mul, mul_one, MvPolynomial.coeff_monomial]
      rw [if_neg]
      intro h
      have ha := DFunLike.congr_fun h a
      rw [Finsupp.coe_zero, Pi.zero_apply, Finsupp.add_apply,
        Finsupp.single_apply, if_pos rfl] at ha
      omega
    rw [h1, h2, sub_zero]
  rw [h, sub_zero, if_pos rfl]

/-- **Family D, bool factor**: bilinear-coefficient of `(1 - X_a(1-X_a)) * p`. -/
theorem coeff_X_v_X_w_boolFactorPoly_mul {n : ℕ}
    (a v w : Fin n) (p : MvPolynomial (Fin n) ℚ) (hvw : v ≠ w) :
    MvPolynomial.coeff (Finsupp.single v 1 + Finsupp.single w 1)
      (boolFactorPoly n a * p) =
      MvPolynomial.coeff (Finsupp.single v 1) (boolFactorPoly n a) *
        MvPolynomial.coeff (Finsupp.single w 1) p +
      MvPolynomial.coeff (Finsupp.single w 1) (boolFactorPoly n a) *
        MvPolynomial.coeff (Finsupp.single v 1) p +
      MvPolynomial.coeff 0 (boolFactorPoly n a) *
        MvPolynomial.coeff (Finsupp.single v 1 + Finsupp.single w 1) p := by
  rw [coeff_two_mono_mul v w hvw (boolFactorPoly n a) p]
  rw [coeff_X_v_X_w_boolFactorPoly a v w hvw, zero_mul, add_zero]

/-- **Family D, cadj factor**: bilinear-coefficient of `(1 - C c · X_i · X_j) * p`. -/
theorem coeff_X_v_X_w_cadjFactorPoly_mul {n : ℕ}
    (c : ℚ) (i j v w : Fin n) (p : MvPolynomial (Fin n) ℚ)
    (_hij : i ≠ j) (hvw : v ≠ w) :
    MvPolynomial.coeff (Finsupp.single v 1 + Finsupp.single w 1)
      (cadjFactorPoly c i j * p) =
      MvPolynomial.coeff (Finsupp.single v 1) (cadjFactorPoly c i j) *
        MvPolynomial.coeff (Finsupp.single w 1) p +
      MvPolynomial.coeff (Finsupp.single w 1) (cadjFactorPoly c i j) *
        MvPolynomial.coeff (Finsupp.single v 1) p +
      MvPolynomial.coeff (Finsupp.single v 1 + Finsupp.single w 1)
          (cadjFactorPoly c i j) *
        MvPolynomial.coeff 0 p +
      MvPolynomial.coeff 0 (cadjFactorPoly c i j) *
        MvPolynomial.coeff (Finsupp.single v 1 + Finsupp.single w 1) p :=
  coeff_two_mono_mul v w hvw (cadjFactorPoly c i j) p

/-! ## Axiom check -/

#print axioms pderiv_w_pderiv_v_one_sub_boolLC_factor_diag
#print axioms pderiv_w_pderiv_v_one_sub_boolLC_factor
#print axioms pderiv_w_pderiv_v_one_sub_C_X_mul_X_ij
#print axioms pderiv_w_pderiv_v_one_sub_C_X_mul_X
#print axioms pderiv_w_pderiv_v_factor_pair
#print axioms coeff_X_v_X_w_factor_mul_generic
#print axioms coeff_X_v_X_w_boolFactorPoly_mul
#print axioms coeff_X_v_X_w_cadjFactorPoly_mul
#print axioms coeff_X_v_X_w_cadjFactorPoly
#print axioms coeff_X_v_X_w_boolFactorPoly
#print axioms coeff_zero_cadjFactorPoly
#print axioms coeff_zero_boolFactorPoly

end BridgeAKappaTwoFactorPairLemmas

end PallLean.Paper93.Paper283
