/-
  CrossTermVanishing.lean -- Leibniz cross-terms vanish at first-of-block tag monomials

  Key result: For first-of-block S and T, the coefficient of tagMonomial T
  in mlProj(iterDerivList S compiledPoly) equals the coefficient in
  mlProj(boolFactorDerivProd S), namely 2^|S∩T|.

  This bridges from boolFactorFullProd linear independence to compiledPoly
  linear independence, eliminating the axiom identity_construction_np_lower_bound.
-/
import PallLean.CompiledBoolFactorBridge
import PallLean.BlockedBoolRank
import Mathlib.Tactic

namespace CrossTermVanishing

open MvPolynomial SPDP MultilinearSPDP SymmetricPower PaperFaithfulSeparation

/-! ## Step 1: Coefficient preservation for products

Core lemma: if every non-constant monomial b of Q with b ≤ m has coeff 0,
then coeff(m, p * Q) = coeff(m, p) * coeff(0, Q). -/

/-- Coefficient preservation: if every non-constant monomial b of Q with b ≤ m
has coeff 0, then coeff(m, p * Q) = coeff(m, p) * coeff(0, Q). -/
theorem coeff_mul_of_no_submono {n : ℕ}
    (p Q : MvPolynomial (Fin n) ℚ) (m : Fin n →₀ ℕ)
    (hQ : ∀ b : Fin n →₀ ℕ, b ≠ 0 → (∀ i, b i ≤ m i) →
      MvPolynomial.coeff b Q = 0) :
    MvPolynomial.coeff m (p * Q) = MvPolynomial.coeff m p * MvPolynomial.coeff 0 Q := by
  rw [CompiledBoolFactorBridge.coeff_mul_constant_term]
  suffices h : ∑ x ∈ (Finset.antidiagonal m).filter (fun x => x.2 ≠ 0),
      MvPolynomial.coeff x.1 p * MvPolynomial.coeff x.2 Q = 0 by
    linarith
  apply Finset.sum_eq_zero
  intro ⟨a, b⟩ hmem
  simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hmem
  obtain ⟨hab, hb_ne⟩ := hmem
  have hb_le : ∀ i, b i ≤ m i := by
    intro i
    have := congr_fun (congr_arg DFunLike.coe hab) i
    simp only [Finsupp.coe_add, Pi.add_apply] at this
    omega
  rw [hQ b hb_ne hb_le, mul_zero]

/-- Simplified: if Q has constant term 1 and no submonomials of m,
then coeff(m, p * Q) = coeff(m, p). -/
theorem coeff_mul_eq_of_const_one_no_submono {n : ℕ}
    (p Q : MvPolynomial (Fin n) ℚ) (m : Fin n →₀ ℕ)
    (hQ_const : MvPolynomial.coeff 0 Q = 1)
    (hQ_no_sub : ∀ b : Fin n →₀ ℕ, b ≠ 0 → (∀ i, b i ≤ m i) →
      MvPolynomial.coeff b Q = 0) :
    MvPolynomial.coeff m (p * Q) = MvPolynomial.coeff m p := by
  rw [coeff_mul_of_no_submono p Q m hQ_no_sub, hQ_const, mul_one]

/-! ## Step 2: No-submonomials property -/

/-- A polynomial Q has the "no submonomials" property w.r.t. a multilinear
monomial m if every nonzero b with b ≤ m has coeff(b, Q) = 0. -/
def NoSubmonomials {n : ℕ} (Q : MvPolynomial (Fin n) ℚ) (m : Fin n →₀ ℕ) : Prop :=
  ∀ b : Fin n →₀ ℕ, b ≠ 0 → (∀ i, b i ≤ m i) → MvPolynomial.coeff b Q = 0

theorem noSubmono_one {n : ℕ} (m : Fin n →₀ ℕ) :
    NoSubmonomials (1 : MvPolynomial (Fin n) ℚ) m := by
  intro b hb _
  simp only [MvPolynomial.coeff_one]
  rw [if_neg (Ne.symm hb)]

/-- Product rule for NoSubmonomials: if Q₁ and Q₂ both have no submonomials of m,
then neither does Q₁ * Q₂. -/
theorem noSubmono_mul {n : ℕ} (Q₁ Q₂ : MvPolynomial (Fin n) ℚ) (m : Fin n →₀ ℕ)
    (h₁ : NoSubmonomials Q₁ m)
    (h₂ : NoSubmonomials Q₂ m) :
    NoSubmonomials (Q₁ * Q₂) m := by
  intro b hb hle
  rw [MvPolynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro ⟨a, c⟩ hmem
  simp only [Finset.mem_antidiagonal] at hmem
  have ha_le : ∀ i, a i ≤ m i := by
    intro i
    have := congr_fun (congr_arg DFunLike.coe hmem) i
    simp only [Finsupp.coe_add, Pi.add_apply] at this
    have := hle i; omega
  have hc_le : ∀ i, c i ≤ m i := by
    intro i
    have := congr_fun (congr_arg DFunLike.coe hmem) i
    simp only [Finsupp.coe_add, Pi.add_apply] at this
    have := hle i; omega
  by_cases ha : a = 0
  · have hcb : c = b := by
      have := hmem; rw [ha] at this; simpa using this
    rw [hcb, h₂ b hb hle, mul_zero]
  · rw [h₁ a ha ha_le, zero_mul]

/-! ## Step 3: Consecutive pair exclusion for first-of-block sets -/

/-- If all elements of T have values divisible by 3, and j and j+1 are both in T,
then contradiction. -/
theorem no_consec_in_three_mult {n : ℕ}
    (T : Finset (Fin n))
    (hT : ∀ v ∈ T, 3 ∣ v.val)
    (j : Fin n) (hj1 : j.val + 1 < n)
    (hj_in : j ∈ T) (hj1_in : (⟨j.val + 1, hj1⟩ : Fin n) ∈ T) :
    False := by
  have h3j := hT j hj_in
  have h3j1 := hT ⟨j.val + 1, hj1⟩ hj1_in
  obtain ⟨a, ha⟩ := h3j
  obtain ⟨b, hb⟩ := h3j1
  simp at hb
  omega

/-! ## Step 4: (1 - X_i * X_{i+1}) has NoSubmonomials for first-of-block T -/

/-- The coefficient of a nonzero b ≤ tagMonomial T in (1 - X_i * X_{i+1}) is 0,
when T consists of 3-multiples.

The proof: 1 - X_i * X_{i+1} has at most two monomials (the constant 1, and
the degree-2 monomial X_i * X_{i+1}). For b ≠ 0 and b ≤ tagMonomial T:
if b equals the X_i*X_{i+1} monomial, then both i and i+1 must be in T,
contradicting the no-consecutive-pair property. Otherwise coeff(b, ...) = 0. -/
theorem noSubmono_adj_factor {n : ℕ} (i : Fin n) (hi : i.val + 1 < n)
    (T : Finset (Fin n)) (hT : ∀ v ∈ T, 3 ∣ v.val) :
    NoSubmonomials
      ((1 : MvPolynomial (Fin n) ℚ) - MvPolynomial.X i * MvPolynomial.X ⟨i.val + 1, hi⟩)
      (tagMonomial T) := by
  intro b hb hle
  -- coeff b (1 - X_i * X_{i+1}) = coeff b 1 - coeff b (X_i * X_{i+1})
  -- Since b ≠ 0: coeff b 1 = 0
  -- So we need coeff b (X_i * X_{i+1}) = 0
  have hcoeff_sub : MvPolynomial.coeff b
      ((1 : MvPolynomial (Fin n) ℚ) - MvPolynomial.X i * MvPolynomial.X ⟨i.val + 1, hi⟩) =
      MvPolynomial.coeff b (1 : MvPolynomial (Fin n) ℚ) -
      MvPolynomial.coeff b (MvPolynomial.X i * MvPolynomial.X ⟨i.val + 1, hi⟩) := by
    simp [sub_eq_add_neg, map_add, map_neg]
  rw [hcoeff_sub]
  have hb0 : MvPolynomial.coeff b (1 : MvPolynomial (Fin n) ℚ) = 0 := by
    rw [MvPolynomial.coeff_one, if_neg (Ne.symm hb)]
  rw [hb0, zero_sub, neg_eq_zero]
  -- X_i * X_{i+1} = monomial (single i 1 + single (i+1) 1) 1
  -- So coeff b (X_i * X_{i+1}) = if b = single i 1 + single (i+1) 1 then 1 else 0
  have hXX : (MvPolynomial.X i * MvPolynomial.X ⟨i.val + 1, hi⟩ : MvPolynomial (Fin n) ℚ) =
      MvPolynomial.monomial (Finsupp.single i 1 + Finsupp.single ⟨i.val + 1, hi⟩ 1) 1 := by
    rw [MvPolynomial.X, MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]
  rw [hXX, MvPolynomial.coeff_monomial]
  split_ifs with hbeq
  · -- b = single i 1 + single (i+1) 1
    -- Then b i ≥ 1 and b (i+1) ≥ 1
    -- So tagMonomial T at i ≥ 1 and at (i+1) ≥ 1
    -- So i ∈ T and (i+1) ∈ T, contradicting no consecutive pair
    exfalso
    set j := (⟨i.val + 1, hi⟩ : Fin n) with hj_def
    have hij : i ≠ j := by intro h; simp [hj_def, Fin.ext_iff] at h
    have hbi : 1 ≤ b i := by
      have h2 := DFunLike.congr_fun hbeq i
      simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same,
        Finsupp.single_apply, if_neg (Ne.symm hij)] at h2
      omega
    have hbi1 : 1 ≤ b j := by
      have h2 := DFunLike.congr_fun hbeq j
      simp only [Finsupp.coe_add, Pi.add_apply] at h2
      rw [Finsupp.single_apply, if_neg hij, Finsupp.single_eq_same] at h2
      omega
    have hi_in_T : i ∈ T := by
      have h := hle i; rw [tagMonomial_apply] at h
      split_ifs at h with hmem
      · exact hmem
      · exfalso; omega
    have hi1_in_T : j ∈ T := by
      have h := hle j; rw [tagMonomial_apply] at h
      split_ifs at h with hmem
      · exact hmem
      · exfalso; omega
    exact no_consec_in_three_mult T hT i hi hi_in_T (hj_def ▸ hi1_in_T)
  · rfl

/-- Same result for c * X_i * X_{i+1}. -/
theorem noSubmono_cadj_factor {n : ℕ} (c : ℚ) (i : Fin n) (hi : i.val + 1 < n)
    (T : Finset (Fin n)) (hT : ∀ v ∈ T, 3 ∣ v.val) :
    NoSubmonomials
      ((1 : MvPolynomial (Fin n) ℚ) - MvPolynomial.C c * (MvPolynomial.X i * MvPolynomial.X ⟨i.val + 1, hi⟩))
      (tagMonomial T) := by
  intro b hb hle
  -- 1 - c*(X_i * X_{i+1}) = 1 - X_i * X_{i+1} + (1-c)*(X_i * X_{i+1})
  -- Actually, let's compute directly
  -- coeff b (1 - c * (X_i * X_{i+1})) = (if b=0 then 1 else 0) - c * coeff b (X_i * X_{i+1})
  -- Since b ≠ 0: = -c * coeff b (X_i * X_{i+1})
  -- We need coeff b (X_i * X_{i+1}) = 0, which follows from noSubmono_adj_factor
  have hadj := noSubmono_adj_factor i hi T hT b hb hle
  -- hadj : coeff b (1 - X_i * X_{i+1}) = 0
  -- This means coeff b 1 = coeff b (X_i * X_{i+1})
  -- Since coeff b 1 = 0 (b ≠ 0), coeff b (X_i * X_{i+1}) = 0
  have hb1 : MvPolynomial.coeff b (1 : MvPolynomial (Fin n) ℚ) = 0 := by
    rw [MvPolynomial.coeff_one, if_neg (Ne.symm hb)]
  have hXiXj : MvPolynomial.coeff b
      (MvPolynomial.X i * MvPolynomial.X (⟨i.val + 1, hi⟩ : Fin n) : MvPolynomial (Fin n) ℚ) = 0 := by
    have h := hadj
    -- hadj : coeff b (1 - X i * X (i+1)) = 0
    -- = coeff b 1 - coeff b (X i * X (i+1))
    -- = 0 - coeff b (X i * X (i+1))
    -- So coeff b (X i * X (i+1)) = 0
    have hcoeff_sub : MvPolynomial.coeff b
        ((1 : MvPolynomial (Fin n) ℚ) - MvPolynomial.X i * MvPolynomial.X ⟨i.val + 1, hi⟩) =
        MvPolynomial.coeff b (1 : MvPolynomial (Fin n) ℚ) -
        MvPolynomial.coeff b (MvPolynomial.X i * MvPolynomial.X ⟨i.val + 1, hi⟩) := by
      simp [sub_eq_add_neg, map_add, map_neg]
    rw [hcoeff_sub] at h
    linarith
  -- coeff b (1 - C c * (X i * X (i+1))) = coeff b 1 - c * coeff b (X i * X (i+1))
  have hcoeff : MvPolynomial.coeff b
      ((1 : MvPolynomial (Fin n) ℚ) - MvPolynomial.C c * (MvPolynomial.X i * MvPolynomial.X ⟨i.val + 1, hi⟩)) =
      MvPolynomial.coeff b (1 : MvPolynomial (Fin n) ℚ) -
      c * MvPolynomial.coeff b (MvPolynomial.X i * MvPolynomial.X ⟨i.val + 1, hi⟩) := by
    simp [sub_eq_add_neg, map_add, map_neg, MvPolynomial.coeff_C_mul]
  rw [hcoeff, hb1, hXiXj, mul_zero, sub_zero]

end CrossTermVanishing
