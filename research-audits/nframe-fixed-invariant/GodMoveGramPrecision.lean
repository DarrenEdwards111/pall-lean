import GodMoveRationalRowBasis
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Lemmas

/-!
# Integer Gram relations with bounded coefficient magnitude

For an explicitly supplied 0/1 row matrix `R`, form `G = R Rᵀ` and
`D = det(G) I - Rᵀ adj(G) R`. The entries of `D` are integers bounded by
`(r²+1) r! (s+1)^r` for `r` rows and `s` columns. For independent rows,
the rational kernel of `D` is exactly the span of the original rows.

If a numeric row basis spans those rows, its actual residual coefficients
are entries of `D` divided by `det(G)`. Their canonical numerator and
denominator each have at most `2 * (s+1)^2 + 1` magnitude bits. The companion
`GodMoveGramSamplePrecision` discharges the independent-basis premise for
arbitrary actual sample lists.

The determinant formulas are finite executable definitions. No runtime bound
for computing determinants by these definitions is claimed, and a supplied
independent 0/1 matrix is not identified with an algorithm state by definition.
-/

namespace GodMoveGramPrecision

open scoped BigOperators Matrix

def gram {K : Type*} [CommRing K] {r s : ℕ} (R : Matrix (Fin r) (Fin s) K) :
    Matrix (Fin r) (Fin r) K := R * Rᵀ

def relationMatrix {K : Type*} [CommRing K] {r s : ℕ} (R : Matrix (Fin r) (Fin s) K) :
    Matrix (Fin s) (Fin s) K :=
  (gram R).det • 1 - Rᵀ * (gram R).adjugate * R

def BooleanEntries {r s : ℕ} (R : Matrix (Fin r) (Fin s) ℤ) : Prop :=
  ∀ i j, R i j = 0 ∨ R i j = 1

def coefficientBound (r s : ℕ) : ℕ := (r * r + 1) * r.factorial * (s + 1) ^ r

theorem boolean_entry_abs_le {r s : ℕ} (R : Matrix (Fin r) (Fin s) ℤ)
    (hR : BooleanEntries R) (i : Fin r) (j : Fin s) : |R i j| ≤ 1 := by
  rcases hR i j with h | h <;> simp [h]

theorem mul_entry_abs_le {r s t : ℕ} (A : Matrix (Fin r) (Fin s) ℤ)
    (B : Matrix (Fin s) (Fin t) ℤ) (a b : ℕ)
    (hA : ∀ i j, |A i j| ≤ a) (hB : ∀ i j, |B i j| ≤ b)
    (i : Fin r) (j : Fin t) : |(A * B) i j| ≤ (s * a * b : ℕ) := by
  rw [Matrix.mul_apply]
  calc
    |∑ k : Fin s, A i k * B k j| ≤ ∑ k : Fin s, |A i k * B k j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin s, (a : ℤ) * b := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      exact mul_le_mul (hA i k) (hB k j) (abs_nonneg _) (by positivity)
    _ = (s * a * b : ℕ) := by simp; ring

theorem gram_entry_abs_le {r s : ℕ} (R : Matrix (Fin r) (Fin s) ℤ)
    (hR : BooleanEntries R) (i j : Fin r) : |gram R i j| ≤ (s : ℤ) := by
  have h := mul_entry_abs_le R Rᵀ 1 1 (boolean_entry_abs_le R hR)
    (fun i j => boolean_entry_abs_le R hR j i) i j
  simpa [gram] using h

theorem det_abs_le {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (b : ℕ)
    (hA : ∀ i j, |A i j| ≤ b) : |A.det| ≤ (r.factorial * b ^ r : ℕ) := by
  have h := Matrix.det_le (A := A) (abv := (AbsoluteValue.abs : AbsoluteValue ℤ ℤ)) hA
  simpa using h

theorem gram_det_abs_le {r s : ℕ} (R : Matrix (Fin r) (Fin s) ℤ)
    (hR : BooleanEntries R) : |(gram R).det| ≤ (r.factorial * (s + 1) ^ r : ℕ) := by
  apply det_abs_le
  intro i j
  have h := gram_entry_abs_le R hR i j
  exact h.trans (by omega)

theorem gram_adjugate_abs_le {r s : ℕ} (R : Matrix (Fin r) (Fin s) ℤ)
    (hR : BooleanEntries R) (i j : Fin r) :
    |(gram R).adjugate i j| ≤ (r.factorial * (s + 1) ^ r : ℕ) := by
  rw [Matrix.adjugate_apply]
  apply det_abs_le
  intro k l
  by_cases hk : k = j
  · subst k
    simp only [Matrix.updateRow_self, Pi.single_apply]
    split
    · simp
    · simp only [abs_zero]; omega
  · rw [Matrix.updateRow_ne hk]
    exact (gram_entry_abs_le R hR k l).trans (by omega)

/-- A proved coefficient bound for the explicitly constructed integer
relations; the bound is derived entirely from the 0/1 entries. -/
theorem relationMatrix_entry_abs_le {r s : ℕ} (R : Matrix (Fin r) (Fin s) ℤ)
    (hR : BooleanEntries R) (i j : Fin s) :
    |relationMatrix R i j| ≤ (coefficientBound r s : ℤ) := by
  let b := r.factorial * (s + 1) ^ r
  have hdet : |(gram R).det| ≤ (b : ℤ) := gram_det_abs_le R hR
  have hleft : ∀ i j, |(Rᵀ * (gram R).adjugate) i j| ≤ (r * b : ℕ) := by
    intro i j
    simpa using mul_entry_abs_le Rᵀ (gram R).adjugate 1 b
      (fun i j => boolean_entry_abs_le R hR j i) (gram_adjugate_abs_le R hR) i j
  have hright : |(Rᵀ * (gram R).adjugate * R) i j| ≤ (r * (r * b) : ℕ) := by
    simpa using mul_entry_abs_le (Rᵀ * (gram R).adjugate) R (r * b) 1
      hleft (boolean_entry_abs_le R hR) i j
  have hdiag : |((gram R).det • (1 : Matrix (Fin s) (Fin s) ℤ)) i j| ≤ (b : ℤ) := by
    by_cases hij : i = j
    · simpa [Matrix.smul_apply, Matrix.one_apply, hij] using hdet
    · simp [Matrix.smul_apply, hij]
  change |((gram R).det • (1 : Matrix (Fin s) (Fin s) ℤ)) i j -
    (Rᵀ * (gram R).adjugate * R) i j| ≤ _
  calc
    _ ≤ |((gram R).det • (1 : Matrix (Fin s) (Fin s) ℤ)) i j| +
        |(Rᵀ * (gram R).adjugate * R) i j| := abs_sub _ _
    _ ≤ (b : ℤ) + (r * (r * b) : ℕ) := add_le_add hdiag hright
    _ = (coefficientBound r s : ℤ) := by simp [coefficientBound, b]; ring

theorem gram_det_ne_zero {r s : ℕ} (R : Matrix (Fin r) (Fin s) ℚ)
    (hR : LinearIndependent ℚ R) : (gram R).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hzero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hker := Matrix.ker_mulVecLin_transpose_mul_self Rᵀ
  have hmem : v ∈ LinearMap.ker (Rᵀᵀ * Rᵀ).mulVecLin := by
    simpa only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.transpose_transpose] using hzero
  rw [hker] at hmem
  change Rᵀ *ᵥ v = 0 at hmem
  rw [Matrix.mulVec_transpose, Matrix.vecMul_eq_sum] at hmem
  exact hv (funext ((Fintype.linearIndependent_iff.mp hR) v hmem))

theorem relationMatrix_mul_transpose {K : Type*} [CommRing K] {r s : ℕ}
    (R : Matrix (Fin r) (Fin s) K) : relationMatrix R * Rᵀ = 0 := by
  calc
    relationMatrix R * Rᵀ =
        (gram R).det • Rᵀ - Rᵀ * ((gram R).adjugate * gram R) := by
      simp only [relationMatrix, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul,
        Matrix.mul_assoc, gram]
    _ = 0 := by rw [Matrix.adjugate_mul]; simp

theorem transpose_mulVec_mem_span {r s : ℕ} (R : Matrix (Fin r) (Fin s) ℚ)
    (v : Fin r → ℚ) : Rᵀ *ᵥ v ∈ Submodule.span ℚ (Set.range R) := by
  rw [Matrix.mulVec_transpose, Matrix.vecMul_eq_sum]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- Independent original rows suffice to identify the exact kernel of the
explicit Gram relation matrix. -/
theorem relationMatrix_mulVec_eq_zero_iff {r s : ℕ} (R : Matrix (Fin r) (Fin s) ℚ)
    (hR : LinearIndependent ℚ R) (v : Fin s → ℚ) :
    relationMatrix R *ᵥ v = 0 ↔ v ∈ Submodule.span ℚ (Set.range R) := by
  constructor
  · intro hzero
    have hd := gram_det_ne_zero R hR
    have heq : (gram R).det • v = Rᵀ *ᵥ ((gram R).adjugate *ᵥ (R *ᵥ v)) := by
      simpa only [relationMatrix, Matrix.sub_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec, ← Matrix.mulVec_mulVec, sub_eq_zero] using hzero
    have hmem := transpose_mulVec_mem_span R ((gram R).adjugate *ᵥ (R *ᵥ v))
    rw [← heq] at hmem
    have hscaled := Submodule.smul_mem (Submodule.span ℚ (Set.range R)) (gram R).det⁻¹ hmem
    simpa only [smul_smul, inv_mul_cancel₀ hd, one_smul] using hscaled
  · intro hv
    obtain ⟨coeff, hcoeff⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hv
    rw [← hcoeff, ← Matrix.vecMul_eq_sum, ← Matrix.mulVec_transpose,
      Matrix.mulVec_mulVec, relationMatrix_mul_transpose, Matrix.zero_mulVec]

def rationalMatrix {r s : ℕ} (R : Matrix (Fin r) (Fin s) ℤ) : Matrix (Fin r) (Fin s) ℚ :=
  R.map (Int.castRingHom ℚ)

theorem rationalMatrix_gram {r s : ℕ} (R : Matrix (Fin r) (Fin s) ℤ) :
    rationalMatrix (gram R) = gram (rationalMatrix R) := by
  ext i j
  simp [rationalMatrix, gram, Matrix.mul_apply]

theorem rationalMatrix_relation {r s : ℕ} (R : Matrix (Fin r) (Fin s) ℤ) :
    rationalMatrix (relationMatrix R) = relationMatrix (rationalMatrix R) := by
  have hdet : ((gram R).det : ℚ) = (gram (rationalMatrix R)).det := by
    exact ((Int.castRingHom ℚ).map_det (gram R)).trans (congrArg Matrix.det (rationalMatrix_gram R))
  have hadj : rationalMatrix (gram R).adjugate = (gram (rationalMatrix R)).adjugate := by
    exact ((Int.castRingHom ℚ).map_adjugate (gram R)).trans
      (congrArg Matrix.adjugate (rationalMatrix_gram R))
  ext i j
  simp only [rationalMatrix, Matrix.map_apply, relationMatrix, Matrix.sub_apply,
    map_sub, Matrix.smul_apply, smul_eq_mul, map_mul,
    Matrix.mul_apply, map_sum, Matrix.transpose_apply]
  simp only [Int.coe_castRingHom, hdet]
  have hone : ((1 : Matrix (Fin s) (Fin s) ℤ) i j : ℚ) =
      (1 : Matrix (Fin s) (Fin s) ℚ) i j := by simp [Matrix.one_apply]
  rw [hone]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  congr 1
  exact congrFun (congrFun hadj l) k

/-- The bounded integer coefficients define precisely the desired rational
row-span test; no rank or precision premise is assumed. -/
theorem integer_relations_eq_zero_iff {r s : ℕ} (R : Matrix (Fin r) (Fin s) ℤ)
    (hR : LinearIndependent ℚ (rationalMatrix R)) (v : Fin s → ℚ) :
    rationalMatrix (relationMatrix R) *ᵥ v = 0 ↔
      v ∈ Submodule.span ℚ (Set.range (rationalMatrix R)) := by
  rw [rationalMatrix_relation]
  exact relationMatrix_mulVec_eq_zero_iff (rationalMatrix R) hR v

theorem coefficientBound_le_pow (r s : ℕ) (hrs : r ≤ s) :
    coefficientBound r s ≤ (s + 1) ^ (2 * r + 2) := by
  have hquad : r * r + 1 ≤ (s + 1) ^ 2 := by nlinarith
  have hfac : r.factorial ≤ (s + 1) ^ r :=
    (Nat.factorial_le_pow r).trans (Nat.pow_le_pow_left (by omega) r)
  calc
    coefficientBound r s ≤ (s + 1) ^ 2 * (s + 1) ^ r * (s + 1) ^ r :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul hquad hfac)
    _ = (s + 1) ^ (2 * r + 2) := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega

theorem coefficientBound_le_two_pow (r s : ℕ) (hrs : r ≤ s) :
    coefficientBound r s ≤ 2 ^ (2 * (s + 1) ^ 2) := by
  calc
    coefficientBound r s ≤ (s + 1) ^ (2 * r + 2) := coefficientBound_le_pow r s hrs
    _ ≤ (2 ^ (s + 1)) ^ (2 * r + 2) :=
      Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_two_pow_self (n := s + 1))) _
    _ = 2 ^ ((s + 1) * (2 * r + 2)) := (pow_mul _ _ _).symm
    _ ≤ 2 ^ (2 * (s + 1) ^ 2) := Nat.pow_le_pow_right (by omega) (by nlinarith)

/-- Each signed integer relation coefficient needs at most this quadratic
number of magnitude bits; a separate sign bit suffices for its sign. -/
theorem relationMatrix_entry_size_le {r s : ℕ} (R : Matrix (Fin r) (Fin s) ℤ)
    (hR : BooleanEntries R) (hrs : r ≤ s) (i j : Fin s) :
    (relationMatrix R i j).natAbs.size ≤ 2 * (s + 1) ^ 2 + 1 := by
  have habs := relationMatrix_entry_abs_le R hR i j
  have hnat : (relationMatrix R i j).natAbs ≤ coefficientBound r s := by
    rw [← Int.natCast_natAbs] at habs
    exact_mod_cast habs
  apply Nat.size_le.mpr
  apply (hnat.trans (coefficientBound_le_two_pow r s hrs)).trans_lt
  exact Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _)

/-- The row-count premise in the quadratic precision theorem follows from
the same independent-basis condition needed for correctness. -/
theorem independent_relationMatrix_entry_size_le {r s : ℕ}
    (R : Matrix (Fin r) (Fin s) ℤ) (hR : BooleanEntries R)
    (hLI : LinearIndependent ℚ (rationalMatrix R)) (i j : Fin s) :
    (relationMatrix R i j).natAbs.size ≤ 2 * (s + 1) ^ 2 + 1 := by
  apply relationMatrix_entry_size_le R hR
  have h := hLI.fintype_card_le_finrank
  simpa [Module.finrank_fintype_fun_eq_card] using h

theorem relationMatrix_mulVec_eq_scaled_residual {r s : ℕ}
    (R : Matrix (Fin r) (Fin s) ℚ) (hR : LinearIndependent ℚ R)
    (B : GodMoveRationalRowBasis.RowBasis s)
    (hspan : GodMoveRationalRowBasis.rowSpan B = Submodule.span ℚ (Set.range R))
    (v : Fin s → ℚ) :
    relationMatrix R *ᵥ v = (gram R).det • GodMoveRationalRowBasis.residual B v := by
  have horth : R *ᵥ GodMoveRationalRowBasis.residual B v = 0 := by
    funext i
    have hmem : R i ∈ GodMoveRationalRowBasis.rowSpan B := by
      rw [hspan]
      exact Submodule.subset_span ⟨i, rfl⟩
    have h := GodMoveRationalRowBasis.residual_orthogonal_span B v (R i) hmem
    change dotProduct (R i) (GodMoveRationalRowBasis.residual B v) = 0
    simpa only [GodMoveRationalRowBasis.dot, dotProduct_comm] using h
  have hproj : relationMatrix R *ᵥ GodMoveRationalRowBasis.projected B v = 0 := by
    apply (relationMatrix_mulVec_eq_zero_iff R hR _).mpr
    rw [← hspan]
    exact GodMoveRationalRowBasis.projected_mem B v
  have hleft : relationMatrix R *ᵥ GodMoveRationalRowBasis.residual B v =
      relationMatrix R *ᵥ v := by
    rw [GodMoveRationalRowBasis.residual, Matrix.mulVec_sub, hproj, sub_zero]
  rw [← hleft]
  simp only [relationMatrix, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    ← Matrix.mulVec_mulVec, horth, Matrix.mulVec_zero, sub_zero]

theorem gram_det_cast {r s : ℕ} (R : Matrix (Fin r) (Fin s) ℤ) :
    ((gram R).det : ℚ) = (gram (rationalMatrix R)).det :=
  ((Int.castRingHom ℚ).map_det (gram R)).trans (congrArg Matrix.det (rationalMatrix_gram R))

theorem gram_int_det_ne_zero {r s : ℕ} (R : Matrix (Fin r) (Fin s) ℤ)
    (hR : LinearIndependent ℚ (rationalMatrix R)) : (gram R).det ≠ 0 := by
  intro hzero
  have hcast := gram_det_cast R
  rw [hzero, Int.cast_zero] at hcast
  exact gram_det_ne_zero (rationalMatrix R) hR hcast.symm

/-- The actual rational residual operator agrees with the explicit integer
relation matrix divided by its nonzero Gram determinant. -/
theorem residual_coordinate_eq_int_ratio {r s : ℕ} (R : Matrix (Fin r) (Fin s) ℤ)
    (hR : LinearIndependent ℚ (rationalMatrix R))
    (B : GodMoveRationalRowBasis.RowBasis s)
    (hspan : GodMoveRationalRowBasis.rowSpan B =
      Submodule.span ℚ (Set.range (rationalMatrix R))) (i j : Fin s) :
    GodMoveRationalRowBasis.residual B (Pi.single i 1) j =
      (relationMatrix R j i : ℚ) / (gram R).det := by
  have h := relationMatrix_mulVec_eq_scaled_residual (rationalMatrix R) hR B hspan
    (Pi.single i 1)
  rw [← rationalMatrix_relation, ← gram_det_cast, Matrix.mulVec_single_one] at h
  have hc := congrFun h j
  change (relationMatrix R j i : ℚ) =
    ((gram R).det : ℚ) * GodMoveRationalRowBasis.residual B (Pi.single i 1) j at hc
  apply (eq_div_iff (by exact_mod_cast gram_int_det_ne_zero R hR)).mpr
  simpa only [mul_comm] using hc.symm

theorem rat_ratio_num_den_le (n d : ℤ) (hd : d ≠ 0) :
    ((n : ℚ) / d).num.natAbs ≤ n.natAbs ∧ ((n : ℚ) / d).den ≤ d.natAbs := by
  obtain ⟨c, hn, he⟩ := Rat.exists_eq_mul_div_num_and_eq_mul_div_den n hd
  have hc : c ≠ 0 := by
    intro hzero
    apply hd
    simpa [hzero] using he
  have hcpos : 1 ≤ c.natAbs := by
    have hne : c.natAbs ≠ 0 := by simpa using hc
    omega
  have hnabs := congrArg Int.natAbs hn
  have hdabs := congrArg Int.natAbs he
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at hnabs hdabs
  constructor
  · rw [hnabs]
    simpa using Nat.mul_le_mul_right ((n : ℚ) / d).num.natAbs hcpos
  · rw [hdabs]
    simpa using Nat.mul_le_mul_right ((n : ℚ) / d).den hcpos

theorem gram_det_size_le {r s : ℕ} (R : Matrix (Fin r) (Fin s) ℤ)
    (hR : BooleanEntries R) (hrs : r ≤ s) :
    (gram R).det.natAbs.size ≤ 2 * (s + 1) ^ 2 + 1 := by
  have habs := gram_det_abs_le R hR
  rw [← Int.natCast_natAbs] at habs
  have hnat : (gram R).det.natAbs ≤ r.factorial * (s + 1) ^ r := by exact_mod_cast habs
  have hle : r.factorial * (s + 1) ^ r ≤ coefficientBound r s := by
    unfold coefficientBound
    calc
      _ = 1 * (r.factorial * (s + 1) ^ r) := by simp
      _ ≤ (r * r + 1) * (r.factorial * (s + 1) ^ r) := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by rw [Nat.mul_assoc]
  apply Nat.size_le.mpr
  apply (hnat.trans (hle.trans (coefficientBound_le_two_pow r s hrs))).trans_lt
  exact Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _)

/-- The canonical numerator and denominator of every actual residual basis
coefficient have polynomial bit length, derived from a matching independent
0/1 sample-row basis. This concerns precision, not machine runtime. -/
theorem residual_coordinate_precision_le {r s : ℕ} (R : Matrix (Fin r) (Fin s) ℤ)
    (hBool : BooleanEntries R) (hR : LinearIndependent ℚ (rationalMatrix R))
    (B : GodMoveRationalRowBasis.RowBasis s)
    (hspan : GodMoveRationalRowBasis.rowSpan B =
      Submodule.span ℚ (Set.range (rationalMatrix R))) (i j : Fin s) :
    (GodMoveRationalRowBasis.residual B (Pi.single i 1) j).num.natAbs.size ≤
      2 * (s + 1) ^ 2 + 1 ∧
    (GodMoveRationalRowBasis.residual B (Pi.single i 1) j).den.size ≤
      2 * (s + 1) ^ 2 + 1 := by
  have hrs : r ≤ s := by
    simpa [Module.finrank_fintype_fun_eq_card] using hR.fintype_card_le_finrank
  rw [residual_coordinate_eq_int_ratio R hR B hspan i j]
  have h := rat_ratio_num_den_le (relationMatrix R j i) (gram R).det (gram_int_det_ne_zero R hR)
  exact ⟨(Nat.size_le_size h.1).trans (relationMatrix_entry_size_le R hBool hrs j i),
    (Nat.size_le_size h.2).trans (gram_det_size_le R hBool hrs)⟩

end GodMoveGramPrecision

#print axioms GodMoveGramPrecision.gram_det_abs_le
#print axioms GodMoveGramPrecision.gram_adjugate_abs_le
#print axioms GodMoveGramPrecision.relationMatrix_entry_abs_le
#print axioms GodMoveGramPrecision.gram_det_ne_zero
#print axioms GodMoveGramPrecision.relationMatrix_mulVec_eq_zero_iff
#print axioms GodMoveGramPrecision.integer_relations_eq_zero_iff
#print axioms GodMoveGramPrecision.relationMatrix_entry_size_le
#print axioms GodMoveGramPrecision.independent_relationMatrix_entry_size_le
#print axioms GodMoveGramPrecision.relationMatrix_mulVec_eq_scaled_residual
#print axioms GodMoveGramPrecision.residual_coordinate_eq_int_ratio
#print axioms GodMoveGramPrecision.residual_coordinate_precision_le
