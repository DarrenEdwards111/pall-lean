import GodMoveGramPrecision

/-!
# Final inverse weights have polynomial precision

For an integer 0/1 square matrix A, every rational left inverse W has entries
`adj(A)[i,j]/det(A)`. This identity is derived from W*A=I; neither an entry
bound nor an inverse-construction algorithm is assumed. Determinant bounds
then give canonical numerator magnitude and denominator at most n!, and at
most (n+1)^2+1 magnitude bits each.

These bounds concern the final reduced entries of W. They do not bound the
intermediate tracked coefficients, orthogonal rows, norms, divisions, or
partial sums used to compute W. Arithmetic-operation counts plus this final
precision bound therefore do not by themselves establish bit-level runtime.
-/

namespace GodMoveProjectionWeightPrecision

open GodMoveGramPrecision
open scoped Matrix

variable {n : ℕ}

theorem boolean_det_abs_le_factorial (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : BooleanEntries A) : |A.det| ≤ (n.factorial : ℤ) := by
  simpa using det_abs_le A 1 (boolean_entry_abs_le A hA)

theorem boolean_adjugate_abs_le_factorial (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : BooleanEntries A) (i j : Fin n) :
    |A.adjugate i j| ≤ (n.factorial : ℤ) := by
  rw [Matrix.adjugate_apply]
  apply boolean_det_abs_le_factorial
  intro k l
  by_cases hk : k = j
  · subst k
    simp only [Matrix.updateRow_self, Pi.single_apply]
    split <;> simp
  · rw [Matrix.updateRow_ne hk]
    exact hA k l

/-- The numerical left-inverse identity itself supplies a nonzero integer
determinant. This includes the zero-dimensional matrix convention. -/
theorem det_ne_zero_of_left_inverse (A : Matrix (Fin n) (Fin n) ℤ)
    (W : Matrix (Fin n) (Fin n) ℚ) (hWA : W * rationalMatrix A = 1) : A.det ≠ 0 := by
  have h := congrArg Matrix.det hWA
  have hdetmap : (A.det : ℚ) = (rationalMatrix A).det := (Int.castRingHom ℚ).map_det A
  rw [Matrix.det_mul, Matrix.det_one, ← hdetmap] at h
  intro hzero
  simp [hzero] at h

/-- Every final weight is a cofactor ratio, regardless of which exact
algorithm produced the left inverse. -/
theorem leftInverse_entry_eq_ratio (A : Matrix (Fin n) (Fin n) ℤ)
    (W : Matrix (Fin n) (Fin n) ℚ) (hWA : W * rationalMatrix A = 1)
    (i j : Fin n) : W i j = (A.adjugate i j : ℚ) / A.det := by
  have hdet : (A.det : ℚ) ≠ 0 := by exact_mod_cast det_ne_zero_of_left_inverse A W hWA
  have h := congrArg (fun P => P * (rationalMatrix A).adjugate) hWA
  change W * rationalMatrix A * (rationalMatrix A).adjugate =
    1 * (rationalMatrix A).adjugate at h
  rw [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul,
    Matrix.mul_one, Matrix.one_mul] at h
  have hc := congrFun (congrFun h i) j
  have hdetmap : (A.det : ℚ) = (rationalMatrix A).det := (Int.castRingHom ℚ).map_det A
  have hadjmap : rationalMatrix A.adjugate = (rationalMatrix A).adjugate :=
    (Int.castRingHom ℚ).map_adjugate A
  have hentry : (A.adjugate i j : ℚ) = (rationalMatrix A).adjugate i j :=
    congrFun (congrFun hadjmap i) j
  apply (eq_div_iff hdet).mpr
  simpa only [Matrix.smul_apply, smul_eq_mul, ← hdetmap, ← hentry, mul_comm] using hc

/-- Reduction of an integer cofactor ratio cannot enlarge its numerator
magnitude or denominator. Both are bounded directly by n!. -/
theorem leftInverse_entry_num_den_le_factorial (A : Matrix (Fin n) (Fin n) ℤ)
    (W : Matrix (Fin n) (Fin n) ℚ) (hA : BooleanEntries A)
    (hWA : W * rationalMatrix A = 1) (i j : Fin n) :
    (W i j).num.natAbs ≤ n.factorial ∧ (W i j).den ≤ n.factorial := by
  rw [leftInverse_entry_eq_ratio A W hWA i j]
  have hratio := rat_ratio_num_den_le (A.adjugate i j) A.det
    (det_ne_zero_of_left_inverse A W hWA)
  have hnum : (A.adjugate i j).natAbs ≤ n.factorial := by
    have h := boolean_adjugate_abs_le_factorial A hA i j
    rw [← Int.natCast_natAbs] at h
    exact_mod_cast h
  have hden : A.det.natAbs ≤ n.factorial := by
    have h := boolean_det_abs_le_factorial A hA
    rw [← Int.natCast_natAbs] at h
    exact_mod_cast h
  exact ⟨hratio.1.trans hnum, hratio.2.trans hden⟩

theorem factorial_le_input_power (n : ℕ) : n.factorial ≤ (n + 1) ^ n :=
  (Nat.factorial_le_pow n).trans (Nat.pow_le_pow_left (Nat.le_succ n) n)

theorem factorial_le_two_pow_quadratic (n : ℕ) : n.factorial ≤ 2 ^ (n + 1) ^ 2 := by
  calc
    n.factorial ≤ (n + 1) ^ n := factorial_le_input_power n
    _ ≤ (2 ^ (n + 1)) ^ n :=
      Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_two_pow_self (n := n + 1))) n
    _ = 2 ^ ((n + 1) * n) := (pow_mul _ _ _).symm
    _ ≤ 2 ^ (n + 1) ^ 2 := Nat.pow_le_pow_right (by decide) (by nlinarith)

theorem size_le_of_le_factorial {v n : ℕ} (hv : v ≤ n.factorial) :
    v.size ≤ (n + 1) ^ 2 + 1 := by
  apply Nat.size_le.mpr
  exact (hv.trans (factorial_le_two_pow_quadratic n)).trans_lt
    (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))

/-- Final canonical numerator and denominator have a quadratic magnitude-bit
bound. A separate sign bit suffices for the numerator. -/
theorem leftInverse_entry_precision (A : Matrix (Fin n) (Fin n) ℤ)
    (W : Matrix (Fin n) (Fin n) ℚ) (hA : BooleanEntries A)
    (hWA : W * rationalMatrix A = 1) (i j : Fin n) :
    (W i j).num.natAbs.size ≤ (n + 1) ^ 2 + 1 ∧
      (W i j).den.size ≤ (n + 1) ^ 2 + 1 := by
  have h := leftInverse_entry_num_den_le_factorial A W hA hWA i j
  exact ⟨size_le_of_le_factorial h.1, size_le_of_le_factorial h.2⟩

/-- Recover integer 0/1 entries from a rational sample matrix. -/
def integerBooleanMatrix (A : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => if A i j = 1 then 1 else 0

theorem integerBooleanMatrix_boolean (A : Matrix (Fin n) (Fin n) ℚ) :
    BooleanEntries (integerBooleanMatrix A) := by
  intro i j
  unfold integerBooleanMatrix
  split <;> simp

theorem rational_integerBooleanMatrix (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : ∀ i j, A i j = 0 ∨ A i j = 1) :
    rationalMatrix (integerBooleanMatrix A) = A := by
  ext i j
  rcases hA i j with h | h <;> simp [rationalMatrix, integerBooleanMatrix, h]

/-- Direct API for the rational 0/1 sample matrix used by a tracked inverse
construction. No determinant or precision hypothesis is required. -/
theorem rational_leftInverse_entry_precision (A W : Matrix (Fin n) (Fin n) ℚ)
    (hA : ∀ i j, A i j = 0 ∨ A i j = 1) (hWA : W * A = 1) (i j : Fin n) :
    (W i j).num.natAbs.size ≤ (n + 1) ^ 2 + 1 ∧
      (W i j).den.size ≤ (n + 1) ^ 2 + 1 := by
  apply leftInverse_entry_precision (integerBooleanMatrix A) W
    (integerBooleanMatrix_boolean A)
  rwa [rational_integerBooleanMatrix A hA]

end GodMoveProjectionWeightPrecision

#print axioms GodMoveProjectionWeightPrecision.boolean_det_abs_le_factorial
#print axioms GodMoveProjectionWeightPrecision.boolean_adjugate_abs_le_factorial
#print axioms GodMoveProjectionWeightPrecision.det_ne_zero_of_left_inverse
#print axioms GodMoveProjectionWeightPrecision.leftInverse_entry_eq_ratio
#print axioms GodMoveProjectionWeightPrecision.leftInverse_entry_num_den_le_factorial
#print axioms GodMoveProjectionWeightPrecision.leftInverse_entry_precision
#print axioms GodMoveProjectionWeightPrecision.rational_leftInverse_entry_precision
