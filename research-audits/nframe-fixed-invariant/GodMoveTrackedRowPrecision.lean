import GodMoveTrackedOrthogonalization
import GodMoveProjectionWeightPrecision
import GodMoveRationalPrecisionArithmetic

/-!
# Precision of the cached orthogonal and provenance rows

Stored orthogonal rows are exact residuals of original Boolean rows against
an independent Boolean prefix. Integer Gram formulas give a common bounded
denominator for each row. The tracked identity U=C*A and the exact inverse
of A then give common-denominator formulas for the provenance rows C.

All bounds are derived from Boolean entries and row independence. They
concern exact reduced rational values in the actual cached builder. Scalar
dot products, norms, component quotients and finite partial sums require
the separate arithmetic precision analysis; no bit-runtime claim is made here.
-/

namespace GodMoveTrackedRowPrecision

open GodMoveTrackedOrthogonalization GodMoveRationalRowBasis
open GodMoveGramPrecision GodMoveProjectionWeightPrecision
open GodMoveRationalPrecisionArithmetic
open scoped BigOperators Matrix

def gramBound (n : ℕ) : ℕ := 2 ^ (2 * (n + 1) ^ 2)

def storedMagnitudeBits (n : ℕ) : ℕ := 5 * (n + 1) ^ 2

/-- A proved common integer denominator, not a caller-supplied precision
assumption. The following theorems construct these representations. -/
def IntegerRowBound {n : ℕ} (v : Vec n) (N D : ℕ) : Prop :=
  ∃ (num : Fin n → ℤ) (den : ℤ), den ≠ 0 ∧ den.natAbs ≤ D ∧
    (∀ j, (num j).natAbs ≤ N) ∧ ∀ j, v j = (num j : ℚ) / den

theorem IntegerRowBound.num_den_le {n N D : ℕ} {v : Vec n}
    (h : IntegerRowBound v N D) (j : Fin n) :
    (v j).num.natAbs ≤ N ∧ (v j).den ≤ D := by
  obtain ⟨num, den, hden, hD, hN, heq⟩ := h
  rw [heq]
  have hratio := rat_ratio_num_den_le (num j) den hden
  exact ⟨hratio.1.trans (hN j), hratio.2.trans hD⟩

theorem gram_det_natAbs_le_bound {r n : ℕ}
    (R : Matrix (Fin r) (Fin n) ℤ) (hR : BooleanEntries R) (hr : r ≤ n) :
    (gram R).det.natAbs ≤ gramBound n := by
  have habs := gram_det_abs_le R hR
  rw [← Int.natCast_natAbs] at habs
  have hbase : (gram R).det.natAbs ≤ r.factorial * (n + 1) ^ r := by exact_mod_cast habs
  have hcoeff : r.factorial * (n + 1) ^ r ≤ coefficientBound r n := by
    unfold coefficientBound
    calc
      _ = 1 * (r.factorial * (n + 1) ^ r) := by simp
      _ ≤ (r * r + 1) * (r.factorial * (n + 1) ^ r) :=
        Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ring
  exact hbase.trans (hcoeff.trans (coefficientBound_le_two_pow r n hr))

theorem relation_entry_natAbs_le_bound {r n : ℕ}
    (R : Matrix (Fin r) (Fin n) ℤ) (hR : BooleanEntries R) (hr : r ≤ n) (i j : Fin n) :
    (relationMatrix R i j).natAbs ≤ gramBound n := by
  have habs := relationMatrix_entry_abs_le R hR i j
  rw [← Int.natCast_natAbs] at habs
  have hcoeff : (relationMatrix R i j).natAbs ≤ coefficientBound r n := by exact_mod_cast habs
  exact hcoeff.trans (coefficientBound_le_two_pow r n hr)

/-- A Boolean vector's actual Gram residual has one denominator for every
coordinate. The determinant and integer numerator are explicitly identified. -/
theorem residual_boolean_integerRowBound {r n : ℕ}
    (R : Matrix (Fin r) (Fin n) ℤ) (hR : BooleanEntries R)
    (hLI : LinearIndependent ℚ (rationalMatrix R)) (hr : r ≤ n)
    (B : RowBasis n) (hspan : rowSpan B = Submodule.span ℚ (Set.range (rationalMatrix R)))
    (v : Fin n → ℤ) (hv : ∀ j, v j = 0 ∨ v j = 1) :
    IntegerRowBound (residual B (fun j => (v j : ℚ))) (n * gramBound n) (gramBound n) := by
  let num : Fin n → ℤ := relationMatrix R *ᵥ v
  let den : ℤ := (gram R).det
  have hd : den ≠ 0 := gram_int_det_ne_zero R hLI
  refine ⟨num, den, hd, gram_det_natAbs_le_bound R hR hr, ?_, ?_⟩
  · intro j
    have habs : |num j| ≤ (n * gramBound n : ℕ) := by
      have h := mul_entry_abs_le (relationMatrix R) (fun i (_ : Fin 1) => v i)
        (gramBound n) 1
        (fun i j => by
          have hh := relation_entry_natAbs_le_bound R hR hr i j
          rw [← Int.natCast_natAbs]
          exact_mod_cast hh)
        (fun i _ => by rcases hv i with h | h <;> simp [h]) j 0
      simpa [num, Matrix.mul_apply, Matrix.mulVec, dotProduct] using h
    rw [← Int.natCast_natAbs] at habs
    exact_mod_cast habs
  · intro j
    have h := relationMatrix_mulVec_eq_scaled_residual (rationalMatrix R) hLI B hspan
      (fun j => (v j : ℚ))
    rw [← rationalMatrix_relation, ← gram_det_cast] at h
    have hc := congrFun h j
    have hnum : (num j : ℚ) =
        (rationalMatrix (relationMatrix R) *ᵥ (fun j => (v j : ℚ))) j := by
      simp [num, rationalMatrix, Matrix.mulVec, dotProduct]
    apply (eq_div_iff (by exact_mod_cast hd : (den : ℚ) ≠ 0)).mpr
    rw [hnum]
    simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using hc.symm

/-- Integer form of the supplied rational Boolean table. -/
def integerInput {n : ℕ} (A : Table n) : Matrix (Fin n) (Fin n) ℤ :=
  integerBooleanMatrix (tableValue A)

def prefixMatrix {n : ℕ} (A : Table n) (k : ℕ) (hk : k ≤ n) :
    Matrix (Fin k) (Fin n) ℤ :=
  fun i j => integerInput A (Fin.castLE hk i) j

theorem integerInput_cast {n : ℕ} (A : Table n)
    (hA : ∀ i j, tableValue A i j = 0 ∨ tableValue A i j = 1) :
    rationalMatrix (integerInput A) = tableValue A := rational_integerBooleanMatrix _ hA

theorem prefixMatrix_boolean {n : ℕ} (A : Table n) (k : ℕ) (hk : k ≤ n) :
    BooleanEntries (prefixMatrix A k hk) :=
  fun i j => integerBooleanMatrix_boolean (tableValue A) (Fin.castLE hk i) j

theorem prefixMatrix_cast {n : ℕ} (A : Table n)
    (hA : ∀ i j, tableValue A i j = 0 ∨ tableValue A i j = 1)
    (k : ℕ) (hk : k ≤ n) :
    rationalMatrix (prefixMatrix A k hk) = fun i => tableValue A (Fin.castLE hk i) := by
  ext i j
  exact congrFun (congrFun (integerInput_cast A hA) (Fin.castLE hk i)) j

theorem prefixMatrix_independent {n : ℕ} (A : Table n)
    (hA : ∀ i j, tableValue A i j = 0 ∨ tableValue A i j = 1)
    (hLI : LinearIndependent ℚ (tableValue A)) (k : ℕ) (hk : k ≤ n) :
    LinearIndependent ℚ (rationalMatrix (prefixMatrix A k hk)) := by
  rw [prefixMatrix_cast A hA k hk]
  exact hLI.comp (Fin.castLE hk) (Fin.castLE_injective hk)

theorem prefixMatrix_span {n : ℕ} (A : Table n)
    (hA : ∀ i j, tableValue A i j = 0 ∨ tableValue A i j = 1)
    (k : ℕ) (hk : k ≤ n) :
    Submodule.span ℚ (Set.range (rationalMatrix (prefixMatrix A k hk))) = prefixSpan A k := by
  rw [prefixMatrix_cast A hA k hk]
  unfold prefixSpan
  congr 1
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨Fin.castLE hk i, i.isLt, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i.val, hi⟩, rfl⟩

/-- Every stored orthogonal row comes from the exact residual of its
original Boolean row against an independent original-row prefix. -/
theorem build_rows_integerRowBound {n : ℕ} (A : Table n)
    (hA : ∀ i j, tableValue A i j = 0 ∨ tableValue A i j = 1)
    (hLI : LinearIndependent ℚ (tableValue A)) (k : ℕ) (hk : k ≤ n) (i : Fin k) :
    IntegerRowBound (rowValue (build A k).rows[i]) (n * gramBound n) (gramBound n) := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    have hkn : k < n := by omega
    have hk' : k ≤ n := by omega
    have hvalid := build_valid A hLI k hk'
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have hnew : rowValue (build A (k + 1)).rows[Fin.last k] =
          residual hvalid.toRowBasis (rowValue (inputRow A k)) := by
        simpa [build, step] using residualRow_eq hvalid (inputRow A k)
      rw [hnew]
      have hv : (fun j : Fin n => (integerInput A ⟨k, hkn⟩ j : ℚ)) =
          rowValue (inputRow A k) := by
        funext j
        have hc := congrFun (congrFun (integerInput_cast A hA) ⟨k, hkn⟩) j
        simpa [rowValue, inputRow, hkn, tableValue] using hc
      rw [← hv]
      apply residual_boolean_integerRowBound (prefixMatrix A k hk')
        (prefixMatrix_boolean A k hk') (prefixMatrix_independent A hA hLI k hk') hk'
      · change Submodule.span ℚ (Set.range (fun i : Fin k => rowValue (build A k).rows[i])) = _
        rw [hvalid.span_eq, prefixMatrix_span A hA k hk']
      · exact fun j => integerBooleanMatrix_boolean (tableValue A) ⟨k, hkn⟩ j
    · simpa [build, step] using ih hk' j

/-- Multiplying a common-denominator row by the actual inverse of a Boolean
matrix retains a single explicitly bounded integer denominator. -/
theorem integerRowBound_vecMul_leftInverse {n N D : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) (hA : BooleanEntries A)
    (W : Matrix (Fin n) (Fin n) ℚ) (hWA : W * rationalMatrix A = 1)
    (v : Vec n) (hv : IntegerRowBound v N D) :
    IntegerRowBound (v ᵥ* W) (n * N * n.factorial) (D * n.factorial) := by
  obtain ⟨num, den, hden, hD, hN, heq⟩ := hv
  have hdet := det_ne_zero_of_left_inverse A W hWA
  have hdetbound : A.det.natAbs ≤ n.factorial := by
    have h := boolean_det_abs_le_factorial A hA
    rw [← Int.natCast_natAbs] at h
    exact_mod_cast h
  refine ⟨fun l => ∑ j : Fin n, num j * A.adjugate j l, den * A.det,
    mul_ne_zero hden hdet, ?_, ?_, ?_⟩
  · rw [Int.natAbs_mul]
    exact Nat.mul_le_mul hD hdetbound
  · intro l
    have habs : |∑ j : Fin n, num j * A.adjugate j l| ≤ (n * N * n.factorial : ℕ) := by
      have h := mul_entry_abs_le (fun (_ : Fin 1) j => num j) A.adjugate N n.factorial
        (fun _ j => by rw [← Int.natCast_natAbs]; exact_mod_cast hN j)
        (boolean_adjugate_abs_le_factorial A hA) 0 l
      simpa only [Matrix.mul_apply] using h
    rw [← Int.natCast_natAbs] at habs
    exact_mod_cast habs
  · intro l
    change (∑ j : Fin n, v j * W j l) = _
    simp_rw [heq, leftInverse_entry_eq_ratio A W hWA, div_mul_div_comm]
    rw [← Finset.sum_div]
    push_cast
    rfl

/-- Provenance coefficients are determined by the stored row and the
inverse of the original matrix; tracking alone is not treated as a bound. -/
theorem build_coeffs_eq_rows_vecMul_inverse {n : ℕ} (A : Table n)
    (hLI : LinearIndependent ℚ (tableValue A)) (k : ℕ) (hk : k ≤ n) (i : Fin k) :
    rowValue (build A k).coeffs[i] =
      rowValue (build A k).rows[i] ᵥ* inverseWeights (tableValue A) := by
  have hvalid := build_valid A hLI k hk
  have htrack := hvalid.tracking i
  have hWA := inverseWeights_mul (tableValue A) hLI
  have hAW : tableValue A * inverseWeights (tableValue A) = 1 :=
    mul_eq_one_comm.mp hWA
  have hu : rowValue (build A k).rows[i] =
      rowValue (build A k).coeffs[i] ᵥ* tableValue A := by
    simpa only [synthesis, LinearMap.coe_mk, AddHom.coe_mk, Matrix.vecMul_eq_sum] using htrack
  rw [hu, Matrix.vecMul_vecMul, hAW, Matrix.vecMul_one]

/-- Actual stored provenance coefficients have bounded common denominators,
derived from the Boolean input and cached tracking invariant. -/
theorem build_coeffs_integerRowBound {n : ℕ} (A : Table n)
    (hA : ∀ i j, tableValue A i j = 0 ∨ tableValue A i j = 1)
    (hLI : LinearIndependent ℚ (tableValue A)) (k : ℕ) (hk : k ≤ n) (i : Fin k) :
    IntegerRowBound (rowValue (build A k).coeffs[i])
      (n * n * gramBound n * n.factorial) (gramBound n * n.factorial) := by
  rw [build_coeffs_eq_rows_vecMul_inverse A hLI k hk i]
  have hWA : inverseWeights (tableValue A) * rationalMatrix (integerInput A) = 1 := by
    rw [integerInput_cast A hA]
    exact inverseWeights_mul _ hLI
  simpa only [Nat.mul_assoc] using
    integerRowBound_vecMul_leftInverse (integerInput A)
      (integerBooleanMatrix_boolean (tableValue A)) (inverseWeights (tableValue A)) hWA
      (rowValue (build A k).rows[i]) (build_rows_integerRowBound A hA hLI k hk i)

theorem input_le_two_pow_square (n : ℕ) : n ≤ 2 ^ (n + 1) ^ 2 :=
  (Nat.le_of_lt (Nat.lt_two_pow_self (n := n))).trans
    (Nat.pow_le_pow_right (by decide) (by nlinarith))

theorem row_bounds_le_uniform (n : ℕ) :
    n * gramBound n ≤ 2 ^ storedMagnitudeBits n ∧
      gramBound n ≤ 2 ^ storedMagnitudeBits n := by
  constructor
  · calc
      _ ≤ 2 ^ (n + 1) ^ 2 * 2 ^ (2 * (n + 1) ^ 2) :=
        Nat.mul_le_mul_right _ (input_le_two_pow_square n)
      _ = 2 ^ (3 * (n + 1) ^ 2) := by rw [← pow_add]; congr 1; omega
      _ ≤ 2 ^ storedMagnitudeBits n := Nat.pow_le_pow_right (by decide)
        (by unfold storedMagnitudeBits; omega)
  · apply Nat.pow_le_pow_right (by decide)
    unfold storedMagnitudeBits
    omega

theorem coeff_bounds_le_uniform (n : ℕ) :
    n * n * gramBound n * n.factorial ≤ 2 ^ storedMagnitudeBits n ∧
      gramBound n * n.factorial ≤ 2 ^ storedMagnitudeBits n := by
  constructor
  · calc
      _ ≤ 2 ^ (n + 1) ^ 2 * 2 ^ (n + 1) ^ 2 *
          2 ^ (2 * (n + 1) ^ 2) * 2 ^ (n + 1) ^ 2 :=
        Nat.mul_le_mul
          (Nat.mul_le_mul_right _ (Nat.mul_le_mul
            (input_le_two_pow_square n) (input_le_two_pow_square n)))
          (factorial_le_two_pow_quadratic n)
      _ = 2 ^ storedMagnitudeBits n := by
        rw [← pow_add, ← pow_add, ← pow_add]
        congr 1
        unfold storedMagnitudeBits
        omega
  · calc
      _ ≤ 2 ^ (2 * (n + 1) ^ 2) * 2 ^ (n + 1) ^ 2 :=
        Nat.mul_le_mul_left _ (factorial_le_two_pow_quadratic n)
      _ = 2 ^ (3 * (n + 1) ^ 2) := by rw [← pow_add]; congr 1; omega
      _ ≤ 2 ^ storedMagnitudeBits n := Nat.pow_le_pow_right (by decide)
        (by unfold storedMagnitudeBits; omega)

/-- Uniform canonical numerator and denominator bounds for every stored U
coefficient at every actual build prefix. -/
theorem build_rows_bitBound {n : ℕ} (A : Table n)
    (hA : ∀ i j, tableValue A i j = 0 ∨ tableValue A i j = 1)
    (hLI : LinearIndependent ℚ (tableValue A)) (k : ℕ) (hk : k ≤ n)
    (i : Fin k) (j : Fin n) :
    BitBound (build A k).rows[i][j] (storedMagnitudeBits n) := by
  have h := (build_rows_integerRowBound A hA hLI k hk i).num_den_le j
  have hb := row_bounds_le_uniform n
  exact ⟨h.1.trans hb.1, h.2.trans hb.2⟩

/-- The same uniform bound for the tracked original-row coefficients C. -/
theorem build_coeffs_bitBound {n : ℕ} (A : Table n)
    (hA : ∀ i j, tableValue A i j = 0 ∨ tableValue A i j = 1)
    (hLI : LinearIndependent ℚ (tableValue A)) (k : ℕ) (hk : k ≤ n)
    (i : Fin k) (j : Fin n) :
    BitBound (build A k).coeffs[i][j] (storedMagnitudeBits n) := by
  have h := (build_coeffs_integerRowBound A hA hLI k hk i).num_den_le j
  have hb := coeff_bounds_le_uniform n
  exact ⟨h.1.trans hb.1, h.2.trans hb.2⟩

theorem build_rows_precision {n : ℕ} (A : Table n)
    (hA : ∀ i j, tableValue A i j = 0 ∨ tableValue A i j = 1)
    (hLI : LinearIndependent ℚ (tableValue A)) (k : ℕ) (hk : k ≤ n)
    (i : Fin k) (j : Fin n) :
    ((build A k).rows[i][j]).num.natAbs.size ≤ storedMagnitudeBits n + 1 ∧
      ((build A k).rows[i][j]).den.size ≤ storedMagnitudeBits n + 1 :=
  (build_rows_bitBound A hA hLI k hk i j).canonical_sizes

theorem build_coeffs_precision {n : ℕ} (A : Table n)
    (hA : ∀ i j, tableValue A i j = 0 ∨ tableValue A i j = 1)
    (hLI : LinearIndependent ℚ (tableValue A)) (k : ℕ) (hk : k ≤ n)
    (i : Fin k) (j : Fin n) :
    ((build A k).coeffs[i][j]).num.natAbs.size ≤ storedMagnitudeBits n + 1 ∧
      ((build A k).coeffs[i][j]).den.size ≤ storedMagnitudeBits n + 1 :=
  (build_coeffs_bitBound A hA hLI k hk i j).canonical_sizes

end GodMoveTrackedRowPrecision

#print axioms GodMoveTrackedRowPrecision.residual_boolean_integerRowBound
#print axioms GodMoveTrackedRowPrecision.prefixMatrix_independent
#print axioms GodMoveTrackedRowPrecision.prefixMatrix_span
#print axioms GodMoveTrackedRowPrecision.build_rows_integerRowBound
#print axioms GodMoveTrackedRowPrecision.integerRowBound_vecMul_leftInverse
#print axioms GodMoveTrackedRowPrecision.build_coeffs_eq_rows_vecMul_inverse
#print axioms GodMoveTrackedRowPrecision.build_coeffs_integerRowBound
#print axioms GodMoveTrackedRowPrecision.build_rows_bitBound
#print axioms GodMoveTrackedRowPrecision.build_coeffs_bitBound
#print axioms GodMoveTrackedRowPrecision.build_rows_precision
#print axioms GodMoveTrackedRowPrecision.build_coeffs_precision
