import GodMoveTrackedRowPrecision
import GodMoveDotLoopPrecision

/-!
# Precision throughout the cached inverse builder

The stored orthogonal and provenance rows have independent integer Gram and
inverse formulas. Using those formulas at every stage avoids repeatedly feeding
a generic arithmetic height estimate into the next Gram--Schmidt step.

The resulting certificate covers the rational operands, products and every
zero-seeded accumulator prefix of each dot-product loop, together with the
component divisions, residual subtractions and final row divisions. It concerns
canonical rational values, not the internal integer operations implementing a
rational primitive, input discovery, allocation, or a compiled machine clock.
-/

namespace GodMoveTrackedArithmeticPrecision

open GodMoveTrackedOrthogonalization GodMoveTrackedRowPrecision
open GodMoveRationalPrecisionArithmetic GodMoveDotLoopPrecision
open scoped BigOperators

def normBits (n : ℕ) : ℕ := (2 * storedMagnitudeBits n + 1) * (n + 1)
def componentBits (n : ℕ) : ℕ := 2 * normBits n
def scaledBits (n : ℕ) : ℕ := storedMagnitudeBits n + normBits n

/-- A conservative common exponent for every rational stage of the builder. -/
def arithmeticBits (n : ℕ) : ℕ := 100 * (n + 1) ^ 4

private theorem boolean_bitBound (q : ℚ) (hq : q = 0 ∨ q = 1) : BitBound q 0 := by
  rcases hq with rfl | rfl <;> norm_num [BitBound, Bound]

theorem inputRow_bitBound {n : ℕ} (A : Table n)
    (hA : ∀ i j, tableValue A i j = 0 ∨ tableValue A i j = 1)
    (k : ℕ) (j : Fin n) : BitBound (inputRow A k)[j] 0 := by
  by_cases hk : k < n
  · simpa [inputRow, hk, tableValue] using boolean_bitBound _ (hA ⟨k, hk⟩ j)
  · simp [inputRow, hk, BitBound, Bound]

theorem unitRow_bitBound (n k : ℕ) (j : Fin n) : BitBound (unitRow n k)[j] 0 := by
  apply boolean_bitBound
  simp [unitRow]
  omega

theorem build_norms_bitBound {n : ℕ} (A : Table n)
    (hA : ∀ i j, tableValue A i j = 0 ∨ tableValue A i j = 1)
    (hLI : LinearIndependent ℚ (tableValue A)) (k : ℕ) (hk : k ≤ n) (i : Fin k) :
    BitBound (build A k).norms[i] (normBits n) := by
  rw [(build_valid A hLI k hk).norms_correct i]
  have h := dot_bitBound Finset.univ
    (fun j : Fin n => (build A k).rows[i][j])
    (fun j : Fin n => (build A k).rows[i][j])
    (storedMagnitudeBits n) (storedMagnitudeBits n)
    (fun j _ => build_rows_bitBound A hA hLI k hk i j)
    (fun j _ => build_rows_bitBound A hA hLI k hk i j)
  apply h.mono
  simp only [Finset.card_univ, Fintype.card_fin]
  unfold normBits
  nlinarith

theorem build_components_bitBound {n : ℕ} (A : Table n)
    (hA : ∀ i j, tableValue A i j = 0 ∨ tableValue A i j = 1)
    (hLI : LinearIndependent ℚ (tableValue A)) (k : ℕ) (hk : k ≤ n) (i : Fin k) :
    BitBound (components (build A k) (inputRow A k))[i] (componentBits n) := by
  have hdot := dot_bitBound Finset.univ
    (fun j : Fin n => (inputRow A k)[j])
    (fun j : Fin n => (build A k).rows[i][j]) 0 (storedMagnitudeBits n)
    (fun j _ => inputRow_bitBound A hA k j)
    (fun j _ => build_rows_bitBound A hA hLI k hk i j)
  have hn : BitBound (dotRows (inputRow A k) (build A k).rows[i]) (normBits n) := by
    apply hdot.mono
    simp only [Finset.card_univ, Fintype.card_fin]
    unfold normBits
    nlinarith
  have h := hn.div (build_norms_bitBound A hA hLI k hk i)
  simpa [components, componentBits, two_mul] using h

/-- The fields follow the actual cached builder's rational loops. `DotPrecision`
includes both input operands, each multiplication result and all accumulator
prefixes of the instrumented zero-seeded dot-product implementation. -/
structure InversePrecision {n : ℕ} (A : Table n) (b : ℕ) : Prop where
  inputs : ∀ i j : Fin n, BitBound A[i][j] b
  units : ∀ k, ∀ j : Fin n, BitBound (unitRow n k)[j] b
  rows : ∀ k, k ≤ n → ∀ (i : Fin k) (j : Fin n),
    BitBound (build A k).rows[i][j] b
  coeffs : ∀ k, k ≤ n → ∀ (i : Fin k) (j : Fin n),
    BitBound (build A k).coeffs[i][j] b
  norms : ∀ k, k ≤ n → ∀ i : Fin k, BitBound (build A k).norms[i] b
  componentDots : ∀ k, k < n → ∀ i : Fin k,
    DotPrecision (fun j : Fin n => (inputRow A k)[j])
      (fun j => (build A k).rows[i][j]) b
  components : ∀ k, k < n → ∀ i : Fin k,
    BitBound (GodMoveTrackedOrthogonalization.components (build A k) (inputRow A k))[i] b
  rowUpdateDots : ∀ k, k < n → ∀ j : Fin n,
    DotPrecision
      (fun i : Fin k => (GodMoveTrackedOrthogonalization.components
        (build A k) (inputRow A k))[i])
      (fun i => (build A k).rows[i][j]) b
  coeffUpdateDots : ∀ k, k < n → ∀ j : Fin n,
    DotPrecision
      (fun i : Fin k => (GodMoveTrackedOrthogonalization.components
        (build A k) (inputRow A k))[i])
      (fun i => (build A k).coeffs[i][j]) b
  rowUpdates : ∀ k, k < n → ∀ j : Fin n,
    BitBound (subtractComponents (inputRow A k)
      (GodMoveTrackedOrthogonalization.components (build A k) (inputRow A k))
      (build A k).rows)[j] b
  coeffUpdates : ∀ k, k < n → ∀ j : Fin n,
    BitBound (subtractComponents (unitRow n k)
      (GodMoveTrackedOrthogonalization.components (build A k) (inputRow A k))
      (build A k).coeffs)[j] b
  newNormDots : ∀ k, k < n →
    let u := subtractComponents (inputRow A k)
      (GodMoveTrackedOrthogonalization.components (build A k) (inputRow A k))
      (build A k).rows
    DotPrecision (fun j : Fin n => u[j]) (fun j => u[j]) b
  scaled : ∀ i j : Fin n, BitBound ((build A n).rows[i][j] / (build A n).norms[i]) b
  weightDots : ∀ j l : Fin n,
    DotPrecision (fun i : Fin n => (build A n).rows[i][j] / (build A n).norms[i])
      (fun i => (build A n).coeffs[i][l]) b

private theorem stored_le_component (n : ℕ) : storedMagnitudeBits n ≤ componentBits n := by
  unfold componentBits normBits
  nlinarith

private theorem norm_le_component (n : ℕ) : normBits n ≤ componentBits n := by
  unfold componentBits
  omega

private theorem scaled_le_component (n : ℕ) : scaledBits n ≤ componentBits n := by
  unfold scaledBits componentBits normBits
  nlinarith

private theorem component_le_arithmetic (n : ℕ) : componentBits n ≤ arithmeticBits n := by
  unfold componentBits normBits storedMagnitudeBits arithmeticBits
  ring_nf
  omega

private theorem uniform_dot {n m : ℕ} (hm : m ≤ n) (v w : Fin m → ℚ)
    (hv : ∀ i, BitBound (v i) (componentBits n))
    (hw : ∀ i, BitBound (w i) (componentBits n)) :
    DotPrecision v w (arithmeticBits n) := by
  apply dotPrecision_of_bounds v w (componentBits n) (componentBits n)
    (arithmeticBits n) hv hw
  · exact component_le_arithmetic n
  · exact component_le_arithmetic n
  · unfold componentBits normBits storedMagnitudeBits arithmeticBits
    ring_nf
    omega
  · have h := Nat.mul_le_mul_left (componentBits n + componentBits n + 1) hm
    unfold componentBits normBits storedMagnitudeBits arithmeticBits at *
    nlinarith

/-- All rational stages of the actual cached inverse have polynomial precision,
derived solely from independent Boolean input rows. No intermediate precision
or small-rank premise is supplied by the caller. -/
theorem inverse_precision {n : ℕ} (A : Table n)
    (hA : ∀ i j, tableValue A i j = 0 ∨ tableValue A i j = 1)
    (hLI : LinearIndependent ℚ (tableValue A)) :
    InversePrecision A (arithmeticBits n) := by
  have hB := stored_le_component n
  have hQ := component_le_arithmetic n
  have hu : ∀ (k : ℕ) (hk : k ≤ n) (i : Fin k) (j : Fin n),
      BitBound (build A k).rows[i][j] (componentBits n) :=
    fun k hk i j => (build_rows_bitBound A hA hLI k hk i j).mono hB
  have hc : ∀ (k : ℕ) (hk : k ≤ n) (i : Fin k) (j : Fin n),
      BitBound (build A k).coeffs[i][j] (componentBits n) :=
    fun k hk i j => (build_coeffs_bitBound A hA hLI k hk i j).mono hB
  have hs : ∀ i j : Fin n,
      BitBound ((build A n).rows[i][j] / (build A n).norms[i]) (componentBits n) := by
    intro i j
    exact ((build_rows_bitBound A hA hLI n le_rfl i j).div
      (build_norms_bitBound A hA hLI n le_rfl i)).mono (scaled_le_component n)
  refine {
    inputs := fun i j => (boolean_bitBound _ (hA i j)).mono (Nat.zero_le _)
    units := fun k j => (unitRow_bitBound n k j).mono (Nat.zero_le _)
    rows := fun k hk i j => (hu k hk i j).mono hQ
    coeffs := fun k hk i j => (hc k hk i j).mono hQ
    norms := fun k hk i => (build_norms_bitBound A hA hLI k hk i).mono
      ((norm_le_component n).trans hQ)
    componentDots := ?_
    components := fun k hk i => (build_components_bitBound A hA hLI k (by omega) i).mono hQ
    rowUpdateDots := ?_
    coeffUpdateDots := ?_
    rowUpdates := ?_
    coeffUpdates := ?_
    newNormDots := ?_
    scaled := fun i j => (hs i j).mono hQ
    weightDots := fun j l => uniform_dot le_rfl _ _ (fun i => hs i j)
      (fun i => hc n le_rfl i l)
  }
  · intro k hk i
    exact uniform_dot le_rfl _ _
      (fun j => (inputRow_bitBound A hA k j).mono (Nat.zero_le _))
      (fun j => hu k (by omega) i j)
  · intro k hk j
    exact uniform_dot (by omega) _ _
      (fun i => build_components_bitBound A hA hLI k (by omega) i)
      (fun i => hu k (by omega) i j)
  · intro k hk j
    exact uniform_dot (by omega) _ _
      (fun i => build_components_bitBound A hA hLI k (by omega) i)
      (fun i => hc k (by omega) i j)
  · intro k hk j
    simpa [build, step] using (hu (k + 1) (by omega) (Fin.last k) j).mono hQ
  · intro k hk j
    simpa [build, step] using (hc (k + 1) (by omega) (Fin.last k) j).mono hQ
  · intro k hk
    have hd := uniform_dot le_rfl
      (fun j : Fin n => (build A (k + 1)).rows[Fin.last k][j])
      (fun j : Fin n => (build A (k + 1)).rows[Fin.last k][j])
      (fun j => hu (k + 1) (by omega) (Fin.last k) j)
      (fun j => hu (k + 1) (by omega) (Fin.last k) j)
    simpa [build, step] using hd

/-- Correctness, rational-operation count, and complete rational-stage precision
hold for the same materialized inverse algorithm. This is not a Turing runtime
theorem for discovering the input matrix or implementing rational primitives. -/
theorem inverse_correct_cost_precision {n : ℕ} (A : Table n)
    (hA : ∀ i j, tableValue A i j = 0 ∨ tableValue A i j = 1)
    (hLI : LinearIndependent ℚ (tableValue A)) :
    tableValue (GodMoveTrackedOrthogonalizationCost.inverseTable A).value * tableValue A = 1 ∧
    (GodMoveTrackedOrthogonalizationCost.inverseTable A).operations ≤ 8 * n ^ 3 ∧
    InversePrecision A (arithmeticBits n) := by
  refine ⟨?_, GodMoveTrackedOrthogonalizationCost.inverseTable_operations_le_cubic A,
    inverse_precision A hA hLI⟩
  rw [GodMoveTrackedOrthogonalizationCost.inverseTable_value]
  exact inverseTable_mul A hLI

end GodMoveTrackedArithmeticPrecision

#print axioms GodMoveTrackedArithmeticPrecision.build_norms_bitBound
#print axioms GodMoveTrackedArithmeticPrecision.build_components_bitBound
#print axioms GodMoveTrackedArithmeticPrecision.inverse_precision
#print axioms GodMoveTrackedArithmeticPrecision.inverse_correct_cost_precision
