import GodMoveGramPrecision
import GodMoveResidualQueries

/-!
# Polynomial residual precision for actual sample states

Every sample row is the 0/1 vector of actual circuit-wire values. The existing
exact row selector extracts an independent subset of those original rows;
their integer Gram matrix therefore supplies the proved precision bound.

For any numeric basis whose span matches the current sample rows, the actual
`coefficientBits` value of every generated residual relation is at most
`2 * (c.length + 1)^2 + 1`. No independent-basis or precision certificate is
required from the caller. This is a bound on rational representation size,
not a bound on arithmetic execution time or counterexample search.
-/

namespace GodMoveGramSamplePrecision

open GodMoveBooleanInterpolation GodMoveBooleanWireTable GodMoveRationalRowBasis
open GodMoveGramPrecision GodMoveResidualQueries
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer (CGate runFrom)

def sampleRows {n : ℕ} (c : List (CGate n)) (samples : List (Assignment n)) :=
  samples.map (fun a => (a, wireRow c a))

def independentSampleRows {n : ℕ} (c : List (CGate n)) (samples : List (Assignment n)) :=
  selectRows (sampleRows c samples)

theorem independentSampleRows_consistent {n : ℕ} (c : List (CGate n))
    (samples : List (Assignment n)) (i : Fin (independentSampleRows c samples).length) :
    ((independentSampleRows c samples).get i).2 =
      wireRow c ((independentSampleRows c samples).get i).1 := by
  have hm := selectRows_subset (sampleRows c samples) _
    (List.getElem_mem i.isLt)
  obtain ⟨a, _, heq⟩ := List.mem_map.mp hm
  simp only [List.get_eq_getElem]
  rw [← heq]

def integerSampleMatrix {n : ℕ} (c : List (CGate n)) (samples : List (Assignment n)) :
    Matrix (Fin (independentSampleRows c samples).length) (Fin c.length) ℤ :=
  fun i j => if (runFrom ((independentSampleRows c samples).get i).1 [] c).getD j.val false
    then 1 else 0

theorem integerSampleMatrix_boolean {n : ℕ} (c : List (CGate n))
    (samples : List (Assignment n)) : BooleanEntries (integerSampleMatrix c samples) := by
  intro i j
  unfold integerSampleMatrix
  split <;> simp

theorem integerSampleMatrix_cast {n : ℕ} (c : List (CGate n))
    (samples : List (Assignment n)) :
    rationalMatrix (integerSampleMatrix c samples) =
      (fun i : Fin (independentSampleRows c samples).length =>
        ((independentSampleRows c samples).get i).2) := by
  funext i j
  rw [independentSampleRows_consistent]
  simp [rationalMatrix, integerSampleMatrix, wireRow, bit]

theorem integerSampleMatrix_linearIndependent {n : ℕ} (c : List (CGate n))
    (samples : List (Assignment n)) :
    LinearIndependent ℚ (rationalMatrix (integerSampleMatrix c samples)) := by
  rw [integerSampleMatrix_cast]
  exact selectRows_linearIndependent (sampleRows c samples)

theorem sampleRows_span {n : ℕ} (c : List (CGate n)) (samples : List (Assignment n)) :
    rowListSpan (sampleRows c samples) = GodMoveRowSpanSeparation.rowSpan c samples := by
  unfold rowListSpan GodMoveRowSpanSeparation.rowSpan
  congr 1
  ext v
  simp only [Set.mem_setOf_eq, Finset.mem_coe, List.mem_toFinset, sampleRows, List.mem_map]
  constructor
  · rintro ⟨x, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨(a, wireRow c a), ⟨a, ha, rfl⟩, rfl⟩

theorem integerSampleMatrix_span {n : ℕ} (c : List (CGate n))
    (samples : List (Assignment n)) :
    Submodule.span ℚ (Set.range (rationalMatrix (integerSampleMatrix c samples))) =
      GodMoveRowSpanSeparation.rowSpan c samples := by
  rw [integerSampleMatrix_cast, ← rowListSpan_eq_span_get, independentSampleRows,
    selectRows_span, sampleRows_span]

/-- Both canonical rational components of every actual residual coefficient
have the quadratic bit bound whenever the basis represents the sample rows. -/
theorem sample_state_residual_precision_le {n : ℕ} (c : List (CGate n))
    (samples : List (Assignment n)) (B : RowBasis c.length)
    (hspan : GodMoveRationalRowBasis.rowSpan B = GodMoveRowSpanSeparation.rowSpan c samples)
    (j i : Fin c.length) :
    (residualCoefficients B j i).num.natAbs.size ≤ 2 * (c.length + 1) ^ 2 + 1 ∧
    (residualCoefficients B j i).den.size ≤ 2 * (c.length + 1) ^ 2 + 1 := by
  exact residual_coordinate_precision_le (integerSampleMatrix c samples)
    (integerSampleMatrix_boolean c samples) (integerSampleMatrix_linearIndependent c samples)
    B (hspan.trans (integerSampleMatrix_span c samples).symm) i j

/-- The actual computed maximum precision budget is polynomial in wire count;
its bound is proved from sample-state consistency, not assumed. -/
theorem sample_state_coefficientBits_le {n : ℕ} (c : List (CGate n))
    (samples : List (Assignment n)) (B : RowBasis c.length)
    (hspan : GodMoveRationalRowBasis.rowSpan B = GodMoveRowSpanSeparation.rowSpan c samples)
    (j : Fin c.length) :
    coefficientBits (residualCoefficients B j) ≤ 2 * (c.length + 1) ^ 2 + 1 := by
  apply Finset.sup_le
  intro i _
  have h := sample_state_residual_precision_le c samples B hspan j i
  exact max_le h.1 h.2

end GodMoveGramSamplePrecision

#print axioms GodMoveGramSamplePrecision.integerSampleMatrix_boolean
#print axioms GodMoveGramSamplePrecision.integerSampleMatrix_linearIndependent
#print axioms GodMoveGramSamplePrecision.integerSampleMatrix_span
#print axioms GodMoveGramSamplePrecision.sample_state_residual_precision_le
#print axioms GodMoveGramSamplePrecision.sample_state_coefficientBits_le
