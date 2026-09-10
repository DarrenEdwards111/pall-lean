import GodMoveBooleanWireTable
import GodMoveSmallSeparatingSamples

/-!
# Numeric wire-row spanning implies semantic sample separation

The row at a Boolean assignment lists the values of every emitted circuit
wire. If the selected rows span every such row over the rationals, then a
polynomial in the computed-wire space vanishing on the selected assignments
vanishes everywhere on the Boolean cube. Multilinearity then makes it zero.

This proves the interface needed by an actual rational row-selection
algorithm: its finite numeric span invariant yields the existing semantic
`SeparatesWires` condition, rather than assuming that condition as input.
-/

namespace GodMoveRowSpanSeparation

open GodMoveBooleanInterpolation GodMoveComputedWireRank GodMoveBooleanWireTable
open GodMoveSamplingBarrier GodMoveSmallSeparatingSamples GodMoveCircuitNormalization
open GodMoveWireSampleCertificate
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer (CGate)
open scoped BigOperators

noncomputable def wirePolynomial {n : ℕ} (c : List (CGate n))
    (i : Fin c.length) : Poly n := (normalizedWires c).getD i.val 0

theorem wireSpace_eq_span_indexed {n : ℕ} (c : List (CGate n)) :
    wireSpace c = Submodule.span ℚ (Set.range (wirePolynomial c)) := by
  classical
  unfold wireSpace spanWires
  apply congrArg (Submodule.span ℚ)
  ext p
  simp only [Finset.mem_coe, List.mem_toFinset, Set.mem_range]
  constructor
  · intro hp
    obtain ⟨i, hi, hval⟩ := List.mem_iff_getElem.mp hp
    refine ⟨⟨i, by simpa only [normalizedWires_length] using hi⟩, ?_⟩
    exact (List.getD_eq_getElem _ _ hi).trans hval
  · rintro ⟨i, rfl⟩
    have hi : i.val < (normalizedWires c).length := by
      simpa only [normalizedWires_length] using i.isLt
    rw [wirePolynomial, List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi

noncomputable def rowSpan {n : ℕ} (c : List (CGate n))
    (samples : List (Assignment n)) : Submodule ℚ (Fin c.length → ℚ) :=
  Submodule.span ℚ (↑(samples.map (wireRow c)).toFinset : Set (Fin c.length → ℚ))

def coefficientFunctional {s : ℕ} (coeff : Fin s → ℚ) : (Fin s → ℚ) →ₗ[ℚ] ℚ :=
  ∑ i : Fin s, coeff i • LinearMap.proj i

theorem coefficientFunctional_apply {s : ℕ} (coeff v : Fin s → ℚ) :
    coefficientFunctional coeff v = ∑ i : Fin s, coeff i * v i := by
  simp [coefficientFunctional]

theorem eval_wire_combination {n : ℕ} (c : List (CGate n))
    (coeff : Fin c.length → ℚ) (a : Assignment n) :
    MvPolynomial.eval (booleanPoint a) (∑ i : Fin c.length, coeff i • wirePolynomial c i) =
      coefficientFunctional coeff (wireRow c a) := by
  rw [coefficientFunctional_apply]
  change GodMoveSampledWireGauge.sampleEval a (∑ i, coeff i • wirePolynomial c i) = _
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [GodMoveSampledWireGauge.sampleEval_apply, wirePolynomial, ← wireRow_eq_normalized_eval]

/-- A finite rational row-space proof suffices for the global polynomial
condition; no assumed polynomial identity check is hidden in this step. -/
theorem separates_of_all_rows_mem {n : ℕ} (c : List (CGate n))
    (samples : List (Assignment n))
    (hrows : ∀ a : Assignment n, wireRow c a ∈ rowSpan c samples) :
    SeparatesWires c samples := by
  intro p hp hzero
  rw [wireSpace_eq_span_indexed] at hp
  obtain ⟨coeff, hcoeff⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hp
  have heval (a : Assignment n) :
      MvPolynomial.eval (booleanPoint a) p = coefficientFunctional coeff (wireRow c a) := by
    rw [← hcoeff]
    exact eval_wire_combination c coeff a
  have hvanish : ∀ v ∈ rowSpan c samples, coefficientFunctional coeff v = 0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
        have hv' : v ∈ samples.map (wireRow c) := by simpa using hv
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv'
        rw [← heval]
        exact hzero a ha
    | zero => exact (coefficientFunctional coeff).map_zero
    | add v w _ _ hv hw => simp [map_add, hv, hw]
    | smul a v _ hv => simp [hv]
  apply multilinear_eq_of_boolean_eval p 0
    (isMultilinear_of_mem_wireSpace c p (by rwa [wireSpace_eq_span_indexed]))
    (by intro α hα; simp at hα)
  intro a
  simpa [heval] using hvanish (wireRow c a) (hrows a)

/-- Completeness of the executable assignment table reduces row coverage to
its actual finite rows. -/
theorem separates_of_table_rows_mem {n : ℕ} (c : List (CGate n))
    (samples : List (Assignment n))
    (hrows : ∀ a ∈ allAssignments n, wireRow c a ∈ rowSpan c samples) :
    SeparatesWires c samples :=
  separates_of_all_rows_mem c samples (fun a => hrows a (allAssignments_complete n a))

end GodMoveRowSpanSeparation

#print axioms GodMoveRowSpanSeparation.wireSpace_eq_span_indexed
#print axioms GodMoveRowSpanSeparation.eval_wire_combination
#print axioms GodMoveRowSpanSeparation.separates_of_all_rows_mem
#print axioms GodMoveRowSpanSeparation.separates_of_table_rows_mem
