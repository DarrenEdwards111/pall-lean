import GodMoveRowSpanSeparation
import GodMoveRationalRowBasis
import GodMoveSampleRefinement

/-!
# An exact rational residual test produces semantic counterexamples

For a supplied Boolean assignment, the finite row algorithm decides whether
its wire-value row lies outside the span of the current sample rows. Its
nonzero rational residual supplies explicit coefficients of a polynomial in
the computed-wire space: this polynomial vanishes on all current samples and
has positive squared residual norm at the supplied assignment.

Thus the executable row test is exactly the previously defined semantic
counterexample predicate. This result checks a supplied assignment; it does
not bound the cost of finding an assignment whose test succeeds.
-/

namespace GodMoveNumericCounterexample

open GodMoveBooleanInterpolation GodMoveComputedWireRank GodMoveBooleanWireTable
open GodMoveSmallSeparatingSamples GodMoveSampleRefinement
open GodMoveRowSpanSeparation GodMoveRationalRowBasis
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer (CGate)
open scoped BigOperators

theorem coefficientFunctional_eq_dot {s : ℕ} (coeff v : Vec s) :
    coefficientFunctional coeff v = dot coeff v := by
  rw [coefficientFunctional_apply]
  rfl

theorem row_mem_of_sample {n : ℕ} (c : List (CGate n))
    (samples : List (Assignment n)) (a : Assignment n) (ha : a ∈ samples) :
    wireRow c a ∈ GodMoveRowSpanSeparation.rowSpan c samples := by
  apply Submodule.subset_span
  simp only [Finset.mem_coe, List.mem_toFinset]
  exact List.mem_map.mpr ⟨a, ha, rfl⟩

/-- The residual vector supplies exact rational coefficients in the existing wire DAG. -/
noncomputable def residualPolynomial {n : ℕ} (c : List (CGate n))
    (B : RowBasis c.length) (a : Assignment n) : Poly n :=
  ∑ i : Fin c.length, residual B (wireRow c a) i • wirePolynomial c i

theorem residualPolynomial_mem_wireSpace {n : ℕ} (c : List (CGate n))
    (B : RowBasis c.length) (a : Assignment n) :
    residualPolynomial c B a ∈ wireSpace c := by
  rw [wireSpace_eq_span_indexed]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem eval_residualPolynomial {n : ℕ} (c : List (CGate n))
    (B : RowBasis c.length) (a b : Assignment n) :
    MvPolynomial.eval (booleanPoint b) (residualPolynomial c B a) =
      dot (residual B (wireRow c a)) (wireRow c b) := by
  rw [residualPolynomial, eval_wire_combination, coefficientFunctional_eq_dot]

/-- Orthogonality to the projected component identifies the evaluation with
the squared norm of the numeric residual. -/
theorem dot_residual_input {s : ℕ} (B : RowBasis s) (v : Vec s) :
    dot (residual B v) v = dot (residual B v) (residual B v) := by
  have horth := residual_orthogonal_span B v (projected B v) (projected_mem B v)
  conv_rhs => arg 2; rw [GodMoveRationalRowBasis.residual]
  change dot (residual B v) v =
    dotProduct (residual B v) (v - projected B v)
  rw [dotProduct_sub]
  change dot (residual B v) v = dot (residual B v) v - dot (residual B v) (projected B v)
  rw [horth, sub_zero]

theorem eval_residualPolynomial_self {n : ℕ} (c : List (CGate n))
    (B : RowBasis c.length) (a : Assignment n) :
    MvPolynomial.eval (booleanPoint a) (residualPolynomial c B a) =
      dot (residual B (wireRow c a)) (residual B (wireRow c a)) := by
  rw [eval_residualPolynomial, dot_residual_input]

theorem residualPolynomial_vanishes_samples {n : ℕ} (c : List (CGate n))
    (samples : List (Assignment n)) (B : RowBasis c.length)
    (hspan : GodMoveRationalRowBasis.rowSpan B =
      GodMoveRowSpanSeparation.rowSpan c samples)
    (a b : Assignment n) (hb : b ∈ samples) :
    MvPolynomial.eval (booleanPoint b) (residualPolynomial c B a) = 0 := by
  rw [eval_residualPolynomial]
  apply residual_orthogonal_span
  rw [hspan]
  exact row_mem_of_sample c samples b hb

/-- The accepted row comes with a concrete polynomial counterexample. -/
theorem counterexample_of_accepts {n : ℕ} (c : List (CGate n))
    (samples : List (Assignment n)) (B : RowBasis c.length)
    (hspan : GodMoveRationalRowBasis.rowSpan B =
      GodMoveRowSpanSeparation.rowSpan c samples)
    (a : Assignment n) (ha : accepts B (wireRow c a) = true) :
    Counterexample c samples a := by
  refine ⟨⟨residualPolynomial c B a, residualPolynomial_mem_wireSpace c B a⟩, ?_, ?_⟩
  · apply (mem_residualSpace c samples _).mpr
    intro b hb
    exact residualPolynomial_vanishes_samples c samples B hspan a b hb
  · change MvPolynomial.eval (booleanPoint a) (residualPolynomial c B a) ≠ 0
    rw [eval_residualPolynomial_self, ne_eq, dot_self_eq_zero_iff]
    simpa only [accepts, decide_eq_true_eq] using ha

/-- A wire polynomial vanishing on the sample rows also vanishes on their span. -/
theorem eval_zero_of_row_mem {n : ℕ} (c : List (CGate n))
    (samples : List (Assignment n)) (p : Poly n) (hp : p ∈ wireSpace c)
    (hzero : ∀ b ∈ samples, MvPolynomial.eval (booleanPoint b) p = 0)
    (a : Assignment n) (ha : wireRow c a ∈ GodMoveRowSpanSeparation.rowSpan c samples) :
    MvPolynomial.eval (booleanPoint a) p = 0 := by
  rw [wireSpace_eq_span_indexed] at hp
  obtain ⟨coeff, hcoeff⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hp
  have heval (b : Assignment n) :
      MvPolynomial.eval (booleanPoint b) p = coefficientFunctional coeff (wireRow c b) := by
    rw [← hcoeff]
    exact eval_wire_combination c coeff b
  rw [heval]
  have hvanish : ∀ v ∈ GodMoveRowSpanSeparation.rowSpan c samples,
      coefficientFunctional coeff v = 0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
        have hv' : v ∈ samples.map (wireRow c) := by simpa using hv
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hv'
        rw [← heval]
        exact hzero b hb
    | zero => exact (coefficientFunctional coeff).map_zero
    | add v w _ _ hv hw => simp [map_add, hv, hw]
    | smul b v _ hv => simp [hv]
  exact hvanish (wireRow c a) ha

/-- For every supplied assignment, exact rational arithmetic checks precisely
whether it is a semantic sample-refinement counterexample. -/
theorem accepts_iff_counterexample {n : ℕ} (c : List (CGate n))
    (samples : List (Assignment n)) (B : RowBasis c.length)
    (hspan : GodMoveRationalRowBasis.rowSpan B =
      GodMoveRowSpanSeparation.rowSpan c samples)
    (a : Assignment n) :
    accepts B (wireRow c a) = true ↔ Counterexample c samples a := by
  constructor
  · exact counterexample_of_accepts c samples B hspan a
  · intro h
    rw [accepts_iff, hspan]
    intro ha
    obtain ⟨p, hp, hpa⟩ := h
    apply hpa
    exact eval_zero_of_row_mem c samples p.val p.property
      ((mem_residualSpace c samples p).mp hp) a ha

end GodMoveNumericCounterexample

#print axioms GodMoveNumericCounterexample.residualPolynomial_mem_wireSpace
#print axioms GodMoveNumericCounterexample.eval_residualPolynomial_self
#print axioms GodMoveNumericCounterexample.residualPolynomial_vanishes_samples
#print axioms GodMoveNumericCounterexample.counterexample_of_accepts
#print axioms GodMoveNumericCounterexample.eval_zero_of_row_mem
#print axioms GodMoveNumericCounterexample.accepts_iff_counterexample
