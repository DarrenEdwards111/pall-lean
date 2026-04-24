import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace PallLean.Paper93.DeepMath

theorem real_log_one : Real.log 1 = 0 := Real.log_one

theorem real_log_pos_nonneg (x : ℝ) (hx : 1 ≤ x) : 0 ≤ Real.log x :=
  Real.log_nonneg hx

/-- Logarithm of a finite product over positive reals equals the sum of logarithms. -/
theorem real_log_prod_pos {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (h : ∀ i ∈ s, 0 < f i) :
    Real.log (∏ i ∈ s, f i) = ∑ i ∈ s, Real.log (f i) :=
  Real.log_prod (s := s) (f := f) (fun i hi => ne_of_gt (h i hi))

end PallLean.Paper93.DeepMath
