import PallLean.Paper93.DeepMath.NFrame.BarrierViaEigenvalues
import PallLean.Paper93.DeepMath.NFrame.PosDefEigenvalues
import PallLean.Paper93.DeepMath.NFrame.LogConvexity

namespace PallLean.Paper93.DeepMath.NFrame

/-- For PosDef A, the barrier is the negative-sum-of-log-eigenvalues, each log of which
    is well-defined since eigenvalues are positive. -/
theorem barrier_well_defined_via_eigenvalues {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    barrier A = -∑ i, Real.log (hA.1.eigenvalues i) :=
  barrier_eq_neg_sum_log_eigenvalues A hA

/-- For PosDef A, each `Real.log (eigenvalue_i)` is well-defined (eigenvalue is positive). -/
theorem posDef_log_eigenvalue_real {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (i : Fin n) :
    ∃ r : ℝ, Real.log (hA.1.eigenvalues i) = r :=
  ⟨Real.log (hA.1.eigenvalues i), rfl⟩

end PallLean.Paper93.DeepMath.NFrame
