import PallLean.Paper93.DeepMath.NFrame.BarrierViaEigenvalues
import PallLean.Paper93.DeepMath.NFrame.NegLogConvex

namespace PallLean.Paper93.DeepMath.NFrame

/-- For PosDef A and B with all eigenvalues equal pointwise (i.e. same spectrum),
    barriers agree. (Sanity check; trivial.) -/
theorem barrier_same_eigenvalues {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (hB : B.PosDef)
    (hSpec : ∀ i, hA.1.eigenvalues i = hB.1.eigenvalues i) :
    barrier A = barrier B := by
  rw [barrier_eq_neg_sum_log_eigenvalues A hA]
  rw [barrier_eq_neg_sum_log_eigenvalues B hB]
  congr 1
  apply Finset.sum_congr rfl
  intros i _
  rw [hSpec i]

end PallLean.Paper93.DeepMath.NFrame
