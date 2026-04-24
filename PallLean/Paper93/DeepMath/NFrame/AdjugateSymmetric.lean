import PallLean.Paper93.DeepMath.NFrame.AdjugateTranspose
import PallLean.Paper93.DeepMath.NFrame.SymmTransposeSelf

namespace PallLean.Paper93.DeepMath.NFrame

/-- For a symmetric matrix A, the adjugate is also symmetric. -/
theorem adjugate_isSymm_of_isSymm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) :
    A.adjugate.IsSymm := by
  unfold Matrix.IsSymm
  rw [Matrix.adjugate_transpose, transpose_eq_of_isSymm A hA]

end PallLean.Paper93.DeepMath.NFrame
