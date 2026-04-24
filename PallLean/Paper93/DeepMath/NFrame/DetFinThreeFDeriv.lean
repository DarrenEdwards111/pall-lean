import PallLean.Paper93.DeepMath.NFrame.DetFinThree

/-!
# 3×3 determinant has a Fréchet derivative

This file packages `det_fin_three_differentiable` from
`DetFinThree.lean` as the existence of a continuous linear map
serving as the Fréchet derivative of `Matrix.det` on
`Matrix (Fin 3) (Fin 3) ℝ` at every point.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

open scoped Matrix.Norms.Elementwise

namespace PallLean.Paper93.DeepMath.NFrame

/-- 3×3 det has Fréchet derivative at every point. -/
theorem det_fin_three_hasFDerivAt (A : Matrix (Fin 3) (Fin 3) ℝ) :
    ∃ L : Matrix (Fin 3) (Fin 3) ℝ →L[ℝ] ℝ,
      HasFDerivAt (Matrix.det : Matrix (Fin 3) (Fin 3) ℝ → ℝ) L A :=
  ⟨fderiv ℝ Matrix.det A,
   det_fin_three_differentiable.differentiableAt.hasFDerivAt⟩

end PallLean.Paper93.DeepMath.NFrame
