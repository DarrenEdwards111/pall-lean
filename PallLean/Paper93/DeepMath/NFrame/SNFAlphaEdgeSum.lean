import PallLean.Paper93.DeepMath.NFrame.SNF
import PallLean.Paper93.DeepMath.GraphSpectral.LaplacianEdgeSum

namespace PallLean.Paper93.DeepMath.NFrame

open PallLean.Paper93.DeepMath.GraphSpectral

/-- α-term of S_NF equals (α/2) times the edge sum ∑ᵢⱼ Aᵢⱼ(φᵢ−φⱼ)²
    for symmetric adjacency A. -/
theorem S_NF_alpha_eq_edge_sum {n : ℕ} (α : ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (hSym : A.IsSymm) (phi : Fin n → ℝ) :
    S_NF_alpha α A phi = (α / 2) * ∑ i, ∑ j, A i j * (phi i - phi j)^2 := by
  unfold S_NF_alpha
  have h := laplacian_quadForm_eq_edge_sum A hSym phi
  -- `h : 2 * (∑ i, phi i * ((laplacian A).mulVec phi i)) = ∑ i, ∑ j, A i j * (phi i - phi j)^2`
  linear_combination (α / 2) * h

end PallLean.Paper93.DeepMath.NFrame
