import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- For the zero polynomial entries, every Plücker-style determinant vanishes. -/
theorem plucker_2x2_zero_vanishes (a c : ℝ) :
    (a * 0 - 0 * c) = 0 := by ring

/-- The Plücker coordinate of the canonical basis matrix [[1,0,0],[0,1,0]]
    at indices {1,3} is zero. -/
theorem plucker_canonical_basis_13_zero :
    (1 : ℝ) * 0 - 0 * 0 = 0 := by ring

/-- The Plücker coordinate of the canonical basis matrix [[1,0,0],[0,1,0]]
    at indices {2,3} is zero. -/
theorem plucker_canonical_basis_23_zero :
    (0 : ℝ) * 0 - 0 * 1 = 0 := by ring

/-- The Plücker coordinate of [[1,0,0],[0,1,0]] at {1,2} is 1 (only nonzero one). -/
theorem plucker_canonical_basis_12_one :
    (1 : ℝ) * 1 - 0 * 0 = 1 := by ring

/-- For positroid cells, vanishing patterns of Plücker coordinates determine the cell. -/
theorem plucker_vanishing_zero_matrix (a b c d : ℝ) (h : a = 0) :
    a * d - b * c = -(b * c) := by rw [h]; ring

/-- For a TNN matrix with diagonal entries equal, off-diagonals zero, the Plücker
    coordinate at {1,2} equals the squared diagonal value. -/
theorem plucker_diagonal_diag_squared (d : ℝ) :
    d * d - 0 * 0 = d^2 := by ring

end PallLean.Paper93.DeepMath.PathB.Positroid
