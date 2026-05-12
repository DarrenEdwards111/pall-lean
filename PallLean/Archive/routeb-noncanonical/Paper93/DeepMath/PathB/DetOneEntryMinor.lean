import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic

namespace PallLean.Paper93.DeepMath.PathB

/-- For 1×1 matrices, det A = 1 ↔ A 0 0 = 1. -/
theorem fin_one_det_one_iff (A : Matrix (Fin 1) (Fin 1) ℝ) :
    A.det = 1 ↔ A 0 0 = 1 := by
  rw [Matrix.det_fin_one]

/-- For 1×1 matrix with det = 1, the unique principal minor at any nonempty J is 1. -/
theorem fin_one_unit_minor_from_det (A : Matrix (Fin 1) (Fin 1) ℝ) (h : A.det = 1)
    (e : Fin 1 ≃ {i // i ∈ ({0} : Finset (Fin 1))}) :
    (A.submatrix (fun i => (e i).1) (fun i => (e i).1)).det = 1 := by
  -- For Fin 1, e is uniquely determined and (e i).1 = 0
  have h_eq : ∀ i : Fin 1, (e i).1 = (0 : Fin 1) := by
    intro i
    have : (e i).1 ∈ ({0} : Finset (Fin 1)) := (e i).2
    rwa [Finset.mem_singleton] at this
  -- the submatrix is essentially A itself (1×1 case)
  rw [show (A.submatrix (fun i => (e i).1) (fun i => (e i).1)) = A from by
    ext i j
    have hi : (i : Fin 1) = 0 := Subsingleton.elim i 0
    have hj : (j : Fin 1) = 0 := Subsingleton.elim j 0
    simp [Matrix.submatrix_apply, h_eq, hi, hj]]
  exact h

end PallLean.Paper93.DeepMath.PathB
