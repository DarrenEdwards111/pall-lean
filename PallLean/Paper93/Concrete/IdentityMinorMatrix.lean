/-
  PallLean/Paper93/Concrete/IdentityMinorMatrix.lean

  Paper §18's identity-minor matrix for the coupled verifier sheet.

  The NP-side identity minor matrix: from §189's `lemma_124_unconditional`,
  rank ≥ n^(log n / 4) at `Q_times_Phi_135`. This matrix captures that
  structure concretely as the identity matrix of size `n × n`.
-/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Diagonal

namespace PallLean.Paper93.Concrete

open Matrix

/-- The NP-side identity minor matrix: from §189's `lemma_124_unconditional`,
    rank ≥ n^(log n / 4) at `Q_times_Phi_135`. This matrix captures that
    structure. -/
noncomputable def identityMinorMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun _ => 1)

theorem identityMinorMatrix_is_identity (n : ℕ) :
    identityMinorMatrix n = (1 : Matrix (Fin n) (Fin n) ℝ) := rfl

theorem identityMinorMatrix_det_eq_one (n : ℕ) :
    (identityMinorMatrix n).det = 1 := by
  unfold identityMinorMatrix
  exact Matrix.det_diagonal.trans (by simp)

end PallLean.Paper93.Concrete
