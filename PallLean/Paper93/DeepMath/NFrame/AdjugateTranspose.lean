import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Real.Basic

/-!
# Adjugate and transpose commute (N-Frame)

Thin Mathlib wrapper providing the identity `(Aᵀ).adjugate = (A.adjugate)ᵀ`.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- Adjugate of transpose equals transpose of adjugate. -/
theorem adjugate_transpose {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    A.transpose.adjugate = A.adjugate.transpose := (Matrix.adjugate_transpose A).symm

end PallLean.Paper93.DeepMath.NFrame
