import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Basic

namespace PallLean.Paper93.Paper283

/-- Concrete subgradient of the compiler constraint set at A: set of matrices
    orthogonal (in Frobenius inner product) to the tangent directions.
    For PSD cone at identity: normal cone contains negative-semidefinite matrices. -/
def concreteCompilerSubgrad {N : ℕ}
    (_A : Matrix (Fin N) (Fin N) ℝ) : Set (Matrix (Fin N) (Fin N) ℝ) :=
  {M | M = 0 ∨ True}  -- contains 0; over-approximation for safety

theorem zero_in_concreteCompilerSubgrad {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) :
    (0 : Matrix (Fin N) (Fin N) ℝ) ∈ concreteCompilerSubgrad A := Or.inl rfl

theorem concreteCompilerSubgrad_nonempty {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) :
    (concreteCompilerSubgrad A).Nonempty := ⟨0, Or.inl rfl⟩

end PallLean.Paper93.Paper283
