import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

/-!
# Toy amplituhedron map

The amplituhedron `A_{n,k,m}` is the image of the (totally non-negative)
Grassmannian `Gr⁺(k,n)` under the linear map induced by a fixed positive
matrix `Z ∈ Mat(n × (k+m))`. Concretely, on a representative `k × n`
matrix `C` it sends

    C ↦ C * Z : Mat(k × (k+m)).

This file provides a kernel-only toy version of that map together with
elementary linearity facts (zero, identity, scalar multiplication, and
additivity in the `C` argument).
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- The toy amplituhedron map: sends a k×n matrix `C` and a fixed n×(k+m)
matrix `Z` to the k×(k+m) matrix `C * Z`. -/
def amplituhedronMap {k n m : ℕ}
    (C : Matrix (Fin k) (Fin n) ℝ) (Z : Matrix (Fin n) (Fin (k + m)) ℝ) :
    Matrix (Fin k) (Fin (k + m)) ℝ :=
  C * Z

/-- The image of the amplituhedron map at the zero matrix is zero. -/
theorem amplituhedronMap_zero {k n m : ℕ} (Z : Matrix (Fin n) (Fin (k + m)) ℝ) :
    amplituhedronMap (0 : Matrix (Fin k) (Fin n) ℝ) Z = 0 := by
  unfold amplituhedronMap
  exact Matrix.zero_mul Z

/-- The image of the amplituhedron map at the (square) identity case `k = n`. -/
theorem amplituhedronMap_one (n m : ℕ) (Z : Matrix (Fin n) (Fin (n + m)) ℝ) :
    amplituhedronMap (1 : Matrix (Fin n) (Fin n) ℝ) Z = Z := by
  unfold amplituhedronMap
  exact Matrix.one_mul Z

/-- The amplituhedron map is linear in `C`: `amp(α • C, Z) = α • amp(C, Z)`. -/
theorem amplituhedronMap_smul {k n m : ℕ} (α : ℝ)
    (C : Matrix (Fin k) (Fin n) ℝ) (Z : Matrix (Fin n) (Fin (k + m)) ℝ) :
    amplituhedronMap (α • C) Z = α • (amplituhedronMap C Z) := by
  unfold amplituhedronMap
  exact Matrix.smul_mul α C Z

/-- The amplituhedron map is additive in `C`:
`amp(C₁ + C₂, Z) = amp(C₁, Z) + amp(C₂, Z)`. -/
theorem amplituhedronMap_add {k n m : ℕ}
    (C₁ C₂ : Matrix (Fin k) (Fin n) ℝ) (Z : Matrix (Fin n) (Fin (k + m)) ℝ) :
    amplituhedronMap (C₁ + C₂) Z = amplituhedronMap C₁ Z + amplituhedronMap C₂ Z := by
  unfold amplituhedronMap
  exact Matrix.add_mul C₁ C₂ Z

end PallLean.Paper93.DeepMath.PathB.Positroid
