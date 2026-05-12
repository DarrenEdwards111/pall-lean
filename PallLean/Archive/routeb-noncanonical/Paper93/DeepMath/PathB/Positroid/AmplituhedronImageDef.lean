import PallLean.Paper93.DeepMath.PathB.Positroid.AmplituhedronToyMap
import Mathlib.Data.Set.Image

/-!
# Amplituhedron image

The amplituhedron `A_{n,k,m}` is the image of the totally-non-negative
Grassmannian under the amplituhedron map induced by a fixed positive
matrix `Z`. This file defines the image abstractly (as a set of
`k × (k+m)` matrices) and proves elementary properties:

* the image at the zero matrix is zero,
* the image at the identity (in the square case) is `Z`,
* the zero matrix is always in the amplituhedron image set.

All proofs reduce to the underlying linearity facts established for
`amplituhedronMap` in `AmplituhedronToyMap.lean`. The development is
kernel-only, relying solely on `propext`, `Classical.choice`, and
`Quot.sound`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- The image of the amplituhedron map at the zero matrix. -/
def amplituhedronImageAtZero {k n m : ℕ} (Z : Matrix (Fin n) (Fin (k + m)) ℝ) :
    Matrix (Fin k) (Fin (k + m)) ℝ :=
  amplituhedronMap (0 : Matrix (Fin k) (Fin n) ℝ) Z

/-- The image at zero is the zero matrix. -/
theorem amplituhedronImageAtZero_eq_zero {k n m : ℕ}
    (Z : Matrix (Fin n) (Fin (k + m)) ℝ) :
    amplituhedronImageAtZero Z = 0 :=
  amplituhedronMap_zero Z

/-- The image of the amplituhedron map preserves zero. -/
theorem amplituhedronMap_preserves_zero {k n m : ℕ}
    (Z : Matrix (Fin n) (Fin (k + m)) ℝ) :
    amplituhedronMap (0 : Matrix (Fin k) (Fin n) ℝ) Z = 0 :=
  amplituhedronMap_zero Z

/-- For the n=k square case, the image of the identity is Z itself. -/
theorem amplituhedronMap_identity_square {n m : ℕ}
    (Z : Matrix (Fin n) (Fin (n + m)) ℝ) :
    amplituhedronMap (1 : Matrix (Fin n) (Fin n) ℝ) Z = Z :=
  amplituhedronMap_one n m Z

/-- The set of all images: amplituhedron image is `{C * Z | C}`. -/
def amplituhedronImage {k n m : ℕ}
    (Z : Matrix (Fin n) (Fin (k + m)) ℝ) :
    Set (Matrix (Fin k) (Fin (k + m)) ℝ) :=
  {Y | ∃ C : Matrix (Fin k) (Fin n) ℝ, amplituhedronMap C Z = Y}

/-- The zero matrix is in the amplituhedron image. -/
theorem zero_mem_amplituhedronImage {k n m : ℕ}
    (Z : Matrix (Fin n) (Fin (k + m)) ℝ) :
    (0 : Matrix (Fin k) (Fin (k + m)) ℝ) ∈ amplituhedronImage Z :=
  ⟨0, amplituhedronMap_zero Z⟩

end PallLean.Paper93.DeepMath.PathB.Positroid
