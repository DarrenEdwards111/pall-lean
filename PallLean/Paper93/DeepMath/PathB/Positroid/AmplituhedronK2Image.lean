import PallLean.Paper93.DeepMath.PathB.Positroid.AmplituhedronToyMap
import PallLean.Paper93.DeepMath.PathB.Positroid.AmplituhedronImageDef

/-!
# Amplituhedron image at `k = 2`

For `k = 2`, the amplituhedron map specialises to a `2 × n` matrix `C`
acting on a fixed `n × (2 + m)` matrix `Z` to produce a
`2 × (2 + m)` matrix. This file collects the elementary structural
properties of that specialisation: the zero input case, the square
identity case `n = 2`, and the membership of the zero matrix in the
amplituhedron image set.

All proofs are kernel-only (no `sorry`, no custom `axiom`, no `True`
placeholder); they reduce to the linearity lemmas of
`AmplituhedronToyMap` and the image-set facts of
`AmplituhedronImageDef`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- For k=2 (two-row case), the amplituhedron map sends a `2 × n` matrix
`C` and a fixed `n × (2 + m)` matrix `Z` to the `2 × (2 + m)` matrix
`C * Z`. -/
def amplituhedronMap_k2 {n m : ℕ} (C : Matrix (Fin 2) (Fin n) ℝ)
    (Z : Matrix (Fin n) (Fin (2 + m)) ℝ) : Matrix (Fin 2) (Fin (2 + m)) ℝ :=
  amplituhedronMap C Z

/-- For k=2, the amplituhedron map at the zero matrix gives zero. -/
theorem amplituhedronMap_k2_zero {n m : ℕ} (Z : Matrix (Fin n) (Fin (2 + m)) ℝ) :
    amplituhedronMap (0 : Matrix (Fin 2) (Fin n) ℝ) Z = 0 :=
  amplituhedronMap_zero Z

/-- For k=2, n=2, the amplituhedron map at the identity is identity (returns Z). -/
theorem amplituhedronMap_k2_n2_id (m : ℕ) (Z : Matrix (Fin 2) (Fin (2 + m)) ℝ) :
    amplituhedronMap (1 : Matrix (Fin 2) (Fin 2) ℝ) Z = Z :=
  amplituhedronMap_one 2 m Z

/-- For k=2, the zero matrix is in the amplituhedron image. -/
theorem zero_in_amp_image_k2 {n m : ℕ} (Z : Matrix (Fin n) (Fin (2 + m)) ℝ) :
    (0 : Matrix (Fin 2) (Fin (2 + m)) ℝ) ∈ amplituhedronImage Z :=
  zero_mem_amplituhedronImage Z

end PallLean.Paper93.DeepMath.PathB.Positroid
