import PallLean.Paper93.DeepMath.PathB.Positroid.AmplituhedronToyMap

/-!
# Amplituhedron image at `k = 1` (single-row Grassmannian)

For `k = 1`, the amplituhedron map specialises to the vector-matrix
product `c · Z`, where `c` is a `1 × n` row matrix and `Z` is an
`n × (1 + m)` matrix. This file collects the elementary structural
properties of that specialisation: the identity case `n = 1, m = 0`,
the zero input, the zero in the image, and bilinearity in the input
row.

All proofs are kernel-only (no `sorry`, no custom `axiom`, no `True`
placeholder); they reduce to the linearity lemmas of
`AmplituhedronToyMap`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- For k=1 (single-row case), the amplituhedron map is a vector-matrix product. -/
def amplituhedronMap_k1 {n m : ℕ} (c : Matrix (Fin 1) (Fin n) ℝ)
    (Z : Matrix (Fin n) (Fin (1 + m)) ℝ) : Matrix (Fin 1) (Fin (1 + m)) ℝ :=
  amplituhedronMap c Z

/-- For k=1, n=1, m=0, the amplituhedron map at the identity is identity. -/
theorem amplituhedronMap_k1_n1_m0 (Z : Matrix (Fin 1) (Fin (1 + 0)) ℝ) :
    amplituhedronMap (1 : Matrix (Fin 1) (Fin 1) ℝ) Z = Z :=
  amplituhedronMap_one 1 0 Z

/-- For k=1, m=0, the amplituhedron map at the zero matrix gives zero. -/
theorem amplituhedronMap_k1_zero {n : ℕ} (Z : Matrix (Fin n) (Fin (1 + 0)) ℝ) :
    amplituhedronMap (0 : Matrix (Fin 1) (Fin n) ℝ) Z = 0 :=
  amplituhedronMap_zero Z

/-- The amplituhedron image at k=1 contains the zero matrix. -/
theorem zero_in_amplituhedron_image_k1 {n m : ℕ} (Z : Matrix (Fin n) (Fin (1 + m)) ℝ) :
    ∃ c : Matrix (Fin 1) (Fin n) ℝ, amplituhedronMap c Z = 0 :=
  ⟨0, amplituhedronMap_zero Z⟩

/-- For k=1, the amplituhedron map is bilinear in the input row. -/
theorem amplituhedronMap_k1_bilinear {n m : ℕ} (α : ℝ)
    (c₁ c₂ : Matrix (Fin 1) (Fin n) ℝ) (Z : Matrix (Fin n) (Fin (1 + m)) ℝ) :
    amplituhedronMap (α • c₁ + c₂) Z =
      α • amplituhedronMap c₁ Z + amplituhedronMap c₂ Z := by
  unfold amplituhedronMap
  rw [Matrix.add_mul, Matrix.smul_mul]

end PallLean.Paper93.DeepMath.PathB.Positroid
