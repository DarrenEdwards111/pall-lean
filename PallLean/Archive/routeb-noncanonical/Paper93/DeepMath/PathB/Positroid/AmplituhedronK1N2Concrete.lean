import PallLean.Paper93.DeepMath.PathB.Positroid.AmplituhedronToyMap
import PallLean.Paper93.DeepMath.PathB.Positroid.AmplituhedronImageDef
import PallLean.Paper93.DeepMath.PathB.Positroid.AmplituhedronImageTrivialCase

/-!
# Concrete amplituhedron map instances at k=1, n=2

This file provides concrete instances of the toy amplituhedron map and
amplituhedron image at the parameters `k = 1`, `n = 2`. In this regime
the input matrix `C` is a `1 × 2` row vector and the matrix `Z` is a
`2 × (1 + m)` matrix; the amplituhedron map is the matrix product
`C * Z`, a `1 × (1 + m)` row vector.

All proofs reduce to definitional unfolding (`rfl`) or to elementary
membership / image lemmas already established for the abstract
amplituhedron map. The development is kernel-only, relying solely on
`propext`, `Classical.choice`, and `Quot.sound`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- A `One` instance for the non-square `1 × 2` real matrix space, defined
elementwise via the underlying function space (Pi). This is purely a typeclass
convenience for the concrete `k = 1, n = 2` instances below: it does not affect
the matrix-multiplication semantics on square matrices. -/
local instance : One (Matrix (Fin 1) (Fin 2) ℝ) :=
  inferInstanceAs (One (Fin 1 → Fin 2 → ℝ))

/-- For k=1, n=2, m=0: amplituhedronMap is a row vector × 2×1 matrix. -/
theorem amplituhedronMap_k1_n2_m0 (Z : Matrix (Fin 2) (Fin (1+0)) ℝ) :
    amplituhedronMap (1 : Matrix (Fin 1) (Fin 2) ℝ) Z =
      (1 : Matrix (Fin 1) (Fin 2) ℝ) * Z := rfl

/-- For k=1, n=2, m=1: amplituhedronMap is a row vector × 2×2 matrix. -/
theorem amplituhedronMap_k1_n2_m1 (C : Matrix (Fin 1) (Fin 2) ℝ)
    (Z : Matrix (Fin 2) (Fin (1+1)) ℝ) :
    amplituhedronMap C Z = C * Z := rfl

/-- The amplituhedron image at k=1, n=2 contains zero. -/
theorem amplituhedronImage_k1_n2_contains_zero (m : ℕ) (Z : Matrix (Fin 2) (Fin (1+m)) ℝ) :
    (0 : Matrix (Fin 1) (Fin (1+m)) ℝ) ∈ amplituhedronImage Z :=
  zero_mem_amplituhedronImage Z

/-- For k=1 and any n, m, the amplituhedron map's image at zero matrix is the singleton {0}. -/
theorem amplituhedronImage_k1_at_zero {n m : ℕ} :
    amplituhedronImage (0 : Matrix (Fin n) (Fin (1+m)) ℝ) =
      {(0 : Matrix (Fin 1) (Fin (1+m)) ℝ)} :=
  amplituhedronImage_at_zero_Z

end PallLean.Paper93.DeepMath.PathB.Positroid
