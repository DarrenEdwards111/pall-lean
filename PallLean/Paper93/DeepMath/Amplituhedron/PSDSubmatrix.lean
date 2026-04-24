import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Principal submatrices of PSD / PD matrices

Thin wrappers around Mathlib:

* `Matrix.PosSemidef.submatrix` gives us the PSD case directly.
* For the PD case Mathlib does not currently expose a direct wrapper, so we
  prove it here by hand from the underlying `Finsupp` definition, using
  injectivity of the index map to transport nonzero `Finsupp`s.
-/

namespace PallLean.Paper93.DeepMath.Amplituhedron

open Matrix

/-- If `M` is positive semidefinite and `f : Fin k → Fin n` is any function,
then the principal submatrix `M.submatrix f f` is positive semidefinite. -/
theorem posSemidef_submatrix {n k : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.PosSemidef) (f : Fin k → Fin n) :
    (M.submatrix f f).PosSemidef := by
  exact hM.submatrix f

/-- If `M` is positive definite and `f : Fin k → Fin n` is injective,
then the principal submatrix `M.submatrix f f` is positive definite.

Mathlib (v4.28.0) only provides `Matrix.PosSemidef.submatrix`; the positive
definite analogue is proved directly from the `Finsupp`-based definition of
`Matrix.PosDef` below. -/
theorem posDef_submatrix {n k : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.PosDef) {f : Fin k → Fin n} (hf : Function.Injective f) :
    (M.submatrix f f).PosDef := by
  refine ⟨hM.1.submatrix _, fun x hx => ?_⟩
  -- Transport the `Finsupp` `x : Fin k →₀ ℝ` to `Fin n →₀ ℝ` via `mapDomain f`.
  have hxne : x.mapDomain f ≠ 0 := fun h =>
    hx <| Finsupp.mapDomain_injective hf (by simpa using h)
  have hpos := hM.2 hxne
  -- Rewrite the double sum on the LHS in terms of `x.mapDomain f`
  -- using the standard `sum_mapDomain_index` simp lemma.
  simpa [Finsupp.sum_mapDomain_index, add_mul, mul_add, Matrix.submatrix]
    using hpos

end PallLean.Paper93.DeepMath.Amplituhedron
