/-
  PallLean/Paper93/Concrete/PSDMatrix.lean

  Wrapper around Mathlib's positive-semidefinite matrix notions for
  the Paper §93 barrier term.

  A `PSDMatrix n` carries a concrete Gram-style witness `M = B · Bᵀ`
  which makes positive semidefiniteness reducible to the classical
  Mathlib fact `Matrix.posSemidef_self_mul_conjTranspose` (specialised
  to the real case via `TrivialStar ℝ`). The quadratic form
  `(M *ᵥ x) ⬝ᵥ x` is then nonnegative by the corresponding dot-product
  characterisation in Mathlib.
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.StarOrdered
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace PallLean.Paper93.Concrete

open Matrix

/-- PSD witness: matrix `M` is PSD if `M = B · Bᵀ` for some `B`.

    This Gram-style packaging makes the quadratic-form nonnegativity
    (`(M *ᵥ x) ⬝ᵥ x ≥ 0`) immediate from Mathlib's
    `Matrix.posSemidef_self_mul_conjTranspose`, avoiding spectral
    machinery while still matching the intended semantics of the
    Paper §93 barrier term. -/
structure PSDMatrix (n : ℕ) where
  /-- The underlying real `n × n` matrix claimed to be PSD. -/
  M : Matrix (Fin n) (Fin n) ℝ
  /-- A Gram-factor: `M = B · Bᵀ`. -/
  B : Matrix (Fin n) (Fin n) ℝ
  /-- The PSD-witness identity: `M = B · Bᵀ`. -/
  decomp : M = B * B.transpose

/-- A `PSDMatrix` gives rise to the corresponding `Matrix.PosSemidef`
    certificate in Mathlib. This is the core bridge: the Gram-style
    witness `M = B · Bᵀ` is upgraded to `M.PosSemidef` by converting
    the transpose to a conjugate transpose via `TrivialStar ℝ` and
    applying `posSemidef_self_mul_conjTranspose`. -/
theorem PSDMatrix.posSemidef {n : ℕ} (P : PSDMatrix n) : P.M.PosSemidef := by
  -- Convert `B.transpose` to `B.conjTranspose` using `TrivialStar ℝ`.
  have hBT : P.B.transpose = P.B.conjTranspose := by
    ext i j
    simp [Matrix.transpose_apply, Matrix.conjTranspose_apply,
      star_trivial]
  -- Rewrite `M = B * Bᴴ` and apply Mathlib's PSD lemma.
  have hMgram : P.M = P.B * P.B.conjTranspose := by
    rw [P.decomp, hBT]
  rw [hMgram]
  exact Matrix.posSemidef_self_mul_conjTranspose P.B

/-- Quadratic-form nonnegativity: for any vector `x`, the real scalar
    `(M *ᵥ x) ⬝ᵥ x` is nonnegative. This is the PSD property used by
    the barrier term. -/
theorem PSDMatrix.quadForm_nonneg {n : ℕ} (P : PSDMatrix n)
    (x : Fin n → ℝ) : 0 ≤ P.M.mulVec x ⬝ᵥ x := by
  -- Apply Mathlib's dot-product characterisation to `P.M.PosSemidef`.
  have hPSD : P.M.PosSemidef := P.posSemidef
  have hdot : 0 ≤ star x ⬝ᵥ (P.M.mulVec x) :=
    hPSD.dotProduct_mulVec_nonneg x
  -- Reduce `star x` to `x` using `TrivialStar ℝ`, then swap dot-product order.
  have hstar : (star x : Fin n → ℝ) = x := by
    funext i; exact star_trivial _
  rw [hstar] at hdot
  -- `x ⬝ᵥ (M *ᵥ x) = (M *ᵥ x) ⬝ᵥ x` by commutativity of dot product on ℝ.
  rwa [dotProduct_comm] at hdot

/-- Identity PSD matrix: `1 = 1 · 1ᵀ`. -/
def identityPSD (n : ℕ) : PSDMatrix n :=
  ⟨1, 1, by simp⟩

end PallLean.Paper93.Concrete
