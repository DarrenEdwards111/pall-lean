import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Real.Basic

/-!
# Cofactor / adjugate entry identities (N-Frame)

Two thin wrappers around Mathlib's adjugate / Cramer machinery, specialised to
real square matrices indexed by `Fin n`:

* `adjugate_apply_eq_cramer` — the `(i, j)` entry of the adjugate equals the
  `i`-th component of `cramer A` applied to the `j`-th standard basis vector.
* `adjugate_row_expand` — the row-`i` sum
  `∑ j, adj(A)_{i j} · M_{j i}` is the `(i, i)` entry of `adj(A) · M`.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

open Matrix

/-- The adjugate matrix's `(i, j)` entry equals `cramer A` applied to the
`j`-th standard basis vector, evaluated at coordinate `i`.

Reduction chain (all in Mathlib v4.28.0):
* `cramer_apply`     : `cramer A b i = (A.updateCol i b).det`.
* `adjugate_apply`   : `adjugate A i j = (A.updateRow j (Pi.single i 1)).det`.
* `adjugate_transpose` : `(adjugate A)ᵀ = adjugate Aᵀ`.
The two updated determinants are linked through `adjugate_transpose` /
`updateRow_transpose`. -/
theorem adjugate_apply_eq_cramer {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) :
    A.adjugate i j = Matrix.cramer A (Pi.single j 1) i := by
  -- Step 1: rewrite the RHS via `cramer_apply` to a determinant of an
  -- updated column.
  rw [Matrix.cramer_apply]
  -- Step 2: rewrite the LHS via `adjugate_apply` to a determinant of an
  -- updated row.
  rw [Matrix.adjugate_apply]
  -- Step 3: use `adjugate_transpose` (`(adjugate A)ᵀ = adjugate Aᵀ`),
  -- which after applying entries gives `adjugate A i j = adjugate Aᵀ j i`.
  -- Equivalently, by `adjugate_apply` for `Aᵀ`,
  --   `adjugate Aᵀ j i = (Aᵀ.updateRow i (Pi.single j 1)).det`
  -- and then by `updateRow_transpose` and `det_transpose` we land on
  --   `(A.updateCol i (Pi.single j 1)).det`,
  -- which is the desired RHS.
  --
  -- We assemble this as one rewrite chain.
  have hAdjT :
      (A.updateRow j (Pi.single i 1)).det
        = (Aᵀ.updateRow i (Pi.single j 1)).det := by
    -- This is the entrywise content of `adjugate_transpose`.
    have h1 : A.adjugate i j = Aᵀ.adjugate j i := by
      have htr : (A.adjugate)ᵀ = Aᵀ.adjugate := Matrix.adjugate_transpose A
      have := congrArg (fun (M : Matrix (Fin n) (Fin n) ℝ) => M j i) htr
      simpa [Matrix.transpose_apply] using this
    -- Now convert both sides via `adjugate_apply`.
    have hL : A.adjugate i j = (A.updateRow j (Pi.single i 1)).det :=
      Matrix.adjugate_apply A i j
    have hR : Aᵀ.adjugate j i = (Aᵀ.updateRow i (Pi.single j 1)).det :=
      Matrix.adjugate_apply Aᵀ j i
    -- Combine.
    rw [hL, hR] at h1
    exact h1
  rw [hAdjT]
  -- Now: `(Aᵀ.updateRow i (Pi.single j 1)).det = (A.updateCol i (Pi.single j 1)).det`.
  -- Use `updateRow_transpose` (Mᵀ row update vs `updateCol`):
  --   `updateRow Mᵀ j c = (updateCol M j c)ᵀ`.
  rw [Matrix.updateRow_transpose, Matrix.det_transpose]

/-- Row-sum expansion: `∑ j, adj(A)_{i j} · M_{j i} = (adj(A) · M)_{i i}`. -/
theorem adjugate_row_expand {n : ℕ} (A M : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    ∑ j, A.adjugate i j * M j i = (A.adjugate * M) i i := by
  simp [Matrix.mul_apply]

end PallLean.Paper93.DeepMath.NFrame
