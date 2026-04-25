import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Properties of the all-ones matrix `J_n = 1·1ᵀ`

This file collects the basic properties of the all-ones matrix
`J_n : Matrix (Fin n) (Fin n) ℝ`, viewed as the rank-1 outer product
`1·1ᵀ`. In Mathlib this is realised as
`Matrix.vecMulVec (Function.const (Fin n) 1) (Function.const (Fin n) 1)`,
since `Matrix.vecMulVec u v i j = u i * v j` (see
`Mathlib/Data/Matrix/Mul.lean`).

These properties are the building blocks needed for the spectral /
matrix-determinant path to the general-`n` determinant of the
compiled gadget `compiledGadget α n = α • I + J_n`. Specifically:

* `allOnesMatrix_n_apply` — every entry equals `1`.
* `allOnesMatrix_n_mulVec_one` — the all-ones vector is an eigenvector
  with eigenvalue `n`.
* `allOnesMatrix_n_mulVec_sumZero` — every sum-zero vector lies in the
  kernel of `J_n`. Together with the eigenvector above this gives the
  full `(n−1)`-dimensional zero eigenspace + 1-dimensional `n`-eigenspace
  decomposition.
* `allOnesMatrix_n_trace` — the trace of `J_n` is `n`.
* `allOnesMatrix_n_isSymm` — the matrix is symmetric.

Each proof goes via `Matrix.vecMulVec_apply` followed by `simp`,
`Finset.sum_const`, or `ring`, together with the standard `funext` for
function-extensionality. No `sorry`s, no axioms beyond the Lean kernel
trio (`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open Matrix
open scoped BigOperators

/-- **Entrywise formula.** Every entry of the all-ones matrix
`J_n = 1·1ᵀ` (built as `vecMulVec` of two `Function.const`-`1`
vectors) is the constant `1 : ℝ`.

This is just `Matrix.vecMulVec_apply` reduced by `1 * 1 = 1`. -/
theorem allOnesMatrix_n_apply (n : ℕ) (i j : Fin n) :
    (Matrix.vecMulVec (Function.const (Fin n) (1 : ℝ))
        (Function.const (Fin n) 1)) i j = 1 := by
  -- `vecMulVec_apply` rewrites the LHS to `1 * 1`, which `simp` reduces.
  simp [Matrix.vecMulVec_apply]

/-- **Eigenvector identity for the all-ones vector.**

`J_n · 1 = n · 1`, where `1` is the all-ones vector
`Function.const (Fin n) 1`. Equivalently, the all-ones vector is an
eigenvector of `J_n` with eigenvalue `n`.

The proof is by `funext`, then unfolding `mulVec`/`dotProduct` and
recognising the inner sum as `n` copies of `1 * 1` summed over
`Finset.univ : Finset (Fin n)`. -/
theorem allOnesMatrix_n_mulVec_one (n : ℕ) :
    (Matrix.vecMulVec (Function.const (Fin n) (1 : ℝ))
        (Function.const (Fin n) 1)).mulVec
      (Function.const (Fin n) 1) = fun _ => (n : ℝ) := by
  -- Reduce both sides pointwise.
  funext i
  -- `mulVec`/`dotProduct` against an all-ones vector becomes
  -- `∑ j, J_n i j * 1 = ∑ j, 1`.
  -- `simp` with `vecMulVec_apply` and the trivialities of `Function.const`
  -- reduces the sum to `∑ j : Fin n, (1 : ℝ)`, which equals `n` by
  -- `Finset.sum_const_one`/`Finset.card_univ`.
  simp [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin]

/-- **Kernel on sum-zero vectors.**

`J_n · v = 0` whenever `∑ i, v i = 0`. Combined with
`allOnesMatrix_n_mulVec_one`, this exhibits the rank-1 spectral
decomposition of `J_n = 1·1ᵀ`: a single eigenvalue `n` on the all-ones
direction, and `0` on the codimension-1 sum-zero hyperplane. -/
theorem allOnesMatrix_n_mulVec_sumZero (n : ℕ) (v : Fin n → ℝ)
    (hv : ∑ i, v i = 0) :
    (Matrix.vecMulVec (Function.const (Fin n) (1 : ℝ))
        (Function.const (Fin n) 1)).mulVec v = 0 := by
  funext i
  -- The `i`-th component of `J_n · v` is `∑ j, 1 * v j = ∑ j, v j = 0`.
  -- Reduce `mulVec`, `dotProduct` and `vecMulVec` to the bare sum,
  -- then apply the hypothesis `hv`.
  show ((Matrix.vecMulVec (Function.const (Fin n) (1 : ℝ))
        (Function.const (Fin n) 1)).mulVec v) i = (0 : Fin n → ℝ) i
  have hrewrite :
      ((Matrix.vecMulVec (Function.const (Fin n) (1 : ℝ))
            (Function.const (Fin n) 1)).mulVec v) i = ∑ j, v j := by
    simp [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply]
  rw [hrewrite, hv]
  rfl

/-- **Trace.**

`trace J_n = n`. The proof reduces `trace` to `∑ i, J_n i i = ∑ i, 1 = n`
via `Finset.sum_const`. -/
theorem allOnesMatrix_n_trace (n : ℕ) :
    (Matrix.vecMulVec (Function.const (Fin n) (1 : ℝ))
        (Function.const (Fin n) 1)).trace = (n : ℝ) := by
  -- Unfold `trace` and `diag`. Each diagonal entry is `1` by
  -- `vecMulVec_apply`. The sum of `n` ones over `Fin n` is `n`.
  simp [Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin]

/-- **Symmetry.**

`J_n` is symmetric: `J_nᵀ = J_n`. This holds because every entry equals
`1`, so swapping rows and columns leaves the matrix unchanged. -/
theorem allOnesMatrix_n_isSymm (n : ℕ) :
    (Matrix.vecMulVec (Function.const (Fin n) (1 : ℝ))
        (Function.const (Fin n) 1)).IsSymm := by
  -- `IsSymm A` unfolds to `Aᵀ = A`. We prove this entrywise via
  -- `Matrix.ext` together with the entrywise identity `J_n i j = 1`
  -- (`allOnesMatrix_n_apply`).
  refine Matrix.ext ?_
  intro i j
  -- `Aᵀ i j = A j i`. Both sides equal `1` by `allOnesMatrix_n_apply`.
  show (Matrix.vecMulVec (Function.const (Fin n) (1 : ℝ))
          (Function.const (Fin n) 1))ᵀ i j
      = (Matrix.vecMulVec (Function.const (Fin n) (1 : ℝ))
          (Function.const (Fin n) 1)) i j
  simp [Matrix.transpose_apply, Matrix.vecMulVec_apply]

end PallLean.Paper93.DeepMath.PathB.Positroid
