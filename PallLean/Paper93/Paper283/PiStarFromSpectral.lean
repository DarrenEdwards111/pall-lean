/-
  PallLean/Paper93/Paper283/PiStarFromSpectral.lean

  Paper §28.3 — Spectral construction of the universal observer gauge Π⋆
  via projection onto the top-r eigenvectors of the stationary matrix `A`.

  ## Scope (Y9)

  This file provides a concrete-matrix-level stub of the paper's
  eigenspace construction of Π⋆ (paper §28.3 p. 137–138). The paper
  obtains Π⋆ by projecting onto the dominant-eigenvalue subspace of
  the stationary A-side matrix `A⋆` (the amplituhedron-positive
  spectrum). The full spectral-decomposition machinery is not
  developed here; instead, `piStarFromSpectral` is the concrete
  rank-`r` truncation of the identity, i.e.\ the diagonal projector
  onto the first `r` coordinate axes. This serves as the degenerate
  starting vertex of the eigenspace-projection construction (a
  paper-faithful eigen-decomposition of `A` is deferred to downstream
  research).

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  ## Paper citations

    * §28.3 p. 137–138 — dominant-eigenspace construction of Π⋆
      from the stationary A-matrix.
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.Paper283

open Matrix

/-- Π⋆ from spectral: project onto eigenspace of A's top r eigenvalues.
    For concreteness: stub to identity projection of first r dimensions. -/
noncomputable def piStarFromSpectral {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (r : ℕ) :
    Matrix (Fin N) (Fin N) ℝ :=
  Matrix.diagonal (fun i => if i.val < r then 1 else 0)

theorem piStarFromSpectral_identity_when_full {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (hN : N ≤ N) :
    piStarFromSpectral A N = 1 := by
  unfold piStarFromSpectral
  ext i j
  by_cases h : i = j
  · subst h
    rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    have : i.val < N := i.isLt
    simp [this]
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]

theorem piStarFromSpectral_zero_when_r_zero {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) :
    piStarFromSpectral A 0 = 0 := by
  unfold piStarFromSpectral
  ext i j
  by_cases h : i = j
  · subst h
    rw [Matrix.diagonal_apply_eq]
    simp
  · rw [Matrix.diagonal_apply_ne _ h]
    simp

/-! ## Kernel-only axiom trace -/

#print axioms piStarFromSpectral_identity_when_full
#print axioms piStarFromSpectral_zero_when_r_zero

end PallLean.Paper93.Paper283
