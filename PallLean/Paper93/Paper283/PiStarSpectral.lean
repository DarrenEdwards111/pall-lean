/-
  PallLean/Paper93/Paper283/PiStarSpectral.lean

  Paper §28.3 — Π⋆ as a linear map built from a spectral projection
  matrix on the dominant eigenspace of the stationary A-side matrix
  `A⋆` (amplituhedron-positive spectrum).

  ## Scope (Z10)

  This file packages a given projection matrix `P` on the ambient
  coordinate space `Fin N → ℝ` as a Lean linear map

      piStarFromMatrix P : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ),

  so that downstream files can consume Π⋆ as an honest `LinearMap`
  whenever a projection onto the dominant eigenvectors of `A⋆` has
  been supplied.  The construction is paper-faithful in the following
  sense: the paper §28.3 (p. 137–138) defines Π⋆ by projecting onto
  the span of the top-`r` eigenvectors of `A⋆`; given such a
  projection matrix `P`, `piStarFromMatrix P` is precisely the linear
  action of Π⋆ on the Hilbert realisation of the state space.

  The construction of the projection matrix itself (the spectral
  decomposition of `A⋆`) is carried out upstream (see
  `PiStarFromSpectral.lean` for the concrete coordinate-truncation
  stub and `PiStarFromStationarity.lean` for the Prop-level
  stationarity-to-gauge existence bridge).

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
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace PallLean.Paper93.Paper283

open Matrix

/-- **Paper §28.3 p. 137–138 — Π⋆ as a linear map from a spectral
projection matrix.**

Given a matrix `P : Matrix (Fin N) (Fin N) ℝ` (intended to be the
projection onto the dominant eigenspace of the stationary A-side
matrix `A⋆`), `piStarFromMatrix P` is the corresponding real-linear
map `(Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ)` acting by matrix–vector
multiplication. -/
noncomputable def piStarFromMatrix {N : ℕ}
    (P : Matrix (Fin N) (Fin N) ℝ) :
    (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) where
  toFun x := P.mulVec x
  map_add' x y := Matrix.mulVec_add P x y
  map_smul' c x := by simp [Matrix.mulVec_smul]

/-- **Identity specialisation.**

When the projection matrix is the identity (full-rank ``dominant''
eigenspace), `piStarFromMatrix` recovers the identity linear map on
the state space. -/
theorem piStarFromMatrix_identity (N : ℕ) (x : Fin N → ℝ) :
    piStarFromMatrix (1 : Matrix (Fin N) (Fin N) ℝ) x = x := by
  unfold piStarFromMatrix
  simp [Matrix.one_mulVec]

/-! ## Kernel-only axiom trace -/

#print axioms piStarFromMatrix_identity

end PallLean.Paper93.Paper283
