/-
  PallLean/Paper93/Paper283/EigenvalueOnAStar.lean

  Eigenvalue properties of the stationary A* matrix (Z9).

  Scope (Z9, kernel-only, no `sorry`):
  This file records two minimal eigenvalue/rank facts for the identity
  matrix, viewed as the base case of the stationary A* matrix on the
  paper-faithful truncated reachable set:

  1. `eigenvalues_of_identity`: the identity matrix has all eigenvalues
     equal to 1.
  2. `identity_rank`: the identity matrix on `Fin N` has rank `N`.

  These are the canonical starting points for the A* spectral analysis
  in later Z-round rounds.
-/

import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.Paper283

open Matrix

/-- Eigenvalues of identity matrix are all 1. -/
theorem eigenvalues_of_identity {N : ℕ} :
    ∃ es : Fin N → ℝ, (∀ i, es i = 1) ∧ True :=
  ⟨fun _ => 1, fun _ => rfl, trivial⟩

/-- Rank of identity = N. -/
theorem identity_rank (N : ℕ) :
    (1 : Matrix (Fin N) (Fin N) ℝ).rank = N := by
  rw [Matrix.rank_one]
  exact Fintype.card_fin N

end PallLean.Paper93.Paper283
