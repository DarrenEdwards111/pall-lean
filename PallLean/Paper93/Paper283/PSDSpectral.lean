/-
  PallLean/Paper93/Paper283/PSDSpectral.lean

  Y8 — Paper §28.3 / Paper283: Wrapper around Mathlib's PSD spectral
  decomposition, exposing the two spectral facts needed by the
  Π⋆ construction:

    * `posSemidef_eigenvalues_nonneg` : every PSD matrix has non-negative
      eigenvalues.
    * `posSemidef_rank_eq_nonzero_eigenvalues` : the rank of a PSD matrix
      equals the number of its non-zero eigenvalues.

  Both are immediate wrappers around Mathlib's
    * `Matrix.PosSemidef.eigenvalues_nonneg`
      (from `Mathlib.Analysis.Matrix.PosDef`)
    * `Matrix.IsHermitian.rank_eq_card_non_zero_eigs`
      (from `Mathlib.Analysis.Matrix.Spectrum`)

  The rank statement is packaged in the form expected by the
  Π⋆ construction: as the cardinality of a `Finset.filter` rather than
  as a `Fintype.card` of a subtype. The translation between the two is
  provided by `Fintype.card_subtype`.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  Expected `#print axioms posSemidef_eigenvalues_nonneg`:
      [propext, Classical.choice, Quot.sound]
-/

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace PallLean.Paper93.Paper283

open Matrix

/-- Every PSD matrix `A` has eigenvalues in `ℝ≥0` (spectral theorem
consequence). This is a direct wrapper around Mathlib's
`Matrix.PosSemidef.eigenvalues_nonneg`. -/
theorem posSemidef_eigenvalues_nonneg {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.PosSemidef) :
    ∀ i : Fin N, 0 ≤ hA.1.eigenvalues i :=
  fun i => hA.eigenvalues_nonneg i

/-- Number of non-zero eigenvalues = rank.

This wraps `Matrix.IsHermitian.rank_eq_card_non_zero_eigs`, translating
the Mathlib formulation (via `Fintype.card` of a subtype) into the
`Finset.filter` form used by the Π⋆ construction. -/
theorem posSemidef_rank_eq_nonzero_eigenvalues {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.PosSemidef) :
    A.rank = ((Finset.univ.filter (fun i => hA.1.eigenvalues i ≠ 0)).card : ℕ) := by
  classical
  -- Mathlib gives the rank as `Fintype.card { i // hA.1.eigenvalues i ≠ 0 }`.
  have hrank :
      A.rank = Fintype.card { i : Fin N // hA.1.eigenvalues i ≠ 0 } :=
    hA.1.rank_eq_card_non_zero_eigs
  -- `Fintype.card_subtype` rewrites this as the cardinality of the
  -- filtered `Finset.univ`.
  rw [hrank, Fintype.card_subtype]

end PallLean.Paper93.Paper283
