/-
  PallLean/Paper93/Concrete/RealProjectionMatrix.lean

  V7 — Non-identity projection matrix associated with a gauge.

  ## Scope

  The Paper §7.1 / §28.3 N-Frame candidate gauge `Π` is an abstract
  ℚ-linear idempotent on the SPDP row space `MvPolynomial (Fin N) ℚ`
  with finite-rank range. To move from that abstract projection to a
  *concrete* `N × N` real matrix carrying the rank information, we
  collapse the gauge's `ℚ`-rank `r := Module.finrank ℚ
  (LinearMap.range gauge.projection)` onto a diagonal projector whose
  first `r` entries (clamped to `Fin N`) are `1` and the rest are `0`.

  This complements `Paper93/Concrete/ProjectedMatrix.lean`, which uses
  the trivial rank-full identity `projMatrix gauge := 1`. The matrix
  here is rank-respecting: the zero gauge yields the zero matrix, and
  the rank-`N` full gauge yields the identity.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  Expected `#print axioms realProjMatrix_det`:
      [propext, Classical.choice, Quot.sound]

  ## Note on the determinant formula

  The canonical statement suggested by the task sheet reads
  `det = if finrank = N then 1 else 0`. However `finrank` of the range
  is not a priori bounded above by `N` (the SPDP ambient is
  infinite-dimensional), so when `finrank > N` the diagonal is still
  all-ones and the determinant is `1` rather than `0`. We therefore
  prove the strictly correct (and equivalent on the physically relevant
  range `finrank ≤ N`) statement
  `det = if N ≤ finrank then 1 else 0`.

  ## Paper citations

    * §7.1 p. 25 — universal observer gauge `Π⋆` as an idempotent
      linear projection of finite ℚ-rank.
    * §28.3 pp. 137–138 — N-Frame Lagrangian and rank-collapse term.
-/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import PallLean.Paper93.NFrame.LagrangianFunctional

namespace PallLean.Paper93.Concrete

open Matrix

/-- **Real rank-respecting projection matrix** associated with a
candidate gauge.

We extract the ℚ-dimension `r := Module.finrank ℚ (range
gauge.projection)` of the gauge's range, and output the `N × N` real
diagonal matrix whose `i`-th entry is `1` when `i.val < r` and `0`
otherwise. This is the canonical rank-`min(r, N)` diagonal projector
consistent with paper §7.1 p. 25 (`Π⋆` is a finite-rank projection on
the SPDP row space). -/
noncomputable def realProjMatrix {N : ℕ}
    (gauge : PallLean.Paper93.NFrame.CandidateGauge N) :
    Matrix (Fin N) (Fin N) ℝ :=
  let r := Module.finrank ℚ (LinearMap.range gauge.projection)
  Matrix.diagonal (fun i => if i.val < r then (1 : ℝ) else 0)

/-- **Determinant of the rank-respecting projection matrix.**

The determinant is `1` when the gauge's ℚ-rank is at least `N`
(i.e.\ the diagonal is the all-ones diagonal), and `0` otherwise.
This matches the full-rank / rank-deficient dichotomy of paper
§28.3 Bridge B (determinantal barrier ⇒ global rank). -/
theorem realProjMatrix_det
    {N : ℕ} {gauge : PallLean.Paper93.NFrame.CandidateGauge N} :
    (realProjMatrix (N := N) gauge).det =
      (if N ≤ Module.finrank ℚ (LinearMap.range gauge.projection)
         then (1 : ℝ) else 0) := by
  -- Reduce the determinant of a diagonal matrix to the product of its
  -- diagonal entries.
  unfold realProjMatrix
  rw [Matrix.det_diagonal]
  -- Name the rank for brevity.
  set r : ℕ := Module.finrank ℚ (LinearMap.range gauge.projection) with hr
  -- Split on whether `N ≤ r`.
  by_cases hNr : N ≤ r
  · -- Full-rank case: every `i : Fin N` satisfies `i.val < N ≤ r`,
    -- so each factor is `1` and the product is `1`.
    have hprod :
        (∏ i : Fin N, (if (i : Fin N).val < r then (1 : ℝ) else 0)) = 1 := by
      refine Finset.prod_eq_one ?_
      intro i _
      have hi : (i : Fin N).val < r := lt_of_lt_of_le i.isLt hNr
      simp [hi]
    rw [hprod]
    simp [hNr]
  · -- Rank-deficient case: there is an index `i = ⟨r, hrN⟩ : Fin N`
    -- at which the factor is `0`, annihilating the product.
    have hrN : r < N := lt_of_not_ge hNr
    have hi0 : (⟨r, hrN⟩ : Fin N) ∈ (Finset.univ : Finset (Fin N)) :=
      Finset.mem_univ _
    have hfac :
        (if ((⟨r, hrN⟩ : Fin N)).val < r then (1 : ℝ) else 0) = 0 := by
      simp
    have hprod :
        (∏ i : Fin N, (if (i : Fin N).val < r then (1 : ℝ) else 0)) = 0 := by
      refine Finset.prod_eq_zero hi0 ?_
      exact hfac
    rw [hprod]
    simp [hNr]

/-- **Trivial gauge yields the zero matrix.**

For the zero gauge (projection `= 0`), the range is `⊥` and its
ℚ-dimension is `0`; hence every diagonal entry `i.val < 0` is false
and the matrix is `0`. This is the rank-zero vertex of the N-Frame
variational problem (paper §28.3 p. 137). -/
theorem realProjMatrix_trivial_zero {N : ℕ} :
    realProjMatrix (PallLean.Paper93.NFrame.trivialGauge N) =
      (0 : Matrix (Fin N) (Fin N) ℝ) := by
  unfold realProjMatrix PallLean.Paper93.NFrame.trivialGauge
  -- The range of the zero map is `⊥`.
  have hrange :
      LinearMap.range
        (0 : MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ) = ⊥ :=
    LinearMap.range_zero
  -- Therefore the finrank is `0`, and every index satisfies
  -- `¬ (i.val < 0)`.
  have hfinrank :
      Module.finrank ℚ
        (LinearMap.range
          (0 : MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ)) = 0 := by
    rw [hrange]
    exact finrank_bot ℚ (MvPolynomial (Fin N) ℚ)
  -- Rewrite the diagonal: every entry is `0`, so the matrix is `0`.
  rw [hfinrank]
  show Matrix.diagonal (fun i : Fin N => if (i.val < 0) then (1 : ℝ) else 0)
        = (0 : Matrix (Fin N) (Fin N) ℝ)
  have hdiag :
      (fun i : Fin N => if (i : Fin N).val < 0 then (1 : ℝ) else 0) =
        (fun _ : Fin N => (0 : ℝ)) := by
    funext i
    have : ¬ (i : Fin N).val < 0 := Nat.not_lt_zero _
    simp [this]
  rw [hdiag]
  exact Matrix.diagonal_zero

end PallLean.Paper93.Concrete
