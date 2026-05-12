import PallLean.Paper93.DeepMath.NFrame.BarrierDiagonal
import PallLean.Paper93.DeepMath.NFrame.BarrierDiagonalConvex
import PallLean.Paper93.DeepMath.NFrame.BarrierViaEigenvalues
import PallLean.Paper93.DeepMath.NFrame.PosDefEigenvalues
import PallLean.Paper93.DeepMath.NFrame.PosDefOpen
import PallLean.Paper93.DeepMath.PathB.DetPreservationOrthogonal

/-!
# Round 70: spectral reduction for non-diagonal barrier convexity

This file records the strongest kernel-only statement currently available for
the non-diagonal barrier `A ↦ -log(det A)` on the positive-definite cone.

The diagonal piece is already proved upstream as
`barrier_diagonal_convexOn_n`. For non-diagonal matrices, the exact missing
analytic input is the theorem named below as
`SpectralLogConvexityHypothesis`: along every positive-definite affine segment,
the negative sum of the logs of the Hermitian eigenvalues is convex. Equivalently,
this is the spectral-majorization/operator-convexity step needed to pass from
diagonal convexity to arbitrary positive-definite matrices.

No unproved theorem is introduced here. The final theorem proves that this
single named hypothesis is equivalent to full `ConvexOn` of the barrier on the
positive-definite cone.

Namespace: `PallLean.Paper93.DeepMath.PathB.Positroid`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.NFrame
open PallLean.Paper93.DeepMath.PathB

/-- The spectral form of the barrier, written as a separate expression so the
missing non-diagonal convexity input can be stated without mentioning
determinants. -/
noncomputable def spectralBarrier {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) : ℝ :=
  -∑ i, Real.log (hA.1.eigenvalues i)

/-- Positive definiteness supplies strictly positive Hermitian eigenvalues, so
every logarithm in `spectralBarrier` is taken on `(0, ∞)`. -/
theorem spectralBarrier_eigenvalues_pos {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    ∀ i, 0 < hA.1.eigenvalues i := by
  intro i
  exact posDef_eigenvalues_pos A hA i

/-- The upstream eigenvalue formula rewrites the determinant barrier as the
negative sum of logs of positive eigenvalues. -/
theorem barrier_eq_spectralBarrier {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    barrier A = spectralBarrier A hA := by
  unfold spectralBarrier
  exact barrier_eq_neg_sum_log_eigenvalues A hA

/-- Bundled form: PosDef gives both the spectral identity for the barrier and
strict positivity of every spectral coordinate. -/
theorem barrier_spectral_kernel {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    barrier A = spectralBarrier A hA ∧ ∀ i, 0 < hA.1.eigenvalues i :=
  ⟨barrier_eq_spectralBarrier A hA, spectralBarrier_eigenvalues_pos A hA⟩

/-- Orthogonal/unit-determinant conjugation leaves the barrier unchanged. This
is the determinant invariance `det_preserved_orthogonal` transported through
the definition `barrier A = -log(det A)`. -/
theorem barrier_orthogonal_invariant {n : ℕ}
    (U A : Matrix (Fin n) (Fin n) ℝ) (hU : U.det ^ 2 = 1) :
    barrier (U.transpose * A * U) = barrier A := by
  unfold barrier
  rw [det_preserved_orthogonal U A hU]

/-- The already-proved diagonal convexity theorem, transported from the scalar
eigenvalue vector form to diagonal matrices. -/
theorem barrier_diagonal_matrix_convexOn {n : ℕ} :
    ConvexOn ℝ
      ({d : Fin n → ℝ | ∀ i, 0 < d i})
      (fun d => barrier (Matrix.diagonal d)) := by
  exact (barrier_diagonal_convexOn_n (n := n)).congr (by
    intro d hd
    exact (barrier_diagonal_pos d hd).symm)

/-- The exact missing spectral theorem for full non-diagonal convexity.

It says that for any two positive-definite endpoints `A` and `B`, the spectral
barrier of the positive-definite convex combination is bounded above by the same
convex combination of the endpoint spectral barriers.

This is the only analytic input not currently proved in the repository. A future
proof should come from a formalized matrix-analysis result such as the
operator-convexity/concavity proof of `A ↦ -log(det A)`, or an eigenvalue
majorization theorem strong enough to lift the diagonal result
`barrier_diagonal_convexOn_n` through orthogonal/unitary spectral
decomposition. -/
def SpectralLogConvexityHypothesis (n : ℕ) : Prop :=
  ∀ (A B : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (hB : B.PosDef)
    (a b : ℝ) (_ha : 0 ≤ a) (_hb : 0 ≤ b) (_hab : a + b = 1)
    (hC : (a • A + b • B).PosDef),
      spectralBarrier (a • A + b • B) hC ≤
        a • spectralBarrier A hA + b • spectralBarrier B hB

/-- Reduction theorem: the named spectral log-convexity hypothesis implies full
convexity of the non-diagonal log-det barrier on the positive-definite cone. -/
theorem barrier_posDef_convexOn_of_spectralLogConvexity {n : ℕ}
    (hspectral : SpectralLogConvexityHypothesis n) :
    ConvexOn ℝ
      ({A : Matrix (Fin n) (Fin n) ℝ | A.PosDef})
      (fun A => barrier A) := by
  refine ⟨posDef_set_convex, ?_⟩
  intro A hA B hB a b ha hb hab
  have hC : (a • A + b • B).PosDef :=
    posDef_set_convex hA hB ha hb hab
  have hineq := hspectral A B hA hB a b ha hb hab hC
  change barrier (a • A + b • B) ≤ a • barrier A + b • barrier B
  rw [barrier_eq_spectralBarrier (a • A + b • B) hC,
      barrier_eq_spectralBarrier A hA,
      barrier_eq_spectralBarrier B hB]
  exact hineq

/-- Conversely, full barrier convexity on the positive-definite cone immediately
implies the named spectral log-convexity statement by the eigenvalue formula. -/
theorem spectralLogConvexity_of_barrier_posDef_convexOn {n : ℕ}
    (hbarrier :
      ConvexOn ℝ
        ({A : Matrix (Fin n) (Fin n) ℝ | A.PosDef})
        (fun A => barrier A)) :
    SpectralLogConvexityHypothesis n := by
  intro A B hA hB a b ha hb hab hC
  have hineq :
      (fun A : Matrix (Fin n) (Fin n) ℝ => barrier A) (a • A + b • B) ≤
        a • (fun A : Matrix (Fin n) (Fin n) ℝ => barrier A) A +
          b • (fun A : Matrix (Fin n) (Fin n) ℝ => barrier A) B :=
    hbarrier.2 hA hB ha hb hab
  change barrier (a • A + b • B) ≤ a • barrier A + b • barrier B at hineq
  rw [barrier_eq_spectralBarrier (a • A + b • B) hC,
      barrier_eq_spectralBarrier A hA,
      barrier_eq_spectralBarrier B hB] at hineq
  exact hineq

/-- Precise reduction: full non-diagonal `-log det` convexity on the PosDef cone
is equivalent to the named spectral log-convexity hypothesis above. -/
theorem barrier_posDef_convexOn_iff_spectralLogConvexity {n : ℕ} :
    ConvexOn ℝ
        ({A : Matrix (Fin n) (Fin n) ℝ | A.PosDef})
        (fun A => barrier A) ↔
      SpectralLogConvexityHypothesis n := by
  constructor
  · exact spectralLogConvexity_of_barrier_posDef_convexOn
  · exact barrier_posDef_convexOn_of_spectralLogConvexity

end PallLean.Paper93.DeepMath.PathB.Positroid
