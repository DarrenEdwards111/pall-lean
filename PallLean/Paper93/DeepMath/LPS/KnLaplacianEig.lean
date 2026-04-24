import PallLean.Paper93.DeepMath.LPS.CompleteGraphSecondEig
import PallLean.Paper93.DeepMath.GraphSpectral.LaplacianDef

namespace PallLean.Paper93.DeepMath.LPS

open PallLean.Paper93.DeepMath.GraphSpectral
open Matrix

/-- Row sum of the `K_n` adjacency matrix at vertex `i` equals `n - 1`:
the row `i` has a zero on the diagonal and `1` elsewhere. -/
theorem completeAdj_rowSum (n : ℕ) (i : Fin n) :
    ∑ j, completeAdj n i j = (n : ℝ) - 1 := by
  -- Rewrite each summand `if i = j then 0 else 1` as `1 - (if i = j then 1 else 0)`.
  have hpt : ∀ j : Fin n,
      (if i = j then (0 : ℝ) else 1) = 1 - (if i = j then (1 : ℝ) else 0) := by
    intro j
    by_cases hij : i = j
    · simp [hij]
    · simp [hij]
  have hstep : (∑ j, completeAdj n i j)
        = (∑ _j : Fin n, (1 : ℝ)) - ∑ j, (if i = j then (1 : ℝ) else 0) := by
    simp only [completeAdj]
    calc  (∑ j, (if i = j then (0 : ℝ) else 1))
        = ∑ j, (1 - (if i = j then (1 : ℝ) else 0)) := by
              refine Finset.sum_congr rfl ?_
              intro j _
              exact hpt j
      _ = (∑ _j : Fin n, (1 : ℝ)) - ∑ j, (if i = j then (1 : ℝ) else 0) := by
              rw [Finset.sum_sub_distrib]
  have hones : (∑ _j : Fin n, (1 : ℝ)) = (n : ℝ) := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have hdelta : (∑ j, (if i = j then (1 : ℝ) else 0)) = 1 := by
    simp [Finset.sum_ite_eq, Finset.mem_univ]
  rw [hstep, hones, hdelta]

/-- The row-sum of the complete-graph adjacency, packaged as `rowSum`. -/
theorem completeAdj_rowSum_eq (n : ℕ) :
    rowSum (completeAdj n) = fun _ => ((n : ℝ) - 1) := by
  funext i
  exact completeAdj_rowSum n i

/-- **K_n Laplacian eigenvalue on the sum-zero subspace is `n`.**

For the complete-graph Laplacian `L := laplacian (completeAdj n)`, any
vector `v : Fin n → ℝ` with `∑ i, v i = 0` satisfies
`L.mulVec v = (n : ℝ) • v`, i.e. it is an eigenvector of `L` with
eigenvalue `n`. -/
theorem completeAdj_laplacian_sumZero_eigen (n : ℕ) (v : Fin n → ℝ)
    (hv : ∑ i, v i = 0) :
    (laplacian (completeAdj n)).mulVec v = (n : ℝ) • v := by
  funext i
  -- Unfold the Laplacian and expand `(diagonal (rowSum A) - A) *ᵥ v`.
  unfold laplacian
  rw [Matrix.sub_mulVec]
  -- Now the goal involves `(diagonal (rowSum (completeAdj n)) *ᵥ v) i`
  -- and `(completeAdj n *ᵥ v) i`.
  show (Matrix.diagonal (rowSum (completeAdj n)) *ᵥ v) i
         - (completeAdj n *ᵥ v) i = ((n : ℝ) • v) i
  rw [Matrix.mulVec_diagonal, completeAdj_rowSum_eq,
      completeAdj_sumZero_eigen n v hv i]
  -- Goal: ((n : ℝ) - 1) * v i - (- v i) = ((n : ℝ) • v) i
  show ((n : ℝ) - 1) * v i - (- v i) = ((n : ℝ) • v) i
  simp [Pi.smul_apply, smul_eq_mul]
  ring

end PallLean.Paper93.DeepMath.LPS
