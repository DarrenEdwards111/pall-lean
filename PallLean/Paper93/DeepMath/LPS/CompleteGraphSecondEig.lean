import PallLean.Paper93.DeepMath.LPS.CompleteGraphAdj
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace PallLean.Paper93.DeepMath.LPS

open Matrix

/-- On the sum-zero subspace `∑ i, v i = 0`, the complete-graph adjacency
matrix acts as `-1`: `(K v) i = -v i`. -/
theorem completeAdj_sumZero_eigen (n : ℕ) (v : Fin n → ℝ)
    (hv : ∑ i, v i = 0) (i : Fin n) :
    (completeAdj n).mulVec v i = -v i := by
  -- (Av) i = ∑ j, (if i = j then 0 else 1) * v j
  --       = (∑ j, v j) - v i
  --       = 0 - v i = -v i
  simp only [completeAdj, Matrix.mulVec, dotProduct]
  have h1 : (∑ j, (if i = j then (0:ℝ) else 1) * v j) = (∑ j, v j) - v i := by
    have hpt : ∀ j, (if i = j then (0:ℝ) else 1) * v j
                      = v j - (if i = j then v j else 0) := by
      intro j
      by_cases hij : i = j
      · simp [hij]
      · simp [hij]
    calc  (∑ j, (if i = j then (0:ℝ) else 1) * v j)
        = ∑ j, (v j - (if i = j then v j else 0)) := by
            refine Finset.sum_congr rfl ?_
            intro j _
            exact hpt j
      _ = (∑ j, v j) - ∑ j, (if i = j then v j else 0) := by
            rw [Finset.sum_sub_distrib]
      _ = (∑ j, v j) - v i := by
            have : (∑ j, (if i = j then v j else 0)) = v i := by
              simp [Finset.sum_ite_eq, Finset.mem_univ]
            rw [this]
  rw [h1, hv]
  ring

end PallLean.Paper93.DeepMath.LPS
