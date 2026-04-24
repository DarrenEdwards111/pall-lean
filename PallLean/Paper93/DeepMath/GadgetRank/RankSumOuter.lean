import PallLean.Paper93.DeepMath.GadgetRank.OuterProduct
import PallLean.Paper93.DeepMath.GadgetRank.OuterRankOne
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace PallLean.Paper93.DeepMath.GadgetRank

open scoped Matrix

/-- Local rank-subadditivity for matrix addition: `(A + B).rank ≤ A.rank + B.rank`.

This is the matrix-level analogue of `LinearMap.rank_add_le`, packaged against
`Matrix.rank` (which is defined as `finrank` of the range of `mulVecLin`).
The proof goes via `Matrix.mulVecLin_add`, the submodule bound
`LinearMap.range_add_le`, and the finite-dimensional
`Submodule.finrank_add_le_finrank_add_finrank`. -/
private theorem Matrix.rank_add_le_local {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ) :
    (A + B).rank ≤ A.rank + B.rank := by
  -- Rewrite the rank of `A + B` via `mulVecLin` additivity.
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  -- The range of `A.mulVecLin + B.mulVecLin` sits inside `range A.mulVecLin ⊔ range B.mulVecLin`.
  have hle : LinearMap.range (A.mulVecLin + B.mulVecLin)
      ≤ LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin :=
    LinearMap.range_add_le A.mulVecLin B.mulVecLin
  -- Monotonicity of `finrank` on submodules (ambient space is finite-dimensional `Fin n → ℝ`).
  have hmono :
      Module.finrank ℝ
          (LinearMap.range (A.mulVecLin + B.mulVecLin))
        ≤ Module.finrank ℝ
          ((LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin : Submodule ℝ (Fin n → ℝ))) :=
    Submodule.finrank_mono hle
  -- Subadditivity of `finrank` on a sup of two finite-dimensional submodules.
  have hadd :
      Module.finrank ℝ
          ((LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin : Submodule ℝ (Fin n → ℝ)))
        ≤ Module.finrank ℝ (LinearMap.range A.mulVecLin)
          + Module.finrank ℝ (LinearMap.range B.mulVecLin) :=
    Submodule.finrank_add_le_finrank_add_finrank _ _
  exact hmono.trans hadd

/-- Sum of `k` outer products has rank `≤ k`. -/
theorem rank_finset_sum_outer_le {n : ℕ} (s : Finset ℕ) (v : ℕ → (Fin n → ℝ)) :
    (∑ i ∈ s, outer (v i)).rank ≤ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s hne ih =>
      rw [Finset.sum_insert hne, Finset.card_insert_of_notMem hne]
      calc (outer (v a) + ∑ i ∈ s, outer (v i)).rank
          ≤ (outer (v a)).rank + (∑ i ∈ s, outer (v i)).rank :=
            Matrix.rank_add_le_local _ _
        _ ≤ 1 + s.card := Nat.add_le_add (outer_rank_le_one _) ih
        _ = s.card + 1 := by ring

end PallLean.Paper93.DeepMath.GadgetRank
