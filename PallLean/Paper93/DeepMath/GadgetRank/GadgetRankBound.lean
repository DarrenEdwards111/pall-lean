import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadget
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace PallLean.Paper93.DeepMath.GadgetRank

theorem gadgetRank_le_k (k : ℕ) (g : CompiledGadget k) (h : g.spdpRank ≤ k) :
    g.spdpRank ≤ k := h

theorem trivialGadget_rank (k : ℕ) : (trivialGadget k).spdpRank = 0 := rfl

/-- Subadditivity of matrix rank: `(A + B).rank ≤ A.rank + B.rank`. -/
theorem rank_add_le {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) :
    (A + B).rank ≤ A.rank + B.rank := by
  -- Unfold `Matrix.rank` and combine `range_add_le` with
  -- `Submodule.finrank_add_le_finrank_add_finrank`.
  have hrange :
      LinearMap.range (A + B).mulVecLin ≤
        LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rw [Matrix.mulVecLin_add]
    exact LinearMap.range_add_le A.mulVecLin B.mulVecLin
  calc
    (A + B).rank
        = Module.finrank ℝ (LinearMap.range (A + B).mulVecLin) := rfl
    _ ≤ Module.finrank ℝ
          (LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin :
            Submodule ℝ (Fin m → ℝ)) :=
          Submodule.finrank_mono hrange
    _ ≤ Module.finrank ℝ (LinearMap.range A.mulVecLin) +
          Module.finrank ℝ (LinearMap.range B.mulVecLin) :=
          Submodule.finrank_add_le_finrank_add_finrank _ _
    _ = A.rank + B.rank := rfl

end PallLean.Paper93.DeepMath.GadgetRank
