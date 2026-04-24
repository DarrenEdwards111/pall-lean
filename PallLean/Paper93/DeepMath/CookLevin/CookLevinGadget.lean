import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetSumZero
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetPosDef
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetNonzero
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetPSD

namespace PallLean.Paper93.DeepMath.CookLevin

open PallLean.Paper93.DeepMath.GadgetRank

/-- The Cook-Levin compiled gadget matrix at tableau vertex (abstract form):
    instantiates `compiledGadget α n` with specific coupling and size parameters
    drawn from the Turing-machine compilation. -/
def cookLevinGadget (α : ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  compiledGadget α n

/-- The Cook-Levin gadget is positive semidefinite for `α ≥ 0` assuming the
    complete-graph Laplacian is PSD. -/
theorem cookLevinGadget_posSemidef (α : ℝ) (n : ℕ) (hα : 0 ≤ α)
    (hL : (PallLean.Paper93.DeepMath.GraphSpectral.laplacian
            (PallLean.Paper93.DeepMath.LPS.completeAdj n)).PosSemidef) :
    (cookLevinGadget α n).PosSemidef := by
  unfold cookLevinGadget
  exact compiledGadget_posSemidef α n hα hL

/-- For `α > 0` and `n ≥ 2`, the Cook-Levin gadget is nonzero. -/
theorem cookLevinGadget_ne_zero (α : ℝ) (n : ℕ) (hα : 0 < α) (hn : 2 ≤ n) :
    cookLevinGadget α n ≠ 0 := by
  unfold cookLevinGadget
  exact compiledGadget_ne_zero α n hα hn

end PallLean.Paper93.DeepMath.CookLevin
