import PallLean.Paper93.DeepMath.PathB.GaugePropertyDef
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetPSD
import PallLean.Paper93.DeepMath.NFrame.AdjugateOne

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.NFrame
open PallLean.Paper93.DeepMath.GadgetRank

/-- The compiled gadget `compiledGadget α n` is PosSemidef when α ≥ 0 (assuming the underlying
    Laplacian is PSD). For PosDef on full PosDef cone — additional positivity needed. -/
theorem compiledGadget_posSemidef_wrapper (α : ℝ) (n : ℕ) (hα : 0 ≤ α)
    (hL : (PallLean.Paper93.DeepMath.GraphSpectral.laplacian
           (PallLean.Paper93.DeepMath.LPS.completeAdj n)).PosSemidef) :
    (compiledGadget α n).PosSemidef :=
  compiledGadget_posSemidef α n hα hL

/-- For empty family, compiledGadget α n trivially "satisfies the principal-minor condition".
    Combined with PSD ⇒ this is a "weak gauge" — but real gauge needs PosDef + unit minors. -/
theorem compiledGadget_weakly_gauge_at_empty (α : ℝ) (n : ℕ) (hα : 0 ≤ α)
    (hL : (PallLean.Paper93.DeepMath.GraphSpectral.laplacian
           (PallLean.Paper93.DeepMath.LPS.completeAdj n)).PosSemidef) :
    ∀ J ∈ (∅ : Finset (Finset (Fin n))),
      ∀ (e : Fin J.card ≃ {i // i ∈ J}),
      ((compiledGadget α n).submatrix (fun i => (e i).1) (fun i => (e i).1)).det = 1 := by
  intros J hJ
  exact absurd hJ (Finset.notMem_empty J)

end PallLean.Paper93.DeepMath.PathB
