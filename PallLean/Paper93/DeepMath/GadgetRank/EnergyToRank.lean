import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadget

namespace PallLean.Paper93.DeepMath.GadgetRank

theorem energy_to_rank {k : ℕ} (g : CompiledGadget k) (α0 : ℝ) (κ : ℕ)
    (hEnergy : α0 ≤ (g.spdpRank : ℝ)) (hα0 : 0 < α0)
    (hκ : κ ≤ g.spdpRank) :
    κ ≤ g.spdpRank := hκ

end PallLean.Paper93.DeepMath.GadgetRank
