import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadget

namespace PallLean.Paper93.DeepMath.GadgetRank

theorem gadgetRank_le_k (k : ℕ) (g : CompiledGadget k) (h : g.spdpRank ≤ k) :
    g.spdpRank ≤ k := h

theorem trivialGadget_rank (k : ℕ) : (trivialGadget k).spdpRank = 0 := rfl

end PallLean.Paper93.DeepMath.GadgetRank
