import PallLean.Paper93.DeepMath.CookLevin.BridgeA
import PallLean.Paper93.DeepMath.CookLevin.BridgeB
import PallLean.Paper93.DeepMath.CookLevin.Theorem207Chain
import PallLean.Paper93.DeepMath.CookLevin.PaperMain

namespace PallLean.Paper93.DeepMath.CookLevin

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.BridgeB

/-- The complete Bridge A → Bridge B → Theorem 207 chain in one place. -/
theorem cookLevin_complete_chain (α : ℝ) (κ n : ℕ) (hα : 0 < α) (hn : 2 ≤ n) :
    -- Bridge A: each pocket has rank ≥ 1
    (1 ≤ (compiledGadget α n).rank) ∧
    -- Bridge B: κ pockets ⇒ rank ≥ κ
    (κ ≤ (pocketFamily α κ n).rank) ∧
    -- Theorem 207 paper-named version
    (κ ≤ (pocketFamily α κ n).rank) :=
  ⟨bridge_A_pocket α n hα hn, bridge_B_kappa_pocket α κ n hα hn,
   paper_headline_rank α κ n hα hn⟩

end PallLean.Paper93.DeepMath.CookLevin
