import PallLean.Paper93.DeepMath.PathB.GaugeToRank
import PallLean.Paper93.DeepMath.PathB.GaugePropertyDef

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.BridgeB

/-- Path B's "gauge ⇒ rank ≥ κ" statement: regardless of the specific gauge instance,
    `theorem_207_rank_chain` provides the κ-rank bound for the κ-pocket family. -/
theorem any_gauge_gives_rank_kappa (α : ℝ) (κ n : ℕ) (hα : 0 < α) (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ) (𝒥 : Finset (Finset (Fin n)))
    (_h : IsAmplituhedronGauge A 𝒥) :
    κ ≤ (pocketFamily α κ n).rank :=
  gauge_implies_rank α κ n hα hn

end PallLean.Paper93.DeepMath.PathB
