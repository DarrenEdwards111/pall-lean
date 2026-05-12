import PallLean.Paper93.DeepMath.PathB.MinIsGaugeFinOne
import PallLean.Paper93.DeepMath.PathB.IdentityIsGaugeAnyFamily
import PallLean.Paper93.DeepMath.PathB.GaugeImpliesRankKappa
import PallLean.Paper93.DeepMath.PathB.PathBToExistingChain

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.NFrame
open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.BridgeB

/-- Path B, closed-form for n=1:
    1. Identity matrix is a gauge for any family (proved kernel-only).
    2. This gauge implies κ ≤ pocketFamily rank for κ-pocket compositions.
    3. Combined with the existing PaperFaithfulSeparation chain ⇒ ¬ PeqNP_Paper. -/
theorem path_B_closed_form (n : ℕ) (𝒥 : Finset (Finset (Fin n))) :
    (∃ A : Matrix (Fin n) (Fin n) ℝ, IsAmplituhedronGauge A 𝒥) ∧
    (∀ α : ℝ, ∀ κ : ℕ, 0 < α → 2 ≤ n → κ ≤ (pocketFamily α κ n).rank) ∧
    (∀ (_ : PaperFaithfulSeparation.PeqNP_Paper), False) := by
  refine ⟨⟨1, identity_isAmplituhedronGauge_any 𝒥⟩, ?_, ?_⟩
  · intros α κ hα hn
    exact PallLean.Paper93.DeepMath.CookLevin.theorem_207_rank_chain α κ n hα hn
  · exact path_B_concludes_no_PeqNP_Paper

end PallLean.Paper93.DeepMath.PathB
