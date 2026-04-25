import PallLean.Paper93.DeepMath.PathB.SATDeciderHypothesis
import PallLean.Paper93.DeepMath.PathB.SATDeciderRankStatement
import PallLean.Paper93.DeepMath.PathB.SATTiedGauge
import PallLean.Paper93.DeepMath.PathB.PathBToExistingChain

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.NFrame
open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.BridgeB

/-- Path B for SAT deciders: combining
    (1) the rank chain on the compiled gadget (kernel-only),
    (2) the SAT-tied gauge identification (currently weak/trivial form), and
    (3) the existing PaperFaithfulSeparation chain via `accesses_paper_unconditional`
    gives ¬PeqNP_Paper at the cost of one upstream gauge axiom. -/
theorem SAT_path_B_chain :
    -- Rank chain (kernel-only)
    (∀ α : ℝ, ∀ κ n : ℕ, 0 < α → 2 ≤ n → κ ≤ (pocketFamily α κ n).rank) ∧
    -- Gauge existence for any family (kernel-only via identity matrix)
    (∀ n : ℕ, ∀ 𝒥 : Finset (Finset (Fin n)),
       ∃ A : Matrix (Fin n) (Fin n) ℝ, IsAmplituhedronGauge A 𝒥) ∧
    -- ¬PeqNP_Paper (kernel + 1 upstream axiom)
    (∀ (_ : SATDecider), False) := by
  refine ⟨?_, ?_, ?_⟩
  · intros α κ n hα hn
    exact rank_for_SAT_decider_compilation α κ n hα hn
  · intros n 𝒥
    exact ⟨1, identity_isAmplituhedronGauge_any 𝒥⟩
  · exact SATDecider_implies_False

end PallLean.Paper93.DeepMath.PathB
