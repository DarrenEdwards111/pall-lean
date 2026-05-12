import PallLean.Paper93.DeepMath.PathB.SATDeciderHypothesis
import PallLean.Paper93.DeepMath.PathB.SATDeciderRankStatement
import PallLean.Paper93.DeepMath.PathB.IdentityIsGaugeAnyFamily

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.NFrame
open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.BridgeB

/-- Path B's final statement, fully composed:
    1. Rank chain: rank(pocketFamily α κ n) ≥ κ (kernel-only)
    2. General gauge existence: identity matrix witnesses (kernel-only)
    3. SAT decider impossibility: PeqNP_Paper → False (kernel + 1 upstream axiom)

    These three results together exhaust Path B's contribution. The SAT-decider-specific
    gauge tying remains the upstream `exists_amplituhedron_gauge_for_sat_decider` axiom. -/
theorem SAT_final_path_B_chain :
    (∀ α : ℝ, ∀ κ n : ℕ, 0 < α → 2 ≤ n → κ ≤ (pocketFamily α κ n).rank) ∧
    (∀ n : ℕ, ∀ 𝒥 : Finset (Finset (Fin n)),
       ∃ A : Matrix (Fin n) (Fin n) ℝ, IsAmplituhedronGauge A 𝒥) ∧
    (∀ (_ : SATDecider), False) :=
  ⟨fun α κ n hα hn => rank_for_SAT_decider_compilation α κ n hα hn,
   fun n 𝒥 => ⟨1, identity_isAmplituhedronGauge_any 𝒥⟩,
   SATDecider_implies_False⟩

end PallLean.Paper93.DeepMath.PathB
