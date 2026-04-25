import PallLean.Paper93.DeepMath.NFrame.SNF
import PallLean.Paper93.DeepMath.CookLevin.Theorem207Chain
import PallLean.Paper93.DeepMath.NFrame.SNFContinuousJoint

namespace PallLean.Paper93.DeepMath

open NFrame CookLevin GadgetRank BridgeB

/-- THE UNIFIED PAPER §28.3 / §40 MASTER THEOREM:
    The N-Frame Lagrangian S_NF is a well-defined real-valued functional with
    three-term decomposition; AND the Cook-Levin compiled gadget rank chain
    is a κ-rank lower bound for every choice of α > 0, n ≥ 2. -/
theorem unified_master_theorem (α β lam : ℝ) (κ n : ℕ) (hα_pos : 0 < α) (hn : 2 ≤ n)
    (adj : Matrix (Fin n) (Fin n) ℝ) (phi chi : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    -- N-Frame Lagrangian decomposition
    (S_NF α β lam adj phi chi A
       = S_NF_alpha α adj phi + S_NF_beta β chi phi + S_NF_lambda lam A) ∧
    -- Cook-Levin Theorem 207 rank chain
    (κ ≤ (pocketFamily α κ n).rank) :=
  ⟨S_NF_decompose α β lam adj phi chi A, theorem_207_rank_chain α κ n hα_pos hn⟩

end PallLean.Paper93.DeepMath
