import PallLean.Paper93.DeepMath.NFrame.NFrameMainResults
import PallLean.Paper93.DeepMath.CookLevin.CookLevinMainResults
import PallLean.Paper93.DeepMath.CookLevin.Theorem207Chain
import PallLean.Paper93.DeepMath.CookLevin.PaperMain

namespace PallLean.Paper93.DeepMath

open NFrame CookLevin PallLean.Paper93.DeepMath.GadgetRank
  PallLean.Paper93.DeepMath.BridgeB

/-- THE MASTER PAPER §28.3 / §40 STATEMENT:
    For any α > 0, κ pockets, and tableau size n ≥ 2, the κ-pocket
    Cook-Levin compiled gadget has rank ≥ κ. The N-Frame Lagrangian
    underlying this rank bound (via §28.3 Bridges A and B) is a well-defined
    real-valued variational functional with the standard three-term decomposition. -/
theorem paper93_master_statement (α : ℝ) (κ n : ℕ) (hα : 0 < α) (hn : 2 ≤ n) :
    (κ ≤ (pocketFamily α κ n).rank) ∧
    (∀ adj : Matrix (Fin n) (Fin n) ℝ, ∀ phi chi : Fin n → ℝ,
     ∀ A : Matrix (Fin n) (Fin n) ℝ, ∀ β lam : ℝ,
     S_NF α β lam adj phi chi A
       = S_NF_alpha α adj phi + S_NF_beta β chi phi + S_NF_lambda lam A) := by
  refine ⟨paper_headline_rank α κ n hα hn, ?_⟩
  intros adj phi chi A β lam
  exact S_NF_decompose α β lam adj phi chi A

end PallLean.Paper93.DeepMath
