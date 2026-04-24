import PallLean.Paper93.DeepMath.NFrame.SNFAlphaContinuous
import PallLean.Paper93.DeepMath.NFrame.SublevelClosed

namespace PallLean.Paper93.DeepMath.NFrame

/-- Sublevel set `{Φ | S_NF_alpha α A Φ ≤ c}` is closed. -/
theorem isClosed_sublevel_S_NF_alpha {n : ℕ} (α : ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) :
    IsClosed {phi : Fin n → ℝ | S_NF_alpha α A phi ≤ c} :=
  isClosed_sublevel _ (S_NF_alpha_continuous_in_phi α A) c

end PallLean.Paper93.DeepMath.NFrame
