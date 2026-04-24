import PallLean.Paper93.DeepMath.NFrame.SNFContinuousOnSmooth
import PallLean.Paper93.DeepMath.NFrame.DetPosOnPosDefSubset

namespace PallLean.Paper93.DeepMath.NFrame

/-- S_NF restricted to (Φ with no zero entries, PosDef A) is continuous at every point. -/
theorem S_NF_continuousOn_sumZero_no_zero_posDef {n : ℕ} (α β lam : ℝ)
    (adj : Matrix (Fin n) (Fin n) ℝ) (chi : Fin n → ℝ) :
    ContinuousOn (fun p : (Fin n → ℝ) × Matrix (Fin n) (Fin n) ℝ =>
                    S_NF α β lam adj p.1 chi p.2)
                 {p | (∀ i, p.1 i ≠ 0) ∧ p.2.PosDef} := by
  apply (S_NF_continuousOn_smooth α β lam adj chi).mono
  intros p hp
  exact ⟨hp.1, hp.2.det_pos⟩

end PallLean.Paper93.DeepMath.NFrame
