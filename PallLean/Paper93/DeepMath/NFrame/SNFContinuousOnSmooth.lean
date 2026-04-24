import PallLean.Paper93.DeepMath.NFrame.SNFContinuousJoint

namespace PallLean.Paper93.DeepMath.NFrame

/-- S_NF is continuous on the smooth region `{(Φ, A) | ∀ i, Φ i ≠ 0 ∧ 0 < A.det}`. -/
theorem S_NF_continuousOn_smooth {n : ℕ} (α β lam : ℝ)
    (adj : Matrix (Fin n) (Fin n) ℝ) (chi : Fin n → ℝ) :
    ContinuousOn (fun p : (Fin n → ℝ) × Matrix (Fin n) (Fin n) ℝ =>
                    S_NF α β lam adj p.1 chi p.2)
                 {p | (∀ i, p.1 i ≠ 0) ∧ 0 < p.2.det} := by
  intros p hp
  obtain ⟨hphi, hA⟩ := hp
  exact (S_NF_continuousAt_smooth α β lam adj chi p.1 p.2 hphi hA).continuousWithinAt

end PallLean.Paper93.DeepMath.NFrame
