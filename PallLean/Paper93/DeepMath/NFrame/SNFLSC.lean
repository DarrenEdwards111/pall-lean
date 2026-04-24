import PallLean.Paper93.DeepMath.NFrame.SNFContinuousJoint

namespace PallLean.Paper93.DeepMath.NFrame

/-- `S_NF` is lower semi-continuous at (Φ, A) whenever Φ has no zero entries
    and A.det > 0. (Stronger: joint continuity, which implies lsc.) -/
theorem S_NF_lsc_at_smooth {n : ℕ} (α β lam : ℝ)
    (adj : Matrix (Fin n) (Fin n) ℝ) (chi : Fin n → ℝ)
    (phi : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hphi : ∀ i, phi i ≠ 0) (hA : 0 < A.det) :
    LowerSemicontinuousAt (fun p : (Fin n → ℝ) × Matrix (Fin n) (Fin n) ℝ =>
                             S_NF α β lam adj p.1 chi p.2) (phi, A) :=
  (S_NF_continuousAt_smooth α β lam adj chi phi A hphi hA).lowerSemicontinuousAt

end PallLean.Paper93.DeepMath.NFrame
