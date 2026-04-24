import PallLean.Paper93.DeepMath.NFrame.EulerLagrange
import PallLean.Paper93.DeepMath.NFrame.SNFAlphaHasFDeriv

namespace PallLean.Paper93.DeepMath.NFrame

/-- At a joint critical point of S_NF, BOTH the Φ-Fréchet derivative AND the A-Fréchet derivative
    vanish. This is just repackaging the EL critical-point definitions as a conjunction. -/
theorem euler_lagrange_joint_eq {n : ℕ} (α β lam : ℝ)
    (adj : Matrix (Fin n) (Fin n) ℝ) (chi : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (phi : Fin n → ℝ)
    (hphi : IsEulerLagrangeCriticalPhi α β lam adj chi A phi)
    (hA : IsEulerLagrangeCriticalA α β lam adj chi phi A) :
    IsEulerLagrangeCritical α β lam adj chi phi A :=
  ⟨hphi, hA⟩

end PallLean.Paper93.DeepMath.NFrame
