import PallLean.Paper93.DeepMath.NFrame.EulerLagrange

namespace PallLean.Paper93.DeepMath.NFrame

/-- A point is jointly EL-critical iff it is critical in both Φ and A separately. -/
theorem isEulerLagrangeCritical_iff {n : ℕ} (α β lam : ℝ)
    (adj : Matrix (Fin n) (Fin n) ℝ) (chi : Fin n → ℝ)
    (phi : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    IsEulerLagrangeCritical α β lam adj chi phi A ↔
    (IsEulerLagrangeCriticalPhi α β lam adj chi A phi ∧
     IsEulerLagrangeCriticalA α β lam adj chi phi A) := by
  unfold IsEulerLagrangeCritical
  rfl

end PallLean.Paper93.DeepMath.NFrame
