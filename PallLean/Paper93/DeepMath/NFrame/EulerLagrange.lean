import PallLean.Paper93.DeepMath.NFrame.SNF
import Mathlib.Analysis.Calculus.FDeriv.Basic

namespace PallLean.Paper93.DeepMath.NFrame

/-- Definition of Euler-Lagrange critical point for S_NF:
    (Φ, A) is critical if the Fréchet derivative of `S_NF` vanishes at that point,
    treating Φ and A as the free variables with adj, chi, α, β, λ fixed. -/
noncomputable def IsEulerLagrangeCriticalPhi {n : ℕ} (α β lam : ℝ)
    (adj : Matrix (Fin n) (Fin n) ℝ) (chi : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (phi : Fin n → ℝ) : Prop :=
  fderiv ℝ (fun psi => S_NF α β lam adj psi chi A) phi = 0

/-- Definition of δA stationarity (fixing Φ): critical point in A-variable. -/
noncomputable def IsEulerLagrangeCriticalA {n : ℕ} (α β lam : ℝ)
    (adj : Matrix (Fin n) (Fin n) ℝ) (chi : Fin n → ℝ)
    (phi : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  fderiv ℝ (fun B => S_NF α β lam adj phi chi B) A = 0

/-- Full Euler-Lagrange system: critical in both Φ and A. -/
noncomputable def IsEulerLagrangeCritical {n : ℕ} (α β lam : ℝ)
    (adj : Matrix (Fin n) (Fin n) ℝ) (chi : Fin n → ℝ)
    (phi : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  IsEulerLagrangeCriticalPhi α β lam adj chi A phi ∧
  IsEulerLagrangeCriticalA α β lam adj chi phi A

end PallLean.Paper93.DeepMath.NFrame
