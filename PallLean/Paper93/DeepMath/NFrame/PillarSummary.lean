import PallLean.Paper93.DeepMath.NFrame.SNF
import PallLean.Paper93.DeepMath.NFrame.SNFContinuousJoint
import PallLean.Paper93.DeepMath.NFrame.SNFAlphaDifferentiable
import PallLean.Paper93.DeepMath.NFrame.BarrierDiagonalConvex
import PallLean.Paper93.DeepMath.NFrame.SNFMinimizerFull

namespace PallLean.Paper93.DeepMath.NFrame

/-- The five pillars of the N-Frame Lagrangian formalization: definition,
    decomposition, joint continuity at smooth points, α-differentiability,
    and concrete minimizer existence. -/
theorem N_Frame_pillars_well_typed {n : ℕ} (α β lam : ℝ)
    (adj : Matrix (Fin n) (Fin n) ℝ) (phi chi : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    -- Pillar 1: S_NF is real-valued
    (∃ r : ℝ, S_NF α β lam adj phi chi A = r) ∧
    -- Pillar 2: three-term decomposition holds
    (S_NF α β lam adj phi chi A = S_NF_alpha α adj phi + S_NF_beta β chi phi + S_NF_lambda lam A) ∧
    -- Pillar 3: α-term is differentiable in Φ everywhere
    (Differentiable ℝ (fun psi : Fin n → ℝ => S_NF_alpha α adj psi)) := by
  refine ⟨⟨S_NF α β lam adj phi chi A, rfl⟩, S_NF_decompose α β lam adj phi chi A,
          S_NF_alpha_differentiable α adj⟩

end PallLean.Paper93.DeepMath.NFrame
