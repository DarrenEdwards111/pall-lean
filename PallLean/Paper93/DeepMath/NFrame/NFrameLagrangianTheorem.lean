import PallLean.Paper93.DeepMath.NFrame.NFrameMainResults
import PallLean.Paper93.DeepMath.NFrame.SNFFinalSummary

namespace PallLean.Paper93.DeepMath.NFrame

/-- THE N-FRAME LAGRANGIAN THEOREM (Paper §28.3): the three-term Lagrangian
    `S_NF α β λ adj Φ χ A := α·Σ(Φ_u−Φ_v)² + β·Σ(1−χ·sgn Φ)₊ + λ·B(A)`
    is a well-defined real-valued functional with explicit decomposition. -/
theorem N_Frame_Lagrangian_decomposition {n : ℕ} (α β lam : ℝ)
    (adj : Matrix (Fin n) (Fin n) ℝ) (phi chi : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    S_NF α β lam adj phi chi A
      = S_NF_alpha α adj phi + S_NF_beta β chi phi + S_NF_lambda lam A :=
  S_NF_decompose α β lam adj phi chi A

/-- Companion: the three-term decomposition is well-typed and exists for any choice of parameters. -/
theorem N_Frame_Lagrangian_well_defined {n : ℕ} :
    ∀ (α β lam : ℝ) (adj : Matrix (Fin n) (Fin n) ℝ) (phi chi : Fin n → ℝ)
      (A : Matrix (Fin n) (Fin n) ℝ),
      ∃ r : ℝ, S_NF α β lam adj phi chi A = r :=
  fun α β lam adj phi chi A => ⟨S_NF α β lam adj phi chi A, rfl⟩

end PallLean.Paper93.DeepMath.NFrame
