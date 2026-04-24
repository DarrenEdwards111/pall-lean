import PallLean.Paper93.DeepMath.NFrame.SNF

namespace PallLean.Paper93.DeepMath.NFrame

/-- `S_NF_alpha α adj phi` doesn't depend on `A` — so as a function of `A`, it's constant. -/
theorem S_NF_alpha_const_in_A {n : ℕ} (α : ℝ)
    (adj : Matrix (Fin n) (Fin n) ℝ) (phi : Fin n → ℝ) :
    ∀ A B : Matrix (Fin n) (Fin n) ℝ,
      (fun A' : Matrix (Fin n) (Fin n) ℝ => S_NF_alpha α adj phi) A
        = (fun A' : Matrix (Fin n) (Fin n) ℝ => S_NF_alpha α adj phi) B := by
  intro _ _
  rfl

/-- β-term doesn't depend on A either. -/
theorem S_NF_beta_const_in_A {n : ℕ} (β : ℝ) (chi phi : Fin n → ℝ) :
    ∀ A B : Matrix (Fin n) (Fin n) ℝ,
      (fun A' : Matrix (Fin n) (Fin n) ℝ => S_NF_beta β chi phi) A
        = (fun A' : Matrix (Fin n) (Fin n) ℝ => S_NF_beta β chi phi) B := by
  intro _ _
  rfl

/-- Continuous as a function of A (trivially, since constant in A). -/
theorem S_NF_alpha_continuous_in_A {n : ℕ} (α : ℝ)
    (adj : Matrix (Fin n) (Fin n) ℝ) (phi : Fin n → ℝ) :
    Continuous (fun _ : Matrix (Fin n) (Fin n) ℝ => S_NF_alpha α adj phi) :=
  continuous_const

end PallLean.Paper93.DeepMath.NFrame
