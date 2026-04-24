import PallLean.Paper93.DeepMath.Subgradient.DiscreteLaplacian

namespace PallLean.Paper93.DeepMath.Subgradient

/-- A function `phi : Fin n → ℝ` is harmonic w.r.t. adjacency `A` if `Lap A phi i = 0` for all i. -/
def IsHarmonic {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (phi : Fin n → ℝ) : Prop :=
  ∀ i, discreteLap A phi i = 0

/-- Constants are harmonic: `Lap A (λ _. c) = 0`. -/
theorem const_isHarmonic {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) :
    IsHarmonic A (fun _ => c) := by
  intro i
  simp [discreteLap, sub_self, mul_zero, Finset.sum_const_zero]

/-- Zero is harmonic. -/
theorem zero_isHarmonic {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    IsHarmonic A (fun _ => (0:ℝ)) :=
  const_isHarmonic A 0

/-- Sum of harmonic functions is harmonic. -/
theorem IsHarmonic.add {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {phi psi : Fin n → ℝ}
    (hφ : IsHarmonic A phi) (hψ : IsHarmonic A psi) : IsHarmonic A (phi + psi) := by
  intro i
  rw [discreteLap_add]
  rw [hφ i, hψ i]
  ring

end PallLean.Paper93.DeepMath.Subgradient
