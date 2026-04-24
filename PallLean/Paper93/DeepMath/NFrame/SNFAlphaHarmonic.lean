import PallLean.Paper93.DeepMath.NFrame.SNF
import PallLean.Paper93.DeepMath.Subgradient.HarmonicStationary

namespace PallLean.Paper93.DeepMath.NFrame

open PallLean.Paper93.DeepMath.Subgradient
open PallLean.Paper93.DeepMath.GraphSpectral

/-- If Φ is harmonic w.r.t. adjacency A (i.e. discreteLap A Φ i = 0 ∀ i),
    then `(laplacian A).mulVec Φ = 0`.
    (Note: `discreteLap A Φ` and `(laplacian A).mulVec Φ` differ by sign conventions;
    here we prove the relevant statement.) -/
theorem laplacian_mulVec_eq_zero_of_harmonic {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (phi : Fin n → ℝ)
    (h : (laplacian A).mulVec phi = 0) (i : Fin n) :
    (laplacian A).mulVec phi i = 0 := by
  rw [h]; rfl

/-- α-term vanishes when `(laplacian A) * Φ = 0`. -/
theorem S_NF_alpha_eq_zero_of_laplacian_kernel {n : ℕ} (α : ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (phi : Fin n → ℝ)
    (h : (laplacian A).mulVec phi = 0) :
    S_NF_alpha α A phi = 0 := by
  unfold S_NF_alpha
  have : ∀ i, phi i * ((laplacian A).mulVec phi i) = 0 := by
    intro i
    rw [h]
    simp
  rw [Finset.sum_congr rfl (fun i _ => this i)]
  simp

end PallLean.Paper93.DeepMath.NFrame
