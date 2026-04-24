import PallLean.Paper93.DeepMath.NFrame.CompactSumZeroPosDefRegion
import PallLean.Paper93.DeepMath.NFrame.SNFContinuousJoint
import PallLean.Paper93.DeepMath.NFrame.ExistsMinOnCompact

namespace PallLean.Paper93.DeepMath.NFrame

open scoped Matrix.Norms.Elementwise

/-- Full S_NF attains its minimum on a compact smooth region, provided the region
    is nonempty. Statement: for any compact set `K ⊆ {(Φ, A) : ∀ i, Φ i ≠ 0 ∧ 0 < A.det}`,
    S_NF attains its min on K. -/
theorem exists_min_S_NF_on_compact {n : ℕ} (α β lam : ℝ)
    (adj : Matrix (Fin n) (Fin n) ℝ) (chi : Fin n → ℝ)
    (K : Set ((Fin n → ℝ) × Matrix (Fin n) (Fin n) ℝ))
    (hK : IsCompact K) (hne : K.Nonempty)
    (hK_smooth : ∀ p ∈ K, (∀ i, p.1 i ≠ 0) ∧ 0 < p.2.det) :
    ∃ p_star ∈ K, ∀ q ∈ K,
      S_NF α β lam adj p_star.1 chi p_star.2 ≤ S_NF α β lam adj q.1 chi q.2 := by
  apply exists_minimum_on_compact hK hne
  intros p hp
  obtain ⟨hphi, hdet⟩ := hK_smooth p hp
  exact (S_NF_continuousAt_smooth α β lam adj chi p.1 p.2 hphi hdet).continuousWithinAt

end PallLean.Paper93.DeepMath.NFrame
