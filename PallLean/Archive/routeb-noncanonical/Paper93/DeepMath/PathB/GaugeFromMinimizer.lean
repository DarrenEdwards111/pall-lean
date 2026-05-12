import PallLean.Paper93.DeepMath.PathB.MinimizerToGauge
import PallLean.Paper93.DeepMath.NFrame.SNFMinimizerFull

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.NFrame

/-- The "gauge from minimizer" hypothesis: assuming a minimizer (Φ*, A*) of S_NF on a
    suitable compact region exists, we can extract it. (We have this on compact regions
    via `exists_min_S_NF_on_compact`.) -/
theorem gauge_from_minimizer_on_compact {n : ℕ} (α β lam : ℝ)
    (adj : Matrix (Fin n) (Fin n) ℝ) (chi : Fin n → ℝ)
    (K : Set ((Fin n → ℝ) × Matrix (Fin n) (Fin n) ℝ))
    (hK : IsCompact K) (hne : K.Nonempty)
    (hK_smooth : ∀ p ∈ K, (∀ i, p.1 i ≠ 0) ∧ 0 < p.2.det) :
    ∃ p_star ∈ K, ∀ q ∈ K,
      S_NF α β lam adj p_star.1 chi p_star.2 ≤ S_NF α β lam adj q.1 chi q.2 :=
  exists_min_S_NF_on_compact α β lam adj chi K hK hne hK_smooth

end PallLean.Paper93.DeepMath.PathB
