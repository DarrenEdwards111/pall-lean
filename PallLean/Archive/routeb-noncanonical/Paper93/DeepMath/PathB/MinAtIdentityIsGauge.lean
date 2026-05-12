import PallLean.Paper93.DeepMath.PathB.IdentityIsGaugeAnyFamily

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.NFrame

/-- Concrete instance: if the minimizer (Φ*, A*) of S_NF on a smooth compact region happens
    to have A* = identity matrix, then A* automatically satisfies IsAmplituhedronGauge for any
    family. (This is the statement we want for paper §7.1's claim, restricted to the special
    case where the minimizer's A-component is the identity.) -/
theorem A_identity_implies_gauge {n : ℕ}
    (A_star : Matrix (Fin n) (Fin n) ℝ) (𝒥 : Finset (Finset (Fin n)))
    (hA : A_star = 1) :
    IsAmplituhedronGauge A_star 𝒥 := by
  rw [hA]
  exact identity_isAmplituhedronGauge_any 𝒥

end PallLean.Paper93.DeepMath.PathB
