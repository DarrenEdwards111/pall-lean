import PallLean.Paper93.DeepMath.NFrame.ParityPenaltyAtNoZero

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.NFrame

/-- At any Φ with no zero entries, the β-term `parityPenalty` is locally constant.
    Hence, at any minimizer with no zero entries, all coordinate partials of β vanish. -/
theorem beta_locally_constant_at_no_zero {n : ℕ} (chi : Fin n → ℝ)
    (phi : Fin n → ℝ) (h : ∀ i, phi i ≠ 0) :
    ∀ k : Fin n, HasDerivAt (fun t => parityPenalty chi (Function.update phi k t)) 0 (phi k) :=
  fun k => parityPenalty_partial_zero_of_ne_zero chi phi k (h k)

end PallLean.Paper93.DeepMath.PathB
