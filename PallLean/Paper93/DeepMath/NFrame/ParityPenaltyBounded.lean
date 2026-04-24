/-
  PallLean/Paper93/DeepMath/NFrame/ParityPenaltyBounded.lean

  Upper bound on the per-vertex parity penalty term.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * `#print axioms` on every theorem returns only kernel primitives
      (`propext`, `Classical.choice`, `Quot.sound`).
-/
import PallLean.Paper93.DeepMath.NFrame.ParityPenalty
import PallLean.Paper93.DeepMath.NFrame.RealSignFacts

namespace PallLean.Paper93.DeepMath.NFrame

/-- Helper: `|a · b| ≤ 1` when `|a| ≤ 1` and `|b| ≤ 1`. -/
theorem abs_mul_le_one {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) : |a * b| ≤ 1 := by
  rw [abs_mul]
  nlinarith [abs_nonneg a, abs_nonneg b]

/-- Each parity term is bounded above: `parityTerm chi_v phi_v ≤ 2`.
    Proof: `parityTerm = max 0 (1 - chi_v * sgn phi_v)`, and `sgn ∈ [-1, 1]`,
    `chi_v · sgn ∈ [-|chi_v|, |chi_v|]`.
    If `|chi_v| ≤ 1`, then `1 - chi_v · sgn ≤ 2` and `parityTerm ≤ 2`. -/
theorem parityTerm_le_two (chi_v phi_v : ℝ) (hchi : |chi_v| ≤ 1) :
    parityTerm chi_v phi_v ≤ 2 := by
  unfold parityTerm
  have h_sign_bound : |Real.sign phi_v| ≤ 1 := by
    rcases sign_trichotomy phi_v with h | h | h <;> rw [h] <;> norm_num
  have h_prod_abs : |chi_v * Real.sign phi_v| ≤ 1 :=
    abs_mul_le_one hchi h_sign_bound
  have h_prod_lower : -1 ≤ chi_v * Real.sign phi_v :=
    (abs_le.mp h_prod_abs).1
  have h_upper : 1 - chi_v * Real.sign phi_v ≤ 2 := by linarith
  exact max_le (by linarith) h_upper

end PallLean.Paper93.DeepMath.NFrame
