import PallLean.Paper93.DeepMath.NFrame.SNFMinimizerFull
import PallLean.Paper93.DeepMath.NFrame.SNF

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.NFrame

/-- Hypothesis-form: a "gauge" is a triple (Φ*, A*) satisfying paper §28.3 properties.
    The S_NF minimizer (when it exists) IS the gauge. -/
def IsGauge {n : ℕ} (α β lam : ℝ) (adj : Matrix (Fin n) (Fin n) ℝ) (chi : Fin n → ℝ)
    (phi_star : Fin n → ℝ) (A_star : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ phi : Fin n → ℝ, ∀ A : Matrix (Fin n) (Fin n) ℝ,
    S_NF α β lam adj phi_star chi A_star ≤ S_NF α β lam adj phi chi A

/-- Trivially: any minimizer satisfies the IsGauge property by definition. -/
theorem minimizer_is_gauge {n : ℕ} (α β lam : ℝ)
    (adj : Matrix (Fin n) (Fin n) ℝ) (chi : Fin n → ℝ)
    (phi_star : Fin n → ℝ) (A_star : Matrix (Fin n) (Fin n) ℝ)
    (h : ∀ phi A, S_NF α β lam adj phi_star chi A_star ≤ S_NF α β lam adj phi chi A) :
    IsGauge α β lam adj chi phi_star A_star := h

end PallLean.Paper93.DeepMath.PathB
