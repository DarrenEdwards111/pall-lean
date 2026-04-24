import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Pi

namespace PallLean.Paper93.DeepMath.Subgradient

open Finset

/-- Discrete graph Laplacian acting on vertex values: `(Lap A φ)(i) = ∑ j, A i j · (φ i − φ j)`. -/
def discreteLap {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (phi : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j, A i j * (phi i - phi j)

/-- Linearity in `phi`: `Lap A (phi + psi) = Lap A phi + Lap A psi`. -/
theorem discreteLap_add {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (phi psi : Fin n → ℝ) (i : Fin n) :
    discreteLap A (phi + psi) i = discreteLap A phi i + discreteLap A psi i := by
  simp only [discreteLap, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intros j _
  ring

/-- Scalar homogeneity: `Lap A (c • phi) = c • (Lap A phi)`. -/
theorem discreteLap_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (phi : Fin n → ℝ) (i : Fin n) :
    discreteLap A (c • phi) i = c * discreteLap A phi i := by
  simp only [discreteLap, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intros j _
  ring

end PallLean.Paper93.DeepMath.Subgradient
