import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators

namespace PallLean.Paper93.DeepMath.Subgradient

open scoped BigOperators

/-- Dirichlet energy as a sum over all ordered vertex pairs weighted by adjacency. -/
noncomputable def dirichletEnergy {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (phi : Fin n → ℝ) : ℝ :=
  (∑ i, ∑ j, A i j * (phi i - phi j)^2) / 2

/-- Symbolic "gradient component" at vertex `k`, defined as
    `2 * ∑ j, A k j * (phi k - phi j)` (i.e., twice the discrete Laplacian at `k`). -/
noncomputable def gradComp {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (phi : Fin n → ℝ) (k : Fin n) : ℝ :=
  2 * ∑ j, A k j * (phi k - phi j)

/-- For the all-constant function, every gradient component vanishes. -/
theorem gradComp_const {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (k : Fin n) :
    gradComp A (fun _ => c) k = 0 := by
  simp [gradComp, sub_self, mul_zero, Finset.sum_const_zero]

/-- The Dirichlet energy of the all-constant function is 0. -/
theorem dirichletEnergy_const {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) :
    dirichletEnergy A (fun _ => c) = 0 := by
  simp [dirichletEnergy, sub_self, zero_pow, mul_zero, Finset.sum_const_zero]

end PallLean.Paper93.DeepMath.Subgradient
