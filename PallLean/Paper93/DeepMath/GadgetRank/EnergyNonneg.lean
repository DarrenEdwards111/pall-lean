import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace PallLean.Paper93.DeepMath.GadgetRank

/-- Discrete Dirichlet energy of `phi : Fin n → ℝ` over an edge set. -/
def energy {n : ℕ} (phi : Fin n → ℝ) (edges : Finset (Fin n × Fin n)) : ℝ :=
  ∑ e ∈ edges, (phi e.1 - phi e.2)^2

theorem energy_nonneg {n : ℕ} (phi : Fin n → ℝ) (edges : Finset (Fin n × Fin n)) :
    0 ≤ energy phi edges :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem energy_zero_of_constant {n : ℕ} (c : ℝ) (edges : Finset (Fin n × Fin n)) :
    energy (fun _ => c) edges = 0 := by
  simp [energy, sub_self, zero_pow, Finset.sum_const_zero]

end PallLean.Paper93.DeepMath.GadgetRank
