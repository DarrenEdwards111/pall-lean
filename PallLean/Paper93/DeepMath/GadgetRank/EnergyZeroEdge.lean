import PallLean.Paper93.DeepMath.GadgetRank.EnergyNonneg
import Mathlib.Tactic.Linarith

namespace PallLean.Paper93.DeepMath.GadgetRank

theorem energy_zero_imp_edge_eq {n : ℕ} (phi : Fin n → ℝ) (edges : Finset (Fin n × Fin n))
    (hE : energy phi edges = 0) (e : Fin n × Fin n) (he : e ∈ edges) :
    phi e.1 = phi e.2 := by
  -- energy = ∑ (phi e.1 - phi e.2)^2 = 0, each term ≥ 0, so each term = 0, so phi e.1 = phi e.2.
  have hterm_nonneg : ∀ e' ∈ edges, 0 ≤ (phi e'.1 - phi e'.2)^2 := fun _ _ => sq_nonneg _
  have h_each : ∀ e' ∈ edges, (phi e'.1 - phi e'.2)^2 = 0 := by
    exact (Finset.sum_eq_zero_iff_of_nonneg hterm_nonneg).mp hE
  have h_diff : (phi e.1 - phi e.2)^2 = 0 := h_each e he
  have h_zero : phi e.1 - phi e.2 = 0 := by
    exact sq_eq_zero_iff.mp h_diff
  linarith

end PallLean.Paper93.DeepMath.GadgetRank
