import PallLean.Paper93.Concrete.FullLagrangianFixed
namespace NFrameFixedInvariantAudit
open PallLean.Paper93.Concrete PallLean.Paper93.NFrame

theorem rank_penalty_ge_one (r : ℝ) (hr : 0 ≤ r) :
    1 ≤ r + 1 / (1 + r) := by
  have hp : 0 < 1 + r := by linarith
  have hm : (1 / (1 + r)) * (1 + r) = 1 :=
    div_mul_cancel₀ 1 (ne_of_gt hp)
  have hs := sq_nonneg r
  nlinarith

theorem full_action_ge_one {N d : ℕ} (α : ℝ) (hα : 0 ≤ α)
    (G : RegularGraphFixed N d) (g : ObserverGauge N) :
    1 ≤ fullLagrangianFixed α 1 1 G g := by
  have he : 0 ≤ ∑ e ∈ G.edges,
      (g.coord.values e.1 - g.coord.values e.2)^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hm := mul_nonneg hα he
  have hr := rank_penalty_ge_one
    (Module.finrank ℚ (LinearMap.range g.toCandidateGauge.projection) : ℝ)
    (Nat.cast_nonneg _)
  unfold fullLagrangianFixed logDetBarrier
  simp only [one_mul]
  linarith

theorem zero_action_eq_one {N d : ℕ} (α : ℝ)
    (G : RegularGraphFixed N d) :
    fullLagrangianFixed α 1 1 G (trivialObserverGauge N) = 1 := by
  simp only [fullLagrangianFixed, logDetBarrier, trivialObserverGauge,
    trivialCoord, trivialGauge]
  rw [LinearMap.range_zero]
  simp

theorem zero_gauge_is_global_minimum {N d : ℕ} (α : ℝ) (hα : 0 ≤ α)
    (G : RegularGraphFixed N d) (g : ObserverGauge N) :
    fullLagrangianFixed α 1 1 G (trivialObserverGauge N) ≤
      fullLagrangianFixed α 1 1 G g := by
  rw [zero_action_eq_one]
  exact full_action_ge_one α hα G g
end NFrameFixedInvariantAudit
#print axioms NFrameFixedInvariantAudit.zero_gauge_is_global_minimum
