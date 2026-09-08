import PallLean.Paper93.Concrete.FullLagrangianFixed
import Mathlib.Algebra.Order.Floor.Ring

/-!
Exact extraction from the repository's fullLagrangianFixed, not a kinetic
surrogate. Its beta coefficient multiplies projection rank. Taking a unit
finite difference in that coefficient, at FIXED gauge, recovers rank exactly.
This is not minimization over gauges, and not differentiation through an
optimizer. It does not construct a gauge from a machine configuration.
-/
namespace FullActionRankAudit
open PallLean.Paper93.Concrete

theorem full_action_rank_difference {N d : ℕ} (α β γ : ℝ)
    (G : RegularGraphFixed N d) (g : ObserverGauge N) :
    fullLagrangianFixed α (β + 1) γ G g - fullLagrangianFixed α β γ G g =
      (Module.finrank ℚ (LinearMap.range g.toCandidateGauge.projection) : ℝ) := by
  unfold fullLagrangianFixed
  ring

noncomputable def actionDerivedRank {N d : ℕ} (α β γ : ℝ)
    (G : RegularGraphFixed N d) (g : ObserverGauge N) : ℕ :=
  ⌊fullLagrangianFixed α (β + 1) γ G g - fullLagrangianFixed α β γ G g⌋₊

theorem actionDerivedRank_eq {N d : ℕ} (α β γ : ℝ)
    (G : RegularGraphFixed N d) (g : ObserverGauge N) :
    actionDerivedRank α β γ G g =
      Module.finrank ℚ (LinearMap.range g.toCandidateGauge.projection) := by
  unfold actionDerivedRank
  rw [full_action_rank_difference]
  simp

/-- A supplied gauge TRAJECTORY yields a time-indexed rank directly from the
full action. The theorem leaves the construction of that trajectory explicit. -/
theorem trajectory_rank_extraction {N d : ℕ} (α β γ : ℝ)
    (G : RegularGraphFixed N d) (gaugeAt : ℕ → ObserverGauge N) (t : ℕ) :
    actionDerivedRank α β γ G (gaugeAt t) =
      Module.finrank ℚ (LinearMap.range (gaugeAt t).toCandidateGauge.projection) :=
  actionDerivedRank_eq α β γ G (gaugeAt t)

end FullActionRankAudit

#print axioms FullActionRankAudit.full_action_rank_difference
#print axioms FullActionRankAudit.actionDerivedRank_eq
#print axioms FullActionRankAudit.trajectory_rank_extraction
