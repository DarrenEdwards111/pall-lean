import PallLean.Paper93.Concrete.FullLagrangianFixed

/-!
# Every unrestricted minimizer has a bounded production projection rank

This file uses the production `fullLagrangianFixed` and `ObserverGauge`
definitions without alteration. The trivial observer gauge has action `γ`.
For `α ≥ 0`, `β > 0`, and `γ ≥ 0`, any gauge with action no larger than that
trivial competitor has projection rank at most `γ / β`. Thus every global
minimizer over the existing observer-gauge type obeys this bound, independently
of the graph, number of variables, or any encoded machine/input.

At `β = γ = 1` the stronger conclusion holds: every such gauge has rank zero,
so its projection is the zero map and cannot fix any nonzero polynomial.
This strengthens the earlier existence of a zero minimizer to a statement
about every minimizer of this concrete action at those coefficients.

The result concerns the existing unrestricted gauge domain and structural
barrier `1/(1+rank)`. It does not apply automatically to a separately restricted
domain, a different analytic log-determinant action, or a chosen gauge that is
not a minimizer. No replacement invariant or hardness premise is introduced.
-/

namespace GodMoveProductionMinimizerBarrier

open PallLean.Paper93.Concrete PallLean.Paper93.NFrame

/-- The unrestricted domain always supplies this fixed-cost competitor. -/
theorem trivial_action_eq_gamma {N d : ℕ} (α β γ : ℝ)
    (G : RegularGraphFixed N d) :
    fullLagrangianFixed α β γ G (trivialObserverGauge N) = γ := by
  simp only [fullLagrangianFixed, logDetBarrier, trivialObserverGauge,
    trivialCoord, trivialGauge]
  rw [LinearMap.range_zero]
  simp

/-- Nonnegative edge and barrier terms cannot hide projection-rank cost. -/
theorem rank_term_le_gamma_of_action_le_trivial {N d : ℕ} (α β γ : ℝ)
    (G : RegularGraphFixed N d) (g : ObserverGauge N)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hcost : fullLagrangianFixed α β γ G g ≤
      fullLagrangianFixed α β γ G (trivialObserverGauge N)) :
    β * (Module.finrank ℚ (LinearMap.range g.projection) : ℝ) ≤ γ := by
  have he : 0 ≤ ∑ e ∈ G.edges,
      (g.coord.values e.1 - g.coord.values e.2) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hEdge := mul_nonneg hα he
  have hBarrier := mul_nonneg hγ (logDetBarrier_nonneg (gauge := g.toCandidateGauge))
  rw [trivial_action_eq_gamma] at hcost
  unfold fullLagrangianFixed at hcost
  linarith

theorem rank_le_gamma_div_beta_of_action_le_trivial {N d : ℕ} (α β γ : ℝ)
    (G : RegularGraphFixed N d) (g : ObserverGauge N)
    (hα : 0 ≤ α) (hβ : 0 < β) (hγ : 0 ≤ γ)
    (hcost : fullLagrangianFixed α β γ G g ≤
      fullLagrangianFixed α β γ G (trivialObserverGauge N)) :
    (Module.finrank ℚ (LinearMap.range g.projection) : ℝ) ≤ γ / β := by
  apply (le_div_iff₀ hβ).mpr
  simpa only [mul_comm] using
    rank_term_le_gamma_of_action_le_trivial α β γ G g hα hγ hcost

/-- Every global minimizer in the actual unrestricted type has this same
bound; fixed positive coefficients give a bound independent of input size. -/
theorem global_minimizer_rank_le {N d : ℕ} (α β γ : ℝ)
    (G : RegularGraphFixed N d) (g : ObserverGauge N)
    (hα : 0 ≤ α) (hβ : 0 < β) (hγ : 0 ≤ γ)
    (hmin : ∀ g' : ObserverGauge N,
      fullLagrangianFixed α β γ G g ≤ fullLagrangianFixed α β γ G g') :
    (Module.finrank ℚ (LinearMap.range g.projection) : ℝ) ≤ γ / β :=
  rank_le_gamma_div_beta_of_action_le_trivial α β γ G g hα hβ hγ
    (hmin (trivialObserverGauge N))

/-- With these allowed positive rank/barrier coefficients, every gauge no
more expensive than the trivial competitor has rank zero. -/
theorem rank_eq_zero_of_action_le_trivial {N d : ℕ} (α : ℝ)
    (G : RegularGraphFixed N d) (g : ObserverGauge N) (hα : 0 ≤ α)
    (hcost : fullLagrangianFixed α 1 1 G g ≤
      fullLagrangianFixed α 1 1 G (trivialObserverGauge N)) :
    Module.finrank ℚ (LinearMap.range g.projection) = 0 := by
  by_contra hne
  have hr : (1 : ℝ) ≤ (Module.finrank ℚ (LinearMap.range g.projection) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
  have he : 0 ≤ ∑ e ∈ G.edges,
      (g.coord.values e.1 - g.coord.values e.2) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hEdge := mul_nonneg hα he
  have hBarrier : 0 < 1 /
      (1 + (Module.finrank ℚ (LinearMap.range g.projection) : ℝ)) := by positivity
  rw [trivial_action_eq_gamma] at hcost
  unfold fullLagrangianFixed logDetBarrier at hcost
  simp only [one_mul] at hcost
  linarith

/-- The finite-range field prevents `finrank = 0` from hiding a nonzero
infinite-dimensional range. -/
theorem projection_eq_zero_of_action_le_trivial {N d : ℕ} (α : ℝ)
    (G : RegularGraphFixed N d) (g : ObserverGauge N) (hα : 0 ≤ α)
    (hcost : fullLagrangianFixed α 1 1 G g ≤
      fullLagrangianFixed α 1 1 G (trivialObserverGauge N)) :
    g.projection = 0 := by
  letI : Module.Finite ℚ (LinearMap.range g.projection) := g.rank_finite
  have hrange : LinearMap.range g.projection = ⊥ :=
    Submodule.finrank_eq_zero.mp (rank_eq_zero_of_action_le_trivial α G g hα hcost)
  apply LinearMap.ext
  intro p
  have hp := LinearMap.mem_range_self g.projection p
  rw [hrange] at hp
  exact (Submodule.mem_bot ℚ).mp hp

theorem cannot_fix_nonzero_of_action_le_trivial {N d : ℕ} (α : ℝ)
    (G : RegularGraphFixed N d) (g : ObserverGauge N) (hα : 0 ≤ α)
    (hcost : fullLagrangianFixed α 1 1 G g ≤
      fullLagrangianFixed α 1 1 G (trivialObserverGauge N))
    (p : MvPolynomial (Fin N) ℚ) (hp : p ≠ 0) : g.projection p ≠ p := by
  rw [projection_eq_zero_of_action_le_trivial α G g hα hcost]
  exact Ne.symm hp

theorem global_minimizer_projection_eq_zero {N d : ℕ} (α : ℝ)
    (G : RegularGraphFixed N d) (g : ObserverGauge N) (hα : 0 ≤ α)
    (hmin : ∀ g' : ObserverGauge N,
      fullLagrangianFixed α 1 1 G g ≤ fullLagrangianFixed α 1 1 G g') :
    g.projection = 0 :=
  projection_eq_zero_of_action_le_trivial α G g hα (hmin (trivialObserverGauge N))

theorem global_minimizer_cannot_fix_nonzero {N d : ℕ} (α : ℝ)
    (G : RegularGraphFixed N d) (g : ObserverGauge N) (hα : 0 ≤ α)
    (hmin : ∀ g' : ObserverGauge N,
      fullLagrangianFixed α 1 1 G g ≤ fullLagrangianFixed α 1 1 G g')
    (p : MvPolynomial (Fin N) ℚ) (hp : p ≠ 0) : g.projection p ≠ p :=
  cannot_fix_nonzero_of_action_le_trivial α G g hα (hmin (trivialObserverGauge N)) p hp

end GodMoveProductionMinimizerBarrier

#print axioms GodMoveProductionMinimizerBarrier.trivial_action_eq_gamma
#print axioms GodMoveProductionMinimizerBarrier.rank_term_le_gamma_of_action_le_trivial
#print axioms GodMoveProductionMinimizerBarrier.rank_le_gamma_div_beta_of_action_le_trivial
#print axioms GodMoveProductionMinimizerBarrier.global_minimizer_rank_le
#print axioms GodMoveProductionMinimizerBarrier.rank_eq_zero_of_action_le_trivial
#print axioms GodMoveProductionMinimizerBarrier.projection_eq_zero_of_action_le_trivial
#print axioms GodMoveProductionMinimizerBarrier.cannot_fix_nonzero_of_action_le_trivial
#print axioms GodMoveProductionMinimizerBarrier.global_minimizer_projection_eq_zero
#print axioms GodMoveProductionMinimizerBarrier.global_minimizer_cannot_fix_nonzero
