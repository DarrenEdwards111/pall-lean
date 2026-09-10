import GodMoveBoundaryNFrameGauge
import GodMoveProductionMinimizerBarrier

/-!
# Exact production-action minimum subject to preserving the designated rows

The unchanged production action has a concrete minimizer on the explicitly
restricted domain of gauges fixing the designated derivative rows. Its rank
and action are derived from the coefficient identity, not added as fields.
This is a new audit predicate on the existing type, not a redefinition of
production admissibility. Faithful SAT correctness has not been shown to
force a runtime-controlled gauge into this smaller domain.
-/

namespace GodMoveConstrainedBoundaryMinimum

open GodMoveMonomialMinor GodMoveDesignatedPositiveBoundary GodMoveBoundaryNFrameGauge
open PallLean.Paper93.NFrame PallLean.Paper93.Concrete
open scoped BigOperators

/-- Extra preservation conditions for this variational problem. They are
not claimed to follow from the existing production admissibility predicate. -/
def PreservesDesignatedRows {m : ℕ} (k : ℕ) (g : ObserverGauge m) : Prop :=
  ∀ S : KSubset m k, g.projection (qRow S.val) = qRow S.val

theorem boundaryGauge_preserves (m k : ℕ) :
    PreservesDesignatedRows k (boundaryGauge m k) :=
  boundaryGauge_fixes_qRow m k

/-- Every member of this domain must retain the actual independent rows. -/
theorem preserved_rank_lower {m k : ℕ} (g : ObserverGauge m)
    (hg : PreservesDesignatedRows k g) :
    Nat.choose m k ≤ Module.finrank ℚ (LinearMap.range g.projection) := by
  letI : Module.Finite ℚ (LinearMap.range g.projection) := g.rank_finite
  let rows : KSubset m k → LinearMap.range g.projection :=
    fun S => ⟨qRow S.val, ⟨qRow S.val, hg S⟩⟩
  have hli : LinearIndependent ℚ rows := by
    apply LinearIndependent.of_comp (LinearMap.range g.projection).subtype
    exact qRows_linearIndependent m k
  simpa only [kSubset_card] using hli.fintype_card_le_finrank

/-- The production rank-plus-barrier expression increases on nonnegative
real ranks. This proves the variational comparison, rather than dropping
the decreasing barrier term. -/
theorem rank_barrier_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    a + 1 / (1 + a) ≤ b + 1 / (1 + b) := by
  have hb : 0 ≤ b := ha.trans hab
  have hpa : 0 < 1 + a := by linarith
  have hpb : 0 < 1 + b := by linarith
  have heq (x : ℝ) (hx : 0 < 1 + x) :
      x + 1 / (1 + x) = (x * (1 + x) + 1) / (1 + x) := by
    field_simp
  rw [heq a hpa, heq b hpb]
  apply (div_le_div_iff₀ hpa hpb).mpr
  have hprod : 0 ≤ (b - a) * (a + b + a * b) :=
    mul_nonneg (sub_nonneg.mpr hab) (by positivity)
  nlinarith

/-- Nonnegative edge energy leaves the precise rank-plus-barrier floor. -/
theorem rank_barrier_le_action {m d : ℕ} (α : ℝ) (hα : 0 ≤ α)
    (G : RegularGraphFixed m d) (g : ObserverGauge m) :
    (Module.finrank ℚ (LinearMap.range g.projection) : ℝ) +
        1 / (1 + (Module.finrank ℚ (LinearMap.range g.projection) : ℝ)) ≤
      fullLagrangianFixed α 1 1 G g := by
  have he : 0 ≤ ∑ e ∈ G.edges, (g.coord.values e.1 - g.coord.values e.2) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have henergy := mul_nonneg hα he
  unfold fullLagrangianFixed logDetBarrier
  simp only [one_mul]
  linarith

/-- The exact lower action value for this particular preservation domain. -/
theorem preserved_action_lower {m k d : ℕ} (α : ℝ) (hα : 0 ≤ α)
    (G : RegularGraphFixed m d) (g : ObserverGauge m)
    (hg : PreservesDesignatedRows k g) :
    (Nat.choose m k : ℝ) + 1 / (1 + (Nat.choose m k : ℝ)) ≤
      fullLagrangianFixed α 1 1 G g := by
  exact (rank_barrier_mono (Nat.cast_nonneg _)
    (by exact_mod_cast preserved_rank_lower g hg)).trans
      (rank_barrier_le_action α hα G g)

/-- The explicit decoded row projector attains the minimum of the unchanged
production action, on this explicitly stated restricted domain. -/
theorem boundaryGauge_is_constrained_minimizer {m k d : ℕ}
    (α : ℝ) (hα : 0 ≤ α) (G : RegularGraphFixed m d) :
    PreservesDesignatedRows k (boundaryGauge m k) ∧
      ∀ g : ObserverGauge m, PreservesDesignatedRows k g →
        fullLagrangianFixed α 1 1 G (boundaryGauge m k) ≤
          fullLagrangianFixed α 1 1 G g := by
  refine ⟨boundaryGauge_preserves m k, ?_⟩
  intro g hg
  rw [boundaryGauge_action]
  simpa only [one_mul] using preserved_action_lower α hα G g hg

/-- Every minimizer over the row-preserving domain has exactly the binomial
rank, even though unrestricted production minimizers have rank zero. -/
theorem every_constrained_minimizer_rank {m k d : ℕ}
    (α : ℝ) (hα : 0 ≤ α) (G : RegularGraphFixed m d) (g : ObserverGauge m)
    (hg : PreservesDesignatedRows k g)
    (hmin : ∀ g' : ObserverGauge m, PreservesDesignatedRows k g' →
      fullLagrangianFixed α 1 1 G g ≤ fullLagrangianFixed α 1 1 G g') :
    Module.finrank ℚ (LinearMap.range g.projection) = Nat.choose m k := by
  apply Nat.le_antisymm _ (preserved_rank_lower g hg)
  by_contra hle
  have hrNat : Nat.choose m k + 1 ≤ Module.finrank ℚ (LinearMap.range g.projection) := by
    omega
  have hr : (Nat.choose m k : ℝ) + 1 ≤
      (Module.finrank ℚ (LinearMap.range g.projection) : ℝ) := by exact_mod_cast hrNat
  have htop := hmin (boundaryGauge m k) (boundaryGauge_preserves m k)
  rw [boundaryGauge_action] at htop
  simp only [one_mul] at htop
  have ha : 1 / (1 + (Nat.choose m k : ℝ)) ≤ 1 :=
    (div_le_one (by positivity)).mpr (by have := Nat.cast_nonneg (α := ℝ) (Nat.choose m k); linarith)
  have hp : 0 < 1 /
      (1 + (Module.finrank ℚ (LinearMap.range g.projection) : ℝ)) := by positivity
  have hlo := rank_barrier_le_action α hα G g
  linarith

/-- At logarithmic order even the minimum on this domain has superpolynomial
rank. The conclusion is about the preservation domain, not SAT runtime. -/
theorem constrained_minimum_rank_exceeds_power (m d : ℕ)
    (hm : 2 ^ (max 20 (4 * (d + 1))) ≤ m) :
    m ^ d < Module.finrank ℚ
      (LinearMap.range (boundaryGauge m (Nat.log 2 m)).projection) := by
  rw [boundaryGauge_rank]
  exact npow_lt_choose_log m d hm

end GodMoveConstrainedBoundaryMinimum

#print axioms GodMoveConstrainedBoundaryMinimum.boundaryGauge_preserves
#print axioms GodMoveConstrainedBoundaryMinimum.preserved_rank_lower
#print axioms GodMoveConstrainedBoundaryMinimum.rank_barrier_mono
#print axioms GodMoveConstrainedBoundaryMinimum.rank_barrier_le_action
#print axioms GodMoveConstrainedBoundaryMinimum.preserved_action_lower
#print axioms GodMoveConstrainedBoundaryMinimum.boundaryGauge_is_constrained_minimizer
#print axioms GodMoveConstrainedBoundaryMinimum.every_constrained_minimizer_rank
#print axioms GodMoveConstrainedBoundaryMinimum.constrained_minimum_rank_exceeds_power
