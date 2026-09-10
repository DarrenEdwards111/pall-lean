import GodMoveProductionGaugeBridge
import GodMoveProductionMinimizerBarrier
import GodMoveComputedWireLowerBound

/-!
# What the actual production gauge bridge does and does not prove

The constructed gauge has exactly the computed-wire rank. More generally,
every production gauge fixing all emitted normalized wires has at least that
rank. The construction is therefore rank-minimal among those gauges. With
unit rank/barrier weights it also minimizes the unchanged action on that
explicitly restricted set, using its allowed zero coordinates.

Preserving computed wires is stated as an additional restriction; it is not
part of the existing production admissibility predicate and is not silently
added to it. Under this restriction the actual SAT dependency lower bound
transfers to production rank, but it is only linear. Unrestricted minimization
is incompatible with this preservation for SAT slices of length at least 23.
-/

namespace GodMoveProductionConnection

open GodMoveBooleanInterpolation GodMoveComputedWireRank GodMoveComputedWireLowerBound
open GodMoveProductionGaugeBridge GodMoveProductionMinimizerBarrier
open GodMoveCircuitRuntimeCost
open PallLean.Paper93.NFrame PallLean.Paper93.Concrete
open PallLean.Paper93.DeepMath.PathB
open NFrameBoundaryTransducer (CGate computes)
open ComposableMachine

/-- An explicit preservation restriction, beyond production admissibility. -/
def PreservesComputedWires {n : ℕ} (c : List (CGate n)) (g : CandidateGauge n) : Prop :=
  ∀ p ∈ normalizedWires c, g.projection p = p

theorem wireGauge_preserves {n : ℕ} (c : List (CGate n)) :
    PreservesComputedWires c (wireGauge c).toCandidateGauge := wireGauge_fixes_wire c

theorem wireSpace_le_range_of_preserves {n : ℕ} (c : List (CGate n))
    (g : CandidateGauge n) (h : PreservesComputedWires c g) :
    wireSpace c ≤ LinearMap.range g.projection := by
  apply Submodule.span_le.mpr
  intro p hp
  have hmem : p ∈ normalizedWires c := by simpa using hp
  exact ⟨p, h p hmem⟩

/-- A lower bound derived from actual wire preservation, not assumed row transport. -/
theorem wireRank_le_preserving_gauge_rank {n : ℕ} (c : List (CGate n))
    (g : CandidateGauge n) (h : PreservesComputedWires c g) :
    wireRank c ≤ Module.finrank ℚ (LinearMap.range g.projection) := by
  letI : Module.Finite ℚ (LinearMap.range g.projection) := g.rank_finite
  exact Submodule.finrank_mono (wireSpace_le_range_of_preserves c g h)

theorem wireGauge_rank_minimal {n : ℕ} (c : List (CGate n))
    (g : CandidateGauge n) (h : PreservesComputedWires c g) :
    Module.finrank ℚ (LinearMap.range (wireGauge c).projection) ≤
      Module.finrank ℚ (LinearMap.range g.projection) := by
  rw [wireGauge_rank]
  exact wireRank_le_preserving_gauge_rank c g h

theorem rank_penalty_monotone {s r : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r) :
    s + 1 / (1 + s) ≤ r + 1 / (1 + r) := by
  have hr : 0 ≤ r := hs.trans hsr
  have hds : 1 + s ≠ 0 := by positivity
  have hdr : 1 + r ≠ 0 := by positivity
  have hid : (r + 1 / (1 + r)) - (s + 1 / (1 + s)) =
      (r - s) * (r + s + r * s) / ((1 + r) * (1 + s)) := by
    field_simp
    ring
  apply sub_nonneg.mp
  rw [hid]
  exact div_nonneg (mul_nonneg (sub_nonneg.mpr hsr) (by positivity)) (by positivity)

/-- The constructed gauge minimizes the actual action only on this explicitly
restricted wire-preserving set. This is not unrestricted production minimality. -/
theorem wireGauge_action_minimal_among_preserving {n d : ℕ}
    (c : List (CGate n)) (G : RegularGraphFixed n d) (α : ℝ) (hα : 0 ≤ α)
    (g : ObserverGauge n) (h : PreservesComputedWires c g.toCandidateGauge) :
    fullLagrangianFixed α 1 1 G (wireGauge c) ≤ fullLagrangianFixed α 1 1 G g := by
  have hr : (wireRank c : ℝ) ≤ Module.finrank ℚ (LinearMap.range g.projection) := by
    exact_mod_cast wireRank_le_preserving_gauge_rank c g.toCandidateGauge h
  have hpen := rank_penalty_monotone (Nat.cast_nonneg (α := ℝ) (wireRank c)) hr
  have he : 0 ≤ ∑ e ∈ G.edges,
      (g.coord.values e.1 - g.coord.values e.2) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hEdge := mul_nonneg hα he
  rw [wireGauge_action]
  unfold fullLagrangianFixed logDetBarrier
  simp only [one_mul]
  linarith

/-- Every gauge preserving every computed wire of any exact SAT circuit
inherits the same genuine linear lower bound. -/
theorem sat_preserving_gauge_rank_lower (N : ℕ) (c : List (CGate N))
    (hcomp : computes c (SATCircuitSeparationBridge.SATFamily N))
    (g : CandidateGauge N) (h : PreservesComputedWires c g) :
    N - 22 ≤ Module.finrank ℚ (LinearMap.range g.projection) :=
  (satFamily_wireRank_lower N c hcomp).trans (wireRank_le_preserving_gauge_rank c g h)

/-- The same actual production projection rank now has both derived bounds.
The lower bound is linear, so there is no contradiction with the upper bound. -/
theorem actualSAT_gauge_rank_bounds (M : Machine) (T : ℕ → ℕ)
    (hD : Decides M SeparationTarget.SATLang T) (N : ℕ) :
    N - 22 ≤ Module.finrank ℚ (LinearMap.range
      (wireGauge (ComposablePpolyDischarge.circuitFor M N (T N))).projection) ∧
    Module.finrank ℚ (LinearMap.range
      (wireGauge (ComposablePpolyDischarge.circuitFor M N (T N))).projection) ≤
      circuitConstant M * (N + T N + 1) ^ 4 := by
  rw [wireGauge_rank]
  exact ⟨actualSAT_wireRank_lower M T hD N, unrolled_wireRank_le_clock M N (T N)⟩

/-- A SAT wire-preserving gauge cannot also be an unrestricted global
minimizer of the current production action at the allowed unit weights. -/
theorem sat_preserving_gauge_not_global_minimum {N d : ℕ} (hN : 23 ≤ N)
    (c : List (CGate N)) (hcomp : computes c (SATCircuitSeparationBridge.SATFamily N))
    (G : RegularGraphFixed N d) (α : ℝ) (hα : 0 ≤ α)
    (g : ObserverGauge N) (h : PreservesComputedWires c g.toCandidateGauge) :
    ¬ ∀ g' : ObserverGauge N,
      fullLagrangianFixed α 1 1 G g ≤ fullLagrangianFixed α 1 1 G g' := by
  intro hmin
  have hlo := sat_preserving_gauge_rank_lower N c hcomp g.toCandidateGauge h
  have hzero := rank_eq_zero_of_action_le_trivial α G g hα (hmin (trivialObserverGauge N))
  omega

end GodMoveProductionConnection

#print axioms GodMoveProductionConnection.wireSpace_le_range_of_preserves
#print axioms GodMoveProductionConnection.wireRank_le_preserving_gauge_rank
#print axioms GodMoveProductionConnection.wireGauge_rank_minimal
#print axioms GodMoveProductionConnection.rank_penalty_monotone
#print axioms GodMoveProductionConnection.wireGauge_action_minimal_among_preserving
#print axioms GodMoveProductionConnection.sat_preserving_gauge_rank_lower
#print axioms GodMoveProductionConnection.actualSAT_gauge_rank_bounds
#print axioms GodMoveProductionConnection.sat_preserving_gauge_not_global_minimum
