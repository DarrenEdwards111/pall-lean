import GodMoveComputedWireRank
import PallLean.Paper93.Concrete.FullLagrangianFixed
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Exact computed-wire realization in the production gauge type

A finite-dimensional subspace of the production polynomial ambient space has
a linear complement. Projecting along a chosen complement gives an actual
`CandidateGauge`, with exactly that range. Applying this to the computed-wire
space preserves its rank and fixes every normalized wire, including the SAT
decision target of a correct unrolled machine.

This is an algebraic realization using classical choice, not an efficient
algorithm for selecting a basis or representing the projection. The attached
coordinates are zero, as permitted by the current independent coordinate
field. Neither variational minimality nor geometric faithfulness is asserted.
No production gauge, action, or admissibility definition is changed.
-/

namespace GodMoveProductionGaugeBridge

open GodMoveBooleanInterpolation GodMoveComputedWireRank GodMoveCircuitConnection
open GodMoveCircuitRuntimeCost
open PallLean.Paper93.NFrame PallLean.Paper93.Concrete
open PallLean.Paper93.DeepMath.PathB
open NFrameBoundaryTransducer (CGate)
open ComposableMachine
open Submodule

/-- Algebraic projection onto the given space; its complement is chosen,
not constructed by an efficient machine algorithm. -/
noncomputable def spaceGauge {n : ℕ} (W : Submodule ℚ (Poly n))
    [Module.Finite ℚ W] : CandidateGauge n where
  projection := (Classical.choose_spec W.exists_isCompl).projection
  is_idempotent := (Classical.choose_spec W.exists_isCompl).projection_isIdempotentElem
  rank_finite := by
    rw [(Classical.choose_spec W.exists_isCompl).projection_range]
    infer_instance

theorem spaceGauge_range {n : ℕ} (W : Submodule ℚ (Poly n)) [Module.Finite ℚ W] :
    LinearMap.range (spaceGauge W).projection = W :=
  (Classical.choose_spec W.exists_isCompl).projection_range

theorem spaceGauge_fixes_iff {n : ℕ} (W : Submodule ℚ (Poly n))
    [Module.Finite ℚ W] (p : Poly n) :
    (spaceGauge W).projection p = p ↔ p ∈ W :=
  (Classical.choose_spec W.exists_isCompl).projection_eq_self_iff p

theorem spaceGauge_admissible {n : ℕ} (W : Submodule ℚ (Poly n))
    [Module.Finite ℚ W] : AdmissibleGauge (spaceGauge W) :=
  ⟨0, (spaceGauge W).projection.map_zero⟩

/-- An observer gauge in the exact production type, carrying the wire span. -/
noncomputable def wireGauge {n : ℕ} (c : List (CGate n)) : ObserverGauge n :=
  ⟨spaceGauge (wireSpace c), trivialCoord n⟩

theorem wireGauge_range {n : ℕ} (c : List (CGate n)) :
    LinearMap.range (wireGauge c).projection = wireSpace c :=
  spaceGauge_range _

/-- The production projection rank is exactly the operationally bounded rank. -/
theorem wireGauge_rank {n : ℕ} (c : List (CGate n)) :
    Module.finrank ℚ (LinearMap.range (wireGauge c).projection) = wireRank c := by
  rw [wireGauge_range]
  rfl

theorem wireGauge_admissible {n : ℕ} (c : List (CGate n)) :
    AdmissibleGauge (wireGauge c).toCandidateGauge := spaceGauge_admissible (wireSpace c)

theorem wireGauge_fixes_iff {n : ℕ} (c : List (CGate n)) (p : Poly n) :
    (wireGauge c).projection p = p ↔ p ∈ wireSpace c := spaceGauge_fixes_iff _ _

theorem wireGauge_fixes_target {n : ℕ} (c : List (CGate n)) :
    (wireGauge c).projection (circuitTarget c) = circuitTarget c :=
  (wireGauge_fixes_iff c _).mpr (circuitTarget_mem_wireSpace c)

theorem wireGauge_fixes_wire {n : ℕ} (c : List (CGate n))
    (p : Poly n) (hp : p ∈ normalizedWires c) :
    (wireGauge c).projection p = p := by
  apply (wireGauge_fixes_iff c p).mpr
  apply Submodule.subset_span
  simpa using hp

theorem wireGauge_rank_le_length {n : ℕ} (c : List (CGate n)) :
    Module.finrank ℚ (LinearMap.range (wireGauge c).projection) ≤ c.length := by
  rw [wireGauge_rank]
  exact wireRank_le_length c

theorem wireGauge_rank_append_gate_le {n : ℕ} (c : List (CGate n)) (g : CGate n) :
    Module.finrank ℚ (LinearMap.range (wireGauge (c ++ [g])).projection) ≤
      Module.finrank ℚ (LinearMap.range (wireGauge c).projection) + 1 := by
  rw [wireGauge_rank, wireGauge_rank]
  exact wireRank_append_gate_le c g

theorem actualMachine_gauge_rank_le_clock (M : Machine) (L t : ℕ) :
    Module.finrank ℚ (LinearMap.range
      (wireGauge (ComposablePpolyDischarge.circuitFor M L t)).projection) ≤
      circuitConstant M * (L + t + 1) ^ 4 := by
  rw [wireGauge_rank]
  exact unrolled_wireRank_le_clock M L t

theorem actualMachine_gauge_rank_polynomial (M : Machine) {T : ℕ → ℕ}
    (hT : PvsNPSeparatingInvariant.PolyBounded T) :
    PvsNPSeparatingInvariant.PolyBounded (fun L =>
      Module.finrank ℚ (LinearMap.range
        (wireGauge (ComposablePpolyDischarge.circuitFor M L (T L))).projection)) := by
  simp only [wireGauge_rank]
  exact unrolled_wireRank_polynomial M hT

theorem actualSAT_gauge_fixes_decision (M : Machine) (T : ℕ → ℕ)
    (hD : Decides M SeparationTarget.SATLang T) (L : ℕ) :
    (wireGauge (ComposablePpolyDischarge.circuitFor M L (T L))).projection
      (satDecisionTarget L) = satDecisionTarget L :=
  (wireGauge_fixes_iff _ _).mpr (satDecisionTarget_mem_actualWireSpace M T hD L)

/-- Evaluating the unchanged production action on the constructed gauge.
Its coordinate energy vanishes because the permitted coordinate field is zero. -/
theorem wireGauge_action {n d : ℕ} (c : List (CGate n))
    (G : RegularGraphFixed n d) (α β γ : ℝ) :
    fullLagrangianFixed α β γ G (wireGauge c) =
      β * (wireRank c : ℝ) + γ / (1 + (wireRank c : ℝ)) := by
  simp only [fullLagrangianFixed, logDetBarrier, wireGauge_rank]
  have he : (∑ e ∈ G.edges,
      ((wireGauge c).coord.values e.1 - (wireGauge c).coord.values e.2) ^ 2) = 0 := by
    simp [wireGauge, trivialCoord]
  rw [he]
  ring

theorem wireGauge_action_le_length_add_one {n d : ℕ} (c : List (CGate n))
    (G : RegularGraphFixed n d) (α : ℝ) :
    fullLagrangianFixed α 1 1 G (wireGauge c) ≤ (c.length : ℝ) + 1 := by
  rw [wireGauge_action]
  have hr : (wireRank c : ℝ) ≤ c.length := by exact_mod_cast wireRank_le_length c
  have hb : 1 / (1 + (wireRank c : ℝ)) ≤ 1 :=
    (div_le_one (by positivity)).mpr (by have := Nat.cast_nonneg (α := ℝ) (wireRank c); linarith)
  linarith

end GodMoveProductionGaugeBridge

#print axioms GodMoveProductionGaugeBridge.spaceGauge_range
#print axioms GodMoveProductionGaugeBridge.spaceGauge_fixes_iff
#print axioms GodMoveProductionGaugeBridge.wireGauge_rank
#print axioms GodMoveProductionGaugeBridge.wireGauge_fixes_target
#print axioms GodMoveProductionGaugeBridge.wireGauge_fixes_wire
#print axioms GodMoveProductionGaugeBridge.wireGauge_rank_append_gate_le
#print axioms GodMoveProductionGaugeBridge.actualMachine_gauge_rank_le_clock
#print axioms GodMoveProductionGaugeBridge.actualMachine_gauge_rank_polynomial
#print axioms GodMoveProductionGaugeBridge.actualSAT_gauge_fixes_decision
#print axioms GodMoveProductionGaugeBridge.wireGauge_action
#print axioms GodMoveProductionGaugeBridge.wireGauge_action_le_length_add_one
