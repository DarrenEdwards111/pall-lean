import GodMoveProductionGaugeBridge
import PallLean.Paper93.NFrame.UnitPreservingAdmissible

/-!
# Preserving the unit and one output needs at most two dimensions

The exact production unit-preserving admissibility predicate excludes the
zero projection. Adding preservation of an arbitrary output polynomial still
permits a projection onto the span of that output and the constant one. Its
range has dimension at most two, even when the output is a SAT characteristic
or has large derivative rank.

This is an algebraic existence theorem using a chosen linear complement.
It does not compute the projection efficiently, preserve an entire derivative
family, or claim that the projection minimizes any Lagrangian.
-/

namespace GodMoveUnitOutputGauge

open GodMoveBooleanInterpolation GodMoveComputedWireRank GodMoveProductionGaugeBridge
open PallLean.Paper93.NFrame

/-- A genuine production gauge onto the span of the unit and one output. -/
noncomputable def unitOutputGauge {n : ℕ} (p : Poly n) : CandidateGauge n :=
  spaceGauge (spanWires [1, p])

theorem unitOutputGauge_range {n : ℕ} (p : Poly n) :
    LinearMap.range (unitOutputGauge p).projection = spanWires [1, p] :=
  spaceGauge_range _

theorem unitOutputGauge_fixes_one {n : ℕ} (p : Poly n) :
    (unitOutputGauge p).projection 1 = 1 := by
  apply (spaceGauge_fixes_iff (spanWires [1, p]) 1).mpr
  apply Submodule.subset_span
  simp

theorem unitOutputGauge_fixes_output {n : ℕ} (p : Poly n) :
    (unitOutputGauge p).projection p = p := by
  apply (spaceGauge_fixes_iff (spanWires [1, p]) p).mpr
  apply Submodule.subset_span
  simp

/-- This satisfies the existing production refinement, without weakening or
redefining admissibility. -/
theorem unitOutputGauge_admissible {n : ℕ} (p : Poly n) :
    UnitPreservingAdmissibleGauge (unitOutputGauge p) :=
  ⟨spaceGauge_admissible _, unitOutputGauge_fixes_one p⟩

theorem unitOutputGauge_rank_le_two {n : ℕ} (p : Poly n) :
    Module.finrank ℚ (LinearMap.range (unitOutputGauge p).projection) ≤ 2 := by
  rw [unitOutputGauge_range]
  exact spanWires_finrank_le_length [1, p]

/-- Unit and output preservation impose no superconstant lower bound on
projection range dimension by themselves. -/
theorem exists_unitPreserving_outputGauge_rank_le_two {n : ℕ} (p : Poly n) :
    ∃ g : CandidateGauge n, UnitPreservingAdmissibleGauge g ∧
      g.projection p = p ∧ Module.finrank ℚ (LinearMap.range g.projection) ≤ 2 :=
  ⟨unitOutputGauge p, unitOutputGauge_admissible p,
    unitOutputGauge_fixes_output p, unitOutputGauge_rank_le_two p⟩

/-- The same conclusion applies to the actual SAT decision characteristic;
fixing that polynomial alone does not force a large production gauge. -/
theorem satDecision_unitOutputGauge_rank_le_two (n : ℕ) :
    UnitPreservingAdmissibleGauge (unitOutputGauge (satDecisionTarget n)) ∧
      (unitOutputGauge (satDecisionTarget n)).projection (satDecisionTarget n) =
        satDecisionTarget n ∧
      Module.finrank ℚ
        (LinearMap.range (unitOutputGauge (satDecisionTarget n)).projection) ≤ 2 :=
  ⟨unitOutputGauge_admissible _, unitOutputGauge_fixes_output _,
    unitOutputGauge_rank_le_two _⟩

end GodMoveUnitOutputGauge

#print axioms GodMoveUnitOutputGauge.unitOutputGauge_range
#print axioms GodMoveUnitOutputGauge.unitOutputGauge_fixes_one
#print axioms GodMoveUnitOutputGauge.unitOutputGauge_fixes_output
#print axioms GodMoveUnitOutputGauge.unitOutputGauge_admissible
#print axioms GodMoveUnitOutputGauge.unitOutputGauge_rank_le_two
#print axioms GodMoveUnitOutputGauge.exists_unitPreserving_outputGauge_rank_le_two
#print axioms GodMoveUnitOutputGauge.satDecision_unitOutputGauge_rank_le_two
