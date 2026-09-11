import GodMoveRuntimeSnapshotRank
import GodMoveProductionGaugeBridge
import GodMoveSATSourceCanonicity

/-!
# A quadratic runtime bound in the production N-Frame gauge type

The range of this gauge is precisely the span of the actual machine's tape,
head, and control coordinate polynomials through its clock. Its production
rank is quadratically bounded by input length plus runtime, and it fixes
the actual normalized machine output, including the SAT characteristic
when the machine correctly decides SAT.

The projection uses the existing classical complement construction. This
does not provide an efficient basis/projection algorithm. The gauge is
different from both the computed-wire gauge and the designated-row gauge;
no containment of the output's derivative space is asserted. Production
rank, action, coordinates, and admissibility definitions are unchanged.
-/

namespace GodMoveRuntimeSnapshotGauge

open GodMoveBooleanInterpolation GodMoveRuntimeSnapshotRank
open GodMoveProductionGaugeBridge GodMoveComputedWireRank GodMoveCircuitConnection
open GodMoveSATSourceCanonicity
open PallLean.Paper93.NFrame PallLean.Paper93.Concrete
open PallLean.Paper93.DeepMath.PathB
open ComposableMachine ComposableStepCircuit ComposablePpolyDischarge
open PvsNPSeparatingInvariant CookLevinEmitClockBounds3

/-- An algebraic production gauge onto the actual snapshot-coordinate span. -/
noncomputable def snapshotGauge (M : Machine) (L t : ℕ) : ObserverGauge L :=
  ⟨spaceGauge (snapshotSpace M L t), trivialCoord L⟩

theorem snapshotGauge_range (M : Machine) (L t : ℕ) :
    LinearMap.range (snapshotGauge M L t).projection = snapshotSpace M L t :=
  spaceGauge_range _

theorem snapshotGauge_rank (M : Machine) (L t : ℕ) :
    Module.finrank ℚ (LinearMap.range (snapshotGauge M L t).projection) =
      Module.finrank ℚ (snapshotSpace M L t) := by
  rw [snapshotGauge_range]

theorem snapshotGauge_fixes_iff (M : Machine) (L t : ℕ) (p : Poly L) :
    (snapshotGauge M L t).projection p = p ↔ p ∈ snapshotSpace M L t :=
  spaceGauge_fixes_iff _ _

theorem snapshotGauge_admissible (M : Machine) (L t : ℕ) :
    AdmissibleGauge (snapshotGauge M L t).toCandidateGauge := spaceGauge_admissible _

theorem snapshotGauge_rank_le_clock (M : Machine) (L t : ℕ) :
    Module.finrank ℚ (LinearMap.range (snapshotGauge M L t).projection) ≤
      (t + 1) * (2 * (L + t + 1) + QM M) := by
  rw [snapshotGauge_range]
  exact snapshotRank_le_clock M L t

/-- The number of machine states is a constant for the fixed decider. -/
theorem snapshotGauge_rank_le_quadratic (M : Machine) (L t : ℕ) :
    Module.finrank ℚ (LinearMap.range (snapshotGauge M L t).projection) ≤
      (QM M + 2) * (L + t + 1) ^ 2 := by
  apply (snapshotGauge_rank_le_clock M L t).trans
  have hfirst : t + 1 ≤ L + t + 1 := by omega
  have hsecond : 2 * (L + t + 1) + QM M ≤ (QM M + 2) * (L + t + 1) := by
    have hq := Nat.mul_le_mul_left (QM M) (show 1 ≤ L + t + 1 by omega)
    nlinarith
  calc
    _ ≤ (L + t + 1) * ((QM M + 2) * (L + t + 1)) :=
      Nat.mul_le_mul hfirst hsecond
    _ = _ := by ring

theorem snapshotGauge_rank_polynomial (M : Machine) {T : ℕ → ℕ}
    (hT : PolyBounded T) :
    PolyBounded (fun L =>
      Module.finrank ℚ (LinearMap.range (snapshotGauge M L (T L)).projection)) := by
  have hS : PolyBounded (fun L => L + T L + 1) := PB_add (PB_add PB_id hT) (PB_const 1)
  apply PB_le (fun L => snapshotGauge_rank_le_clock M L (T L))
  exact PB_mul (PB_add hT (PB_const 1))
    (PB_add (PB_mul (PB_const 2) hS) (PB_const (QM M)))

theorem snapshotGauge_fixes_snapshot (M : Machine) (L t time : ℕ)
    (htime : time ≤ t) (pt : CPort M (L + t + 1)) :
    (snapshotGauge M L t).projection (snapshotPolynomial M L (L + t + 1) time pt) =
      snapshotPolynomial M L (L + t + 1) time pt :=
  (snapshotGauge_fixes_iff M L t _).mpr
    (snapshotPolynomial_mem_snapshotSpace M L t time htime pt)

theorem snapshotGauge_fixes_one (M : Machine) (L t : ℕ) :
    (snapshotGauge M L t).projection 1 = 1 :=
  (snapshotGauge_fixes_iff M L t _).mpr (one_mem_snapshotSpace M L t)

theorem snapshotGauge_fixes_decision (M : Machine) (L t : ℕ) :
    (snapshotGauge M L t).projection (decisionPolynomial M L t) = decisionPolynomial M L t :=
  (snapshotGauge_fixes_iff M L t _).mpr (decisionPolynomial_mem_snapshotSpace M L t)

/-- The captured polynomial is exactly the source of the faithful circuit
simulation, independently of any SAT or halting assumption. -/
theorem circuitTarget_eq_decisionPolynomial (M : Machine) (L t : ℕ) :
    circuitTarget (circuitFor M L t) = decisionPolynomial M L t := by
  rw [circuitTarget_eq_interpolate]
  exact interpolate_congr (circuitFor_output M L t)

theorem snapshotGauge_fixes_circuitTarget (M : Machine) (L t : ℕ) :
    (snapshotGauge M L t).projection (circuitTarget (circuitFor M L t)) =
      circuitTarget (circuitFor M L t) := by
  rw [circuitTarget_eq_decisionPolynomial]
  exact snapshotGauge_fixes_decision M L t

/-- Actual correctness on all encoded words identifies the fixed output
with the SAT decision characteristic; no rank premise is used. -/
theorem actualSAT_snapshotGauge_fixes_decision (M : Machine) (T : ℕ → ℕ)
    (hD : Decides M SeparationTarget.SATLang T) (L : ℕ) :
    (snapshotGauge M L (T L)).projection (satDecisionTarget L) = satDecisionTarget L := by
  rw [← actualSATCircuit_target M T hD L]
  exact snapshotGauge_fixes_circuitTarget M L (T L)

theorem actualSAT_snapshotGauge_fixes_characteristic (M : Machine) (T : ℕ → ℕ)
    (hD : Decides M SeparationTarget.SATLang T) (L : ℕ) :
    (snapshotGauge M L (T L)).projection
      (languageCharacteristic SeparationTarget.SATLang L) =
      languageCharacteristic SeparationTarget.SATLang L := by
  rw [← normalizedSource_eq_languageCharacteristic M SeparationTarget.SATLang T hD L]
  exact snapshotGauge_fixes_circuitTarget M L (T L)

/-- The production action is evaluated on this specific gauge. Its zero
coordinate field is allowed by the existing definition, not inferred from
machine geometry or minimization. -/
theorem snapshotGauge_action {L d : ℕ} (M : Machine) (t : ℕ)
    (G : RegularGraphFixed L d) (α β γ : ℝ) :
    fullLagrangianFixed α β γ G (snapshotGauge M L t) =
      β * (Module.finrank ℚ (snapshotSpace M L t) : ℝ) +
        γ / (1 + (Module.finrank ℚ (snapshotSpace M L t) : ℝ)) := by
  simp only [fullLagrangianFixed, logDetBarrier, snapshotGauge_rank]
  have he : (∑ e ∈ G.edges,
      ((snapshotGauge M L t).coord.values e.1 -
        (snapshotGauge M L t).coord.values e.2) ^ 2) = 0 := by
    simp [snapshotGauge, trivialCoord]
  rw [he]
  ring

theorem snapshotGauge_action_le_quadratic {L d : ℕ} (M : Machine) (t : ℕ)
    (G : RegularGraphFixed L d) (α : ℝ) :
    fullLagrangianFixed α 1 1 G (snapshotGauge M L t) ≤
      (((QM M + 2) * (L + t + 1) ^ 2 : ℕ) : ℝ) + 1 := by
  rw [snapshotGauge_action]
  have hr : (Module.finrank ℚ (snapshotSpace M L t) : ℝ) ≤
      (((QM M + 2) * (L + t + 1) ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast (show Module.finrank ℚ (snapshotSpace M L t) ≤
      (QM M + 2) * (L + t + 1) ^ 2 by
        simpa only [snapshotGauge_rank] using snapshotGauge_rank_le_quadratic M L t)
  have hb : 1 / (1 + (Module.finrank ℚ (snapshotSpace M L t) : ℝ)) ≤ 1 :=
    (div_le_one (by positivity)).mpr (by
      have := Nat.cast_nonneg (α := ℝ) (Module.finrank ℚ (snapshotSpace M L t))
      linarith)
  linarith

end GodMoveRuntimeSnapshotGauge

#print axioms GodMoveRuntimeSnapshotGauge.snapshotGauge_range
#print axioms GodMoveRuntimeSnapshotGauge.snapshotGauge_rank
#print axioms GodMoveRuntimeSnapshotGauge.snapshotGauge_admissible
#print axioms GodMoveRuntimeSnapshotGauge.snapshotGauge_rank_le_clock
#print axioms GodMoveRuntimeSnapshotGauge.snapshotGauge_rank_le_quadratic
#print axioms GodMoveRuntimeSnapshotGauge.snapshotGauge_rank_polynomial
#print axioms GodMoveRuntimeSnapshotGauge.snapshotGauge_fixes_snapshot
#print axioms GodMoveRuntimeSnapshotGauge.snapshotGauge_fixes_one
#print axioms GodMoveRuntimeSnapshotGauge.circuitTarget_eq_decisionPolynomial
#print axioms GodMoveRuntimeSnapshotGauge.snapshotGauge_fixes_circuitTarget
#print axioms GodMoveRuntimeSnapshotGauge.actualSAT_snapshotGauge_fixes_decision
#print axioms GodMoveRuntimeSnapshotGauge.actualSAT_snapshotGauge_fixes_characteristic
#print axioms GodMoveRuntimeSnapshotGauge.snapshotGauge_action
#print axioms GodMoveRuntimeSnapshotGauge.snapshotGauge_action_le_quadratic
