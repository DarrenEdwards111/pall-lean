import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPDynamicTraceGeometry

/-!
# No-go: SAT correctness alone does not imply dynamic boundary soundness

`ComputationalDepthPvsNPDynamicTraceGeometry` lowered the final bridge to the field

```lean
boundary_sound_of_decides :
  DecidesSAT U D -> SoundOnFoolingFamily projection.projectedObserver hardFamily.fam
```

This file proves the guardrail: the field cannot be derived from `DecidesSAT U D` alone.
A constant dynamic boundary has polynomial size and can be paired with any decider, but it collapses the two labels of a
one-bit fooling family.  Therefore any non-circular proof of `boundary_sound_of_decides` must use an additional concrete
trace-geometry invariant tying the solver's dynamic boundary to the hard residual labels.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsNPDynamicTraceGeometryNoGo

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPObserverSwitchToy
open PallLean.Paper93.DeepMath.PathB.PvsNPTranscriptObserver
open PallLean.Paper93.DeepMath.PathB.PvsNPDynamicPreservationFromCorrectness
open PallLean.Paper93.DeepMath.PathB.PvsNPDynamicTraceGeometry

/-- The all-false one-bit assignment. -/
def bitZero : Assignment 1 :=
  fun _ => false

/-- The all-true one-bit assignment. -/
def bitOne : Assignment 1 :=
  fun _ => true

/-- The two one-bit assignments are distinct. -/
theorem bitZero_ne_bitOne : bitZero ≠ bitOne := by
  intro h
  have h0 := congrFun h (0 : Fin 1)
  simp [bitZero, bitOne] at h0

/-- Any one-bit fooling family has two distinct labels. -/
theorem one_bit_fooling_labels_distinct (fam : FoolingResidualFamily 1) :
    fam.label bitZero ≠ fam.label bitOne := by
  intro hlabel
  exact bitZero_ne_bitOne (fam.label_injective hlabel)

/-- The constant dynamic observer induced by the one-point boundary. -/
def constantTranscriptObserver : TranscriptObserver PUnit :=
  fun _ => PUnit.unit

/-- A constant boundary is not sound for any one-bit fooling family. -/
theorem constant_boundary_not_sound_one_bit (fam : FoolingResidualFamily 1) :
    ¬ SoundOnFoolingFamily constantTranscriptObserver fam := by
  intro hsound
  have hlabels : fam.label bitZero = fam.label bitOne := hsound bitZero bitOne rfl
  exact one_bit_fooling_labels_distinct fam hlabels

/-- The canonical constant dynamic projection.  It has a one-cell boundary, hence satisfies the polynomial boundary
and the `1 < 2` exponential gap at `m = 1, k = 0`. -/
def constantDynamicProjection (U : MachineModel) (D : DecisionMachine U) :
    DynamicSPDPBoundaryProjectionFor U D 1 where
  k := 0
  dynamicTrace := PUnit
  boundary := PUnit
  fintypeBoundary := inferInstance
  rawTrace := fun _ => PUnit.unit
  boundaryOf := fun _ => PUnit.unit
  polyBoundary := by
    simp
  expGap := by
    norm_num

/-- The projected observer of the constant dynamic projection is the constant observer. -/
theorem constantDynamicProjection_projectedObserver_eq
    (U : MachineModel) (D : DecisionMachine U) :
    (constantDynamicProjection U D).projectedObserver = constantTranscriptObserver := by
  funext x
  rfl

/-- `DecidesSAT` alone cannot imply boundary soundness: the constant boundary collapses the two labels of every one-bit
fooling family, regardless of the decider.  The `hD` argument is intentionally unused: this is the point of the no-go. -/
theorem decidesSAT_does_not_force_boundary_soundness_constant
    {U : MachineModel} {D : DecisionMachine U}
    (_hD : DecidesSAT U D) (fam : FoolingResidualFamily 1) :
    ¬ SoundOnFoolingFamily (constantDynamicProjection U D).projectedObserver fam := by
  rw [constantDynamicProjection_projectedObserver_eq]
  exact constant_boundary_not_sound_one_bit fam

/-- Conditional phrasing: if a SAT decider exists, then no theorem using only `DecidesSAT U D` can certify the constant
projection as sound on a one-bit fooling family. -/
theorem no_boundary_sound_of_decides_for_constant_projection
    {U : MachineModel} {D : DecisionMachine U} (hD : DecidesSAT U D)
    (fam : FoolingResidualFamily 1) :
    ¬ (DecidesSAT U D ->
        SoundOnFoolingFamily (constantDynamicProjection U D).projectedObserver fam) := by
  intro h
  exact decidesSAT_does_not_force_boundary_soundness_constant hD fam (h hD)

/-- If a dynamic trace-geometry object uses the constant projection, then it rules out `DecidesSAT` immediately; it cannot
be obtained from correctness alone. -/
theorem constant_projection_trace_geometry_implies_not_decidesSAT
    {U : MachineModel} {D : DecisionMachine U}
    (hardFamily : PallLean.Paper93.DeepMath.PathB.PvsNPHardResidualFamily.HardSATResidualFamily 1)
    (hgeom : DecidesSAT U D ->
      SoundOnFoolingFamily (constantDynamicProjection U D).projectedObserver hardFamily.fam) :
    ¬ DecidesSAT U D := by
  intro hD
  exact decidesSAT_does_not_force_boundary_soundness_constant hD hardFamily.fam (hgeom hD)

/-!
Conclusion:

```text
DecidesSAT U D
```

is not enough.  A future proof of `boundary_sound_of_decides` must use a genuine dynamic trace-geometry invariant such
as a restricted solver lower bound, a transcript fooling-set theorem, or a proof-complexity/search obstruction.  Otherwise
the constant projection is an immediate counterexample.
-/

end PallLean.Paper93.DeepMath.PathB.PvsNPDynamicTraceGeometryNoGo

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicTraceGeometryNoGo.bitZero_ne_bitOne
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicTraceGeometryNoGo.one_bit_fooling_labels_distinct
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicTraceGeometryNoGo.constant_boundary_not_sound_one_bit
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicTraceGeometryNoGo.constantDynamicProjection_projectedObserver_eq
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicTraceGeometryNoGo.decidesSAT_does_not_force_boundary_soundness_constant
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicTraceGeometryNoGo.no_boundary_sound_of_decides_for_constant_projection
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicTraceGeometryNoGo.constant_projection_trace_geometry_implies_not_decidesSAT
