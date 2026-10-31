import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPDynamicPreservationFromCorrectness

/-!
# Dynamic trace geometry derives the decoder

`ComputationalDepthPvsNPDynamicPreservationFromCorrectness` named the final dynamic bridge as

```lean
decode_correct_of_decides_dynamic
```

This file pushes that bridge one step lower.  The decoder does not have to be postulated.  It can be
constructed from a concrete trace-geometry theorem:

```text
SAT correctness of D
  -> equal dynamic boundary cells imply equal hard residual labels.
```

That is exactly the image-quotient condition needed to define a decoder on boundary cells.  We prove the
quotient decoder by choice/default outside the image, then convert the trace-geometry bridge into the previous
dynamic preservation interface.

This still does not prove `P ≠ NP`: the remaining hard theorem is now the trace-geometry field

```lean
boundary_sound_of_decides
```

for a genuine NP-complete residual family and a polynomial dynamic boundary.  But the decoder is no longer a
primitive socket; it is derived from explicit boundary geometry.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsNPDynamicTraceGeometry

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPObserverSwitchToy
open PallLean.Paper93.DeepMath.PathB.PvsNPTranscriptObserver
open PallLean.Paper93.DeepMath.PathB.PvsNPHardResidualFamily
open PallLean.Paper93.DeepMath.PathB.PvsNPDynamicPreservationFromCorrectness

/-- Default assignment used for boundary cells outside the image of the residual family. -/
def defaultAssignment (m : Nat) : Assignment m :=
  fun _ => false

/-- Decode a boundary cell by choosing any residual branch that maps to it.

If the cell is outside the image, return a harmless default.  Correctness on the residual family follows exactly from
boundary-label soundness, i.e. from the fact that all preimages of the same cell carry the same semantic label. -/
noncomputable def decodeOfBoundary {U : MachineModel} {D : DecisionMachine U} {m : Nat}
    (P : DynamicSPDPBoundaryProjectionFor U D m) (fam : FoolingResidualFamily m) :
    P.boundary -> Assignment m := by
  classical
  exact fun y =>
    if h : exists a : Assignment m, P.projectedObserver (fam.instanceOf a) = y then
      fam.label (Classical.choose h)
    else
      defaultAssignment m

/-- The quotient decoder is correct whenever equal dynamic boundary cells imply equal residual labels. -/
theorem decodeOfBoundary_correct_of_sound {U : MachineModel} {D : DecisionMachine U} {m : Nat}
    (P : DynamicSPDPBoundaryProjectionFor U D m) (fam : FoolingResidualFamily m)
    (hsound : SoundOnFoolingFamily P.projectedObserver fam) :
    forall a : Assignment m,
      decodeOfBoundary P fam (P.projectedObserver (fam.instanceOf a)) = fam.label a := by
  classical
  intro a
  unfold decodeOfBoundary
  let h : exists b : Assignment m, P.projectedObserver (fam.instanceOf b) =
      P.projectedObserver (fam.instanceOf a) := ⟨a, rfl⟩
  rw [dif_pos h]
  exact hsound (Classical.choose h) a (Classical.choose_spec h)

/-- A dynamic trace-geometry theorem for one claimed SAT decider.

Compared with `DynamicSPDPPreservationFromCorrectnessFor`, this does not include a decoder.  It asks for the more
geometric statement that SAT correctness makes the dynamic boundary label-sound on the hard residual family.  The decoder
is then constructed in this file. -/
structure DynamicTraceGeometryFromCorrectnessFor
    (U : MachineModel) (D : DecisionMachine U) where
  m : Nat
  hardFamily : HardSATResidualFamily m
  projection : DynamicSPDPBoundaryProjectionFor U D m
  boundary_sound_of_decides :
    DecidesSAT U D -> SoundOnFoolingFamily projection.projectedObserver hardFamily.fam

namespace DynamicTraceGeometryFromCorrectnessFor

variable {U : MachineModel} {D : DecisionMachine U}

/-- The decoder induced by the dynamic trace geometry. -/
noncomputable def decode
    (G : DynamicTraceGeometryFromCorrectnessFor U D) : G.projection.boundary -> Assignment G.m :=
  decodeOfBoundary G.projection G.hardFamily.fam

/-- Dynamic trace geometry derives the previous `decode_correct_of_decides_dynamic` field. -/
theorem decode_correct_of_decides_dynamic
    (G : DynamicTraceGeometryFromCorrectnessFor U D) :
    DecidesSAT U D ->
      forall a : Assignment G.m,
        G.decode (G.projection.boundaryOf
          (G.projection.rawTrace (G.hardFamily.fam.instanceOf a))) = G.hardFamily.fam.label a := by
  intro hD a
  exact decodeOfBoundary_correct_of_sound
    G.projection G.hardFamily.fam (G.boundary_sound_of_decides hD) a

/-- Convert trace geometry into the dynamic preservation-from-correctness bridge. -/
noncomputable def toDynamicPreservation
    (G : DynamicTraceGeometryFromCorrectnessFor U D) :
    DynamicSPDPPreservationFromCorrectnessFor U D where
  m := G.m
  hardFamily := G.hardFamily
  projection := G.projection
  decode := G.decode
  decode_correct_of_decides_dynamic := G.decode_correct_of_decides_dynamic

/-- Therefore polynomial dynamic trace geometry below the exponential gap contradicts SAT correctness. -/
theorem not_decidesSAT
    (G : DynamicTraceGeometryFromCorrectnessFor U D) :
    ¬ DecidesSAT U D := by
  exact G.toDynamicPreservation.not_decidesSAT

/-- Direct contradiction form. -/
theorem contradiction_of_decides
    (G : DynamicTraceGeometryFromCorrectnessFor U D) (hD : DecidesSAT U D) : False := by
  exact G.not_decidesSAT hD

/-- The trace-geometry field itself is impossible below the exponential boundary gap under SAT correctness. -/
theorem boundary_soundness_is_the_gap
    (m k : Nat) (boundary : Type) [Fintype boundary]
    (obs : TranscriptObserver boundary) (fam : FoolingResidualFamily m)
    (hpoly : Fintype.card boundary <= m ^ k) (hgap : m ^ k < 2 ^ m) :
    ¬ SoundOnFoolingFamily obs fam := by
  exact poly_transcript_boundary_fails_fooling_soundness obs fam hpoly hgap

end DynamicTraceGeometryFromCorrectnessFor

/-- Global dynamic trace-geometry theorem target. -/
abbrev DynamicTraceGeometryFromCorrectnessForAllMachines (U : MachineModel) : Type 1 :=
  forall D : DecisionMachine U, DynamicTraceGeometryFromCorrectnessFor U D

/-- Cash-out: global trace geometry rules out polynomial-time SAT decision. -/
theorem no_SATDecisionInP_of_dynamicTraceGeometry {U : MachineModel}
    (hGeom : DynamicTraceGeometryFromCorrectnessForAllMachines U) :
    ¬ SATDecisionInP U := by
  intro hP
  rcases hP with ⟨D, hD⟩
  exact (hGeom D).not_decidesSAT hD

/-- Same cash-out through the dynamic preservation interface. -/
theorem no_SATDecisionInP_via_dynamicPreservation_of_dynamicTraceGeometry {U : MachineModel}
    (hGeom : DynamicTraceGeometryFromCorrectnessForAllMachines U) :
    ¬ SATDecisionInP U := by
  exact no_SATDecisionInP_of_dynamicPreservationFromCorrectness
    (fun D => (hGeom D).toDynamicPreservation)

/-!
## Status after this file

The bridge has been lowered from a decoder socket to a trace-geometry socket:

```text
boundary_sound_of_decides
  -> quotient decoder exists
  -> decode_correct_of_decides_dynamic
  -> dynamic preservation bridge
  -> no SATDecisionInP.
```

The remaining non-circular mathematical problem is precisely:

```lean
DecidesSAT U D -> SoundOnFoolingFamily projection.projectedObserver hardFamily.fam
```

for an explicit NP-complete hard residual family and a polynomial dynamic boundary.  This is the point where general
P-vs-NP hardness lives; for restricted solver classes it is the usual class-specific lower-bound theorem.
-/

end PallLean.Paper93.DeepMath.PathB.PvsNPDynamicTraceGeometry

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicTraceGeometry.decodeOfBoundary_correct_of_sound
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicTraceGeometry.DynamicTraceGeometryFromCorrectnessFor.decode_correct_of_decides_dynamic
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicTraceGeometry.DynamicTraceGeometryFromCorrectnessFor.toDynamicPreservation
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicTraceGeometry.DynamicTraceGeometryFromCorrectnessFor.not_decidesSAT
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicTraceGeometry.DynamicTraceGeometryFromCorrectnessFor.contradiction_of_decides
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicTraceGeometry.DynamicTraceGeometryFromCorrectnessFor.boundary_soundness_is_the_gap
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicTraceGeometry.no_SATDecisionInP_of_dynamicTraceGeometry
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicTraceGeometry.no_SATDecisionInP_via_dynamicPreservation_of_dynamicTraceGeometry
