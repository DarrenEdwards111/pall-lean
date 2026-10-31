import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPDynamicTraceGeometryNoGo

/-!
# Dynamic trace-label invariant: the extra geometry needed after the no-go

`ComputationalDepthPvsNPDynamicTraceGeometryNoGo` proves that `DecidesSAT U D` alone cannot force boundary soundness:
a constant one-cell boundary collapses labels.  Therefore the next legitimate bridge must include an additional concrete
trace-geometry invariant.

This file names one such invariant and proves the safe derivation:

```text
trace carries the residual label
+ boundary projection preserves that trace label
------------------------------------------------
boundary is sound on the fooling family
```

Then it packages the conditional version:

```lean
DecidesSAT U D -> DynamicTraceLabelInvariantFor ...
```

which converts into the existing `DynamicTraceGeometryFromCorrectnessFor` interface.  This is the correct next theorem
target for restricted solver classes or any future non-circular P-vs-NP trace geometry.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsNPDynamicTraceInvariant

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPObserverSwitchToy
open PallLean.Paper93.DeepMath.PathB.PvsNPTranscriptObserver
open PallLean.Paper93.DeepMath.PathB.PvsNPHardResidualFamily
open PallLean.Paper93.DeepMath.PathB.PvsNPDynamicPreservationFromCorrectness
open PallLean.Paper93.DeepMath.PathB.PvsNPDynamicTraceGeometry

/-- A concrete dynamic trace-label invariant for a projection and a fooling family.

The trace-level label is allowed to live in the full dynamic trace.  The boundary-level label is what survives the
projection.  The two correctness fields say:

* raw traces of residual instances carry the semantic label;
* the projected boundary preserves that trace label on the residual family.

This is stronger than bare SAT truth and is exactly the kind of extra geometry the no-go says is necessary. -/
structure DynamicTraceLabelInvariantFor {U : MachineModel} {D : DecisionMachine U} {m : Nat}
    (P : DynamicSPDPBoundaryProjectionFor U D m) (fam : FoolingResidualFamily m) where
  traceLabel : P.dynamicTrace -> Assignment m
  boundaryLabel : P.boundary -> Assignment m
  rawTrace_carries_label :
    forall a : Assignment m,
      traceLabel (P.rawTrace (fam.instanceOf a)) = fam.label a
  boundary_preserves_traceLabel :
    forall a : Assignment m,
      boundaryLabel (P.boundaryOf (P.rawTrace (fam.instanceOf a))) =
        traceLabel (P.rawTrace (fam.instanceOf a))

namespace DynamicTraceLabelInvariantFor

variable {U : MachineModel} {D : DecisionMachine U} {m : Nat}
variable {P : DynamicSPDPBoundaryProjectionFor U D m} {fam : FoolingResidualFamily m}

/-- The boundary label induced by a trace-label invariant decodes every residual label. -/
theorem boundaryLabel_correct
    (I : DynamicTraceLabelInvariantFor P fam) :
    forall a : Assignment m,
      I.boundaryLabel (P.projectedObserver (fam.instanceOf a)) = fam.label a := by
  intro a
  calc
    I.boundaryLabel (P.projectedObserver (fam.instanceOf a))
        = I.boundaryLabel (P.boundaryOf (P.rawTrace (fam.instanceOf a))) := rfl
    _ = I.traceLabel (P.rawTrace (fam.instanceOf a)) := I.boundary_preserves_traceLabel a
    _ = fam.label a := I.rawTrace_carries_label a

/-- A dynamic trace-label invariant implies fooling-family boundary soundness. -/
theorem soundOnFoolingFamily
    (I : DynamicTraceLabelInvariantFor P fam) :
    SoundOnFoolingFamily P.projectedObserver fam := by
  intro a b heq
  have ha := I.boundaryLabel_correct a
  have hb := I.boundaryLabel_correct b
  rw [heq] at ha
  exact ha.symm.trans hb

/-- Therefore a polynomial boundary below the exponential gap cannot satisfy such a trace-label invariant. -/
theorem impossible_below_gap
    (I : DynamicTraceLabelInvariantFor P fam)
    (hpoly : @Fintype.card P.boundary P.fintypeBoundary <= m ^ P.k)
    (hgap : m ^ P.k < 2 ^ m) : False := by
  letI : Fintype P.boundary := P.fintypeBoundary
  exact transcript_fooling_contradicts_poly_boundary
    P.projectedObserver fam I.soundOnFoolingFamily hpoly hgap

/-- In particular, using the projection's own polynomial and gap fields, the invariant is impossible. -/
theorem impossible
    (I : DynamicTraceLabelInvariantFor P fam) : False := by
  exact I.impossible_below_gap P.polyBoundary P.expGap

end DynamicTraceLabelInvariantFor

/-- Conditional trace-label invariant for one claimed SAT decider.

This is the correct replacement for the impossible hope that `DecidesSAT` alone gives soundness.  A future restricted-class
or trace-geometry theorem must prove `invariant_of_decides` from the actual operational semantics of the solver and the
chosen residual family. -/
structure DynamicTraceInvariantFromCorrectnessFor
    (U : MachineModel) (D : DecisionMachine U) where
  m : Nat
  hardFamily : HardSATResidualFamily m
  projection : DynamicSPDPBoundaryProjectionFor U D m
  invariant_of_decides :
    DecidesSAT U D -> DynamicTraceLabelInvariantFor projection hardFamily.fam

namespace DynamicTraceInvariantFromCorrectnessFor

variable {U : MachineModel} {D : DecisionMachine U}

/-- Conditional trace-label invariance derives boundary soundness from correctness. -/
theorem boundary_sound_of_decides
    (G : DynamicTraceInvariantFromCorrectnessFor U D) :
    DecidesSAT U D -> SoundOnFoolingFamily G.projection.projectedObserver G.hardFamily.fam := by
  intro hD
  exact (G.invariant_of_decides hD).soundOnFoolingFamily

/-- Convert the invariant layer into the dynamic trace-geometry interface. -/
def toDynamicTraceGeometry
    (G : DynamicTraceInvariantFromCorrectnessFor U D) :
    DynamicTraceGeometryFromCorrectnessFor U D where
  m := G.m
  hardFamily := G.hardFamily
  projection := G.projection
  boundary_sound_of_decides := G.boundary_sound_of_decides

/-- Hence the invariant layer cashes out through the existing dynamic trace-geometry theorem. -/
theorem not_decidesSAT
    (G : DynamicTraceInvariantFromCorrectnessFor U D) :
    ¬ DecidesSAT U D := by
  exact G.toDynamicTraceGeometry.not_decidesSAT

/-- Direct contradiction form. -/
theorem contradiction_of_decides
    (G : DynamicTraceInvariantFromCorrectnessFor U D) (hD : DecidesSAT U D) : False := by
  exact G.not_decidesSAT hD

/-- Even before converting interfaces, an invariant obtained from a correct decider is impossible below the projection's
own polynomial/exponential gap. -/
theorem invariant_of_decides_impossible
    (G : DynamicTraceInvariantFromCorrectnessFor U D) (hD : DecidesSAT U D) : False := by
  exact (G.invariant_of_decides hD).impossible

end DynamicTraceInvariantFromCorrectnessFor

/-- Global theorem target at the invariant layer. -/
abbrev DynamicTraceInvariantFromCorrectnessForAllMachines (U : MachineModel) : Type 1 :=
  forall D : DecisionMachine U, DynamicTraceInvariantFromCorrectnessFor U D

/-- Cash-out: global conditional trace-label invariants rule out polynomial-time SAT decision. -/
theorem no_SATDecisionInP_of_dynamicTraceInvariant {U : MachineModel}
    (hInv : DynamicTraceInvariantFromCorrectnessForAllMachines U) :
    ¬ SATDecisionInP U := by
  intro hP
  rcases hP with ⟨D, hD⟩
  exact (hInv D).not_decidesSAT hD

/-- Same cash-out through the dynamic trace-geometry layer. -/
theorem no_SATDecisionInP_via_traceGeometry_of_dynamicTraceInvariant {U : MachineModel}
    (hInv : DynamicTraceInvariantFromCorrectnessForAllMachines U) :
    ¬ SATDecisionInP U := by
  exact no_SATDecisionInP_of_dynamicTraceGeometry
    (fun D => (hInv D).toDynamicTraceGeometry)

/-!
## Status

The valid next bridge is now:

```lean
DecidesSAT U D -> DynamicTraceLabelInvariantFor projection hardFamily.fam
```

not merely `DecidesSAT U D -> SoundOnFoolingFamily ...`, and definitely not `DecidesSAT U D` alone.

For restricted solver classes, `invariant_of_decides` is where the class-specific lower bound belongs.  For general `P`,
proving it for an NP-complete residual family would be the actual P-vs-NP breakthrough.
-/

end PallLean.Paper93.DeepMath.PathB.PvsNPDynamicTraceInvariant

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicTraceInvariant.DynamicTraceLabelInvariantFor.boundaryLabel_correct
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicTraceInvariant.DynamicTraceLabelInvariantFor.soundOnFoolingFamily
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicTraceInvariant.DynamicTraceLabelInvariantFor.impossible_below_gap
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicTraceInvariant.DynamicTraceLabelInvariantFor.impossible
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicTraceInvariant.DynamicTraceInvariantFromCorrectnessFor.boundary_sound_of_decides
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicTraceInvariant.DynamicTraceInvariantFromCorrectnessFor.toDynamicTraceGeometry
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicTraceInvariant.DynamicTraceInvariantFromCorrectnessFor.not_decidesSAT
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicTraceInvariant.DynamicTraceInvariantFromCorrectnessFor.contradiction_of_decides
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicTraceInvariant.DynamicTraceInvariantFromCorrectnessFor.invariant_of_decides_impossible
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicTraceInvariant.no_SATDecisionInP_of_dynamicTraceInvariant
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicTraceInvariant.no_SATDecisionInP_via_traceGeometry_of_dynamicTraceInvariant
