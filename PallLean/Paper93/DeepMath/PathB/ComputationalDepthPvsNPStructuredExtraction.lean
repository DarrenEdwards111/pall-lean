import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPDynamicH4Equivalence

/-!
# Structured dynamic-H4 extraction target

The previous audit proved that the old bridge

```lean
DynamicH4ForPTimeSAT U
```

is inhabited exactly when `¬ SATDecisionInP U`.  So proving that bridge directly would be circular: it is the lower bound
in another name.

This file replaces that extensional bridge by a **structured extraction interface**.  For a claimed SAT decider `D`, the
new target must explicitly provide:

* a raw transcript/state type `rawTranscript`;
* a finite projected boundary type `boundary`;
* a concrete transcript observer on residual SAT instances;
* a concrete boundary projection from raw transcripts to boundary cells;
* a fooling residual family;
* the preservation theorem saying the projected boundary cannot merge different fooling labels;
* the polynomial boundary bound;
* the exponential gap.

The point is not that these fields are currently proved.  The point is that the only dangerous field is now visible:
`preserves`.  The final theorems show that if all fields are supplied for every claimed SAT decider, then SAT has no
polynomial-time decider.  Unlike the old bridge, this interface is not merely a black-box request for an impossible
`DynamicH4Witness`; it names the construction that a future proof must actually instantiate.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsNPStructuredExtraction

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPTranscriptObserver
open PallLean.Paper93.DeepMath.PathB.PvsNPDynamicH4Theorem
open PallLean.Paper93.DeepMath.PathB.PvsNPPACAmplituhedronProjection

/-- A structured dynamic-H4 extraction from one claimed polynomial-time SAT decider.

`D` and `hD` are parameters on purpose: this is not an arbitrary witness.  It must be extracted from the concrete solver
surface under audit.

The load-bearing fields are:

* `project`: the boundary/compression map;
* `preserves`: equality after projection preserves the semantic/search labels of the fooling family;
* `polyBoundary`: the projected boundary is polynomially bounded;
* `expGap`: the fooling family is exponentially larger than that polynomial bound.
-/
structure StructuredDynamicH4ExtractionFor
    (U : MachineModel) (D : DecisionMachine U) (hD : DecidesSAT U D) where
  m : Nat
  k : Nat
  rawTranscript : Type
  boundary : Type
  fintypeBoundary : Fintype boundary
  rawObserver : TranscriptObserver rawTranscript
  project : rawTranscript -> boundary
  positiveCell : boundary -> Prop := fun _ => True
  project_positive : forall r : rawTranscript, positiveCell (project r) := by intro _; trivial
  fam : FoolingResidualFamily m
  preserves : SoundOnFoolingFamily (fun x => project (rawObserver x)) fam
  polyBoundary : @Fintype.card boundary fintypeBoundary <= m ^ k
  expGap : m ^ k < 2 ^ m

namespace StructuredDynamicH4ExtractionFor

variable {U : MachineModel} {D : DecisionMachine U} {hD : DecidesSAT U D}

/-- Package the explicit projection fields as the existing PAC/amplituhedron projection interface. -/
def toPACProjection (E : StructuredDynamicH4ExtractionFor U D hD) :
    PACAmplituhedronProjection E.rawTranscript E.boundary where
  project := E.project
  positiveCell := E.positiveCell
  project_positive := E.project_positive

/-- The projected observer determined by the structured extraction. -/
def projectedObserver (E : StructuredDynamicH4ExtractionFor U D hD) :
    TranscriptObserver E.boundary :=
  fun x => E.project (E.rawObserver x)

/-- The structured extraction converts to the old impossible dynamic-H4 witness.

This theorem is the bridge from the non-circular component interface back into the already-proved fooling-set lower-bound
machinery. -/
def toDynamicH4Witness (E : StructuredDynamicH4ExtractionFor U D hD) : DynamicH4Witness where
  m := E.m
  k := E.k
  α := E.boundary
  fintypeα := E.fintypeBoundary
  obs := E.projectedObserver
  fam := E.fam
  sound := E.preserves
  polyBoundary := E.polyBoundary
  expGap := E.expGap

/-- Any fully structured extraction is impossible.  The contradiction is exactly the dynamic transcript/fooling lower
bound: preservation injects `2^m` labels into a boundary with at most `m^k` cells. -/
theorem impossible (E : StructuredDynamicH4ExtractionFor U D hD) : False := by
  exact dynamicH4Witness_impossible E.toDynamicH4Witness

/-- Same impossibility routed through the PAC projection socket.  This is useful when the future construction is phrased
geometrically as a positive-cell projection. -/
theorem impossible_via_PAC (E : StructuredDynamicH4ExtractionFor U D hD) : False := by
  letI : Fintype E.boundary := E.fintypeBoundary
  exact PAC_projection_contradicts_poly_boundary
    E.toPACProjection E.rawObserver E.fam E.preserves E.polyBoundary E.expGap

/-- Load-bearing contrapositive: if the projection really has polynomial boundary below the exponential gap, then the
preservation field cannot hold.  This isolates the exact mathematical target for any future proof attempt. -/
theorem preservation_is_the_only_gap
    (m k : Nat) (rawTranscript boundary : Type) [Fintype boundary]
    (rawObserver : TranscriptObserver rawTranscript)
    (project : rawTranscript -> boundary)
    (positiveCell : boundary -> Prop)
    (project_positive : forall r : rawTranscript, positiveCell (project r))
    (fam : FoolingResidualFamily m)
    (hpoly : Fintype.card boundary <= m ^ k)
    (hgap : m ^ k < 2 ^ m) :
    ¬ SoundOnFoolingFamily (fun x => project (rawObserver x)) fam := by
  let P : PACAmplituhedronProjection rawTranscript boundary := {
    project := project
    positiveCell := positiveCell
    project_positive := project_positive
  }
  exact PAC_projection_must_lose_labels P rawObserver fam hpoly hgap

end StructuredDynamicH4ExtractionFor

/-- The non-circular replacement target for the old extensional bridge.

For every claimed polynomial-time SAT decider, explicitly extract the raw transcript surface, boundary projection,
fooling family, preservation theorem, polynomial bound, and exponential gap.

This is still a very hard theorem.  But unlike `DynamicH4ForPTimeSAT`, it exposes the construction rather than merely
requesting an impossible witness. -/
abbrev StructuredDynamicH4ForPTimeSAT (U : MachineModel) : Type 1 :=
  forall (D : DecisionMachine U) (hD : DecidesSAT U D),
    StructuredDynamicH4ExtractionFor U D hD

/-- A structured dynamic-H4 extraction theorem implies the old dynamic-H4 bridge. -/
def DynamicH4ForPTimeSAT_of_structured {U : MachineModel}
    (hStructured : StructuredDynamicH4ForPTimeSAT U) :
    DynamicH4ForPTimeSAT U := by
  intro D hD
  exact (hStructured D hD).toDynamicH4Witness

/-- Main cash-out: a structured extraction theorem for all claimed SAT deciders rules out polynomial-time SAT decision. -/
theorem no_SATDecisionInP_of_structuredDynamicH4 {U : MachineModel}
    (hStructured : StructuredDynamicH4ForPTimeSAT U) :
    ¬ SATDecisionInP U := by
  exact no_SATDecisionInP_of_DynamicH4
    (DynamicH4ForPTimeSAT_of_structured hStructured)

/-- Direct cash-out without passing through the old extensional bridge. -/
theorem no_SATDecisionInP_of_structuredDynamicH4_direct {U : MachineModel}
    (hStructured : StructuredDynamicH4ForPTimeSAT U) :
    ¬ SATDecisionInP U := by
  intro hP
  rcases hP with ⟨D, hD⟩
  exact (hStructured D hD).impossible

/-!
What remains after this file:

```text
Given a concrete claimed SAT decider D,
construct StructuredDynamicH4ExtractionFor U D hD.
```

The mechanical parts should be solver-model bookkeeping: transcript type, boundary projection, polynomial cell bound, and
scale gap.  The live mathematical obstacle is now named by
`StructuredDynamicH4ExtractionFor.preservation_is_the_only_gap`:

```text
equality of projected boundary cells -> equality of hard residual/search labels.
```

That preservation theorem is where any real P-vs-NP content must enter.
-/

end PallLean.Paper93.DeepMath.PathB.PvsNPStructuredExtraction

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPStructuredExtraction.StructuredDynamicH4ExtractionFor.toDynamicH4Witness
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPStructuredExtraction.StructuredDynamicH4ExtractionFor.impossible
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPStructuredExtraction.StructuredDynamicH4ExtractionFor.impossible_via_PAC
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPStructuredExtraction.StructuredDynamicH4ExtractionFor.preservation_is_the_only_gap
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPStructuredExtraction.DynamicH4ForPTimeSAT_of_structured
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPStructuredExtraction.no_SATDecisionInP_of_structuredDynamicH4
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPStructuredExtraction.no_SATDecisionInP_of_structuredDynamicH4_direct
