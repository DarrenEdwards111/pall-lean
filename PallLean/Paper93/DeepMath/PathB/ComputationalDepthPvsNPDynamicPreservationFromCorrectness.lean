import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDynamicSPDP
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPHardResidualFamily

/-!
# Dynamic SPDP preservation from SAT correctness: the named bridge

The static P-vs-NP1 extraction theorem has the safe form

```text
TΦ(P) = Q · Φ + Δ,
Γ(TΦ(P)) ≤ Γ(P).
```

For the H4 / dynamic-SPDP route, the corresponding bridge is not a one-shot
polynomial projection.  It must be a time-indexed / transcript-indexed boundary
operation:

```text
SAT correctness of D
  -> dynamic projected boundary decodes hard residual labels
  -> exponentially many residual labels inject into polynomially many cells
  -> contradiction.
```

This file adds that bridge as an explicit frontier object.  It is deliberately not
claimed as solved: the live field is

```lean
decode_correct_of_decides_dynamic
```

and any genuine P-vs-NP proof must derive that field from concrete solver trace
geometry, not assume it.

What this file proves is the safe cash-out and conversions:

* dynamic correctness-derived label preservation implies the previous hard-residual
  decoder extraction interface;
* hence it implies the final decoder theorem;
* hence, below the exponential gap, it contradicts `DecidesSAT U D`;
* weak/static Bool truth observers are still fenced off by the existing dynamic-SPDP
  no-go theorem.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsNPDynamicPreservationFromCorrectness

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPObserverSwitchToy
open PallLean.Paper93.DeepMath.PathB.PvsNPTranscriptObserver
open PallLean.Paper93.DeepMath.PathB.PvsNPHardResidualFamily
open PallLean.Paper93.DeepMath.PathB.PvsNPFinalDecoderTheorem
open PallLean.Paper93.DeepMath.PathB.DynamicSPDP

/-- A dynamic boundary/projection surface for one claimed SAT decider.

`rawTrace` is intentionally indexed by the hard residual instance.  In a concrete
implementation it should be the operational trace/state stream produced by running `D`
on the residual instance.  `boundaryOf` is the dynamic SPDP/boundary projection of that
trace.  This structure contains only the P-side compression data; it does **not** contain
label preservation. -/
structure DynamicSPDPBoundaryProjectionFor
    (U : MachineModel) (D : DecisionMachine U) (m : Nat) where
  k : Nat
  dynamicTrace : Type
  boundary : Type
  fintypeBoundary : Fintype boundary
  rawTrace : ResidualInstance -> dynamicTrace
  boundaryOf : dynamicTrace -> boundary
  polyBoundary : @Fintype.card boundary fintypeBoundary <= m ^ k
  expGap : m ^ k < 2 ^ m

namespace DynamicSPDPBoundaryProjectionFor

/-- The induced projected transcript observer. -/
def projectedObserver {U : MachineModel} {D : DecisionMachine U} {m : Nat}
    (P : DynamicSPDPBoundaryProjectionFor U D m) : TranscriptObserver P.boundary :=
  fun x => P.boundaryOf (P.rawTrace x)

/-- Forget the dynamic presentation to the earlier generic solver transcript/projection surface. -/
def toSolverTranscriptProjection {U : MachineModel} {D : DecisionMachine U} {m : Nat}
    (P : DynamicSPDPBoundaryProjectionFor U D m) : SolverTranscriptProjectionFor U D m where
  k := P.k
  rawTranscript := P.dynamicTrace
  boundary := P.boundary
  fintypeBoundary := P.fintypeBoundary
  rawObserver := P.rawTrace
  project := P.boundaryOf
  polyBoundary := P.polyBoundary
  expGap := P.expGap

end DynamicSPDPBoundaryProjectionFor

/-- Dynamic SPDP preservation/decoding from correctness for one claimed decider.

This is the exact theorem we wanted to add.  The load-bearing field is
`decode_correct_of_decides_dynamic`:

```text
if D really decides SAT, then the dynamic boundary cell obtained from the residual
trace decodes the semantic residual label.
```

That field is the non-circular bridge still to be proved from real trace geometry. -/
structure DynamicSPDPPreservationFromCorrectnessFor
    (U : MachineModel) (D : DecisionMachine U) where
  m : Nat
  hardFamily : HardSATResidualFamily m
  projection : DynamicSPDPBoundaryProjectionFor U D m
  decode : projection.boundary -> Assignment m
  decode_correct_of_decides_dynamic :
    DecidesSAT U D ->
      forall a : Assignment m,
        decode (projection.boundaryOf
          (projection.rawTrace (hardFamily.fam.instanceOf a))) = hardFamily.fam.label a

namespace DynamicSPDPPreservationFromCorrectnessFor

variable {U : MachineModel} {D : DecisionMachine U}

/-- Convert the dynamic bridge to the previous hard-residual decoder interface. -/
def toHardResidualDecoderExtraction
    (E : DynamicSPDPPreservationFromCorrectnessFor U D) :
    HardResidualDecoderExtractionFor U D where
  m := E.m
  hardFamily := E.hardFamily
  projection := E.projection.toSolverTranscriptProjection
  decode := E.decode
  decode_correct_of_decides_for_hard_residuals := by
    intro hD a
    exact E.decode_correct_of_decides_dynamic hD a

/-- Convert the dynamic bridge directly to the final correctness-derived decoder interface. -/
def toCorrectnessDerivedLabelDecoder
    (E : DynamicSPDPPreservationFromCorrectnessFor U D) :
    CorrectnessDerivedLabelDecoderFor U D :=
  E.toHardResidualDecoderExtraction.toCorrectnessDerivedLabelDecoder

/-- SAT correctness plus dynamic preservation gives projected soundness on the hard residual family. -/
theorem sound_of_decides
    (E : DynamicSPDPPreservationFromCorrectnessFor U D) (hD : DecidesSAT U D) :
    SoundOnFoolingFamily E.projection.projectedObserver E.hardFamily.fam := by
  exact E.toHardResidualDecoderExtraction.sound_of_decides hD

/-- Below the exponential gap, the dynamic bridge is incompatible with `D` deciding SAT. -/
theorem not_decidesSAT
    (E : DynamicSPDPPreservationFromCorrectnessFor U D) :
    ¬ DecidesSAT U D := by
  exact E.toHardResidualDecoderExtraction.not_decidesSAT

/-- Direct contradiction form. -/
theorem contradiction_of_decides
    (E : DynamicSPDPPreservationFromCorrectnessFor U D) (hD : DecidesSAT U D) : False := by
  exact E.not_decidesSAT hD

/-- Diagnostic: the dynamic decoder correctness field is exactly the gap below the exponential boundary scale. -/
theorem dynamic_decoder_correctness_is_the_gap
    (m k : Nat) (dynamicTrace boundary : Type) [Fintype boundary]
    (rawTrace : ResidualInstance -> dynamicTrace)
    (boundaryOf : dynamicTrace -> boundary)
    (fam : FoolingResidualFamily m)
    (decode : boundary -> Assignment m)
    (hpoly : Fintype.card boundary <= m ^ k)
    (hgap : m ^ k < 2 ^ m) :
    ¬ (forall a : Assignment m,
        decode (boundaryOf (rawTrace (fam.instanceOf a))) = fam.label a) := by
  intro hdecode
  exact CorrectnessDerivedLabelDecoderFor.decoder_correctness_is_the_final_gap
    m k dynamicTrace boundary rawTrace boundaryOf fam decode hpoly hgap hdecode

end DynamicSPDPPreservationFromCorrectnessFor

/-- The global dynamic-SPDP preservation theorem target.

For every claimed polynomial-time SAT decider, produce a hard residual family, an operational
dynamic trace projection, and a decoder whose correctness follows from `DecidesSAT`.

This is a *frontier theorem*, not a solved lemma. -/
abbrev DynamicSPDPPreservationFromCorrectnessForAllMachines (U : MachineModel) : Type 1 :=
  forall D : DecisionMachine U, DynamicSPDPPreservationFromCorrectnessFor U D

/-- Cash-out: a global dynamic preservation theorem rules out polynomial-time SAT decision. -/
theorem no_SATDecisionInP_of_dynamicPreservationFromCorrectness {U : MachineModel}
    (hDyn : DynamicSPDPPreservationFromCorrectnessForAllMachines U) :
    ¬ SATDecisionInP U := by
  intro hP
  rcases hP with ⟨D, hD⟩
  exact (hDyn D).not_decidesSAT hD

/-- Same cash-out routed through the hard-residual interface. -/
theorem no_SATDecisionInP_via_hardResidual_of_dynamicPreservationFromCorrectness {U : MachineModel}
    (hDyn : DynamicSPDPPreservationFromCorrectnessForAllMachines U) :
    ¬ SATDecisionInP U := by
  exact no_SATDecisionInP_of_hardResidualDecoderExtraction
    (fun D => (hDyn D).toHardResidualDecoderExtraction)

/-- Same cash-out routed through the final decoder theorem. -/
theorem no_SATDecisionInP_via_finalDecoder_of_dynamicPreservationFromCorrectness {U : MachineModel}
    (hDyn : DynamicSPDPPreservationFromCorrectnessForAllMachines U) :
    ¬ SATDecisionInP U := by
  exact no_SATDecisionInP_of_correctnessDerivedLabelDecoders
    (fun D => (hDyn D).toCorrectnessDerivedLabelDecoder)

/-!
## Honest status

The new bridge is now named and connected:

```text
DynamicSPDPPreservationFromCorrectnessFor
  -> HardResidualDecoderExtractionFor
  -> CorrectnessDerivedLabelDecoderFor
  -> no SATDecisionInP.
```

The only live mathematical burden is the dynamic preservation field:

```lean
decode_correct_of_decides_dynamic
```

To avoid circularity, that field must be proved from an explicit NP-complete residual
family and concrete solver trace geometry.  The previously proved dynamic-SPDP no-go
remains in force: static Boolean residual truth is too weak and cannot supply this field.
-/

end PallLean.Paper93.DeepMath.PathB.PvsNPDynamicPreservationFromCorrectness

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicPreservationFromCorrectness.DynamicSPDPBoundaryProjectionFor.toSolverTranscriptProjection
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicPreservationFromCorrectness.DynamicSPDPPreservationFromCorrectnessFor.toHardResidualDecoderExtraction
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicPreservationFromCorrectness.DynamicSPDPPreservationFromCorrectnessFor.toCorrectnessDerivedLabelDecoder
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicPreservationFromCorrectness.DynamicSPDPPreservationFromCorrectnessFor.sound_of_decides
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicPreservationFromCorrectness.DynamicSPDPPreservationFromCorrectnessFor.not_decidesSAT
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicPreservationFromCorrectness.DynamicSPDPPreservationFromCorrectnessFor.contradiction_of_decides
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicPreservationFromCorrectness.DynamicSPDPPreservationFromCorrectnessFor.dynamic_decoder_correctness_is_the_gap
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicPreservationFromCorrectness.no_SATDecisionInP_of_dynamicPreservationFromCorrectness
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicPreservationFromCorrectness.no_SATDecisionInP_via_hardResidual_of_dynamicPreservationFromCorrectness
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicPreservationFromCorrectness.no_SATDecisionInP_via_finalDecoder_of_dynamicPreservationFromCorrectness
