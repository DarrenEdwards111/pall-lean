import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPStructuredExtraction

/-!
# P-vs-NP final theorem shape: correctness-derived label decoding

The previous RHA/Tseitin files made the last obstruction visible but still carried

```lean
preservesLabels : SoundOnFoolingFamily ...
```

as a field.  That is too weak as a final theorem statement: preservation is exactly what must be proved from SAT-solver
correctness, not assumed.

This file states the sharper final target.  A projected boundary/cell is useful only if it comes with a **decoder** whose
correctness is derived from `DecidesSAT U D`.  The decoder theorem says that, on a hard residual family, the projected
state of the alleged solver determines the semantic/search label.

```text
SAT correctness of D
  -> projected boundary cell determines residual label
  -> projected observer is sound on the fooling family
  -> at least 2^m projected cells
  -> contradiction with polynomial boundary m^k < 2^m.
```

This is still not a proof of `P ≠ NP`: the hard future theorem is to construct such a decoder for a genuine NP-complete
residual family from an arbitrary claimed polynomial-time SAT decider.  But the load-bearing assumption is now exactly the
right one: **label decoding from correctness**, not label preservation as an unexplained field.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsNPFinalDecoderTheorem

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPObserverSwitchToy
open PallLean.Paper93.DeepMath.PathB.PvsNPTranscriptObserver
open PallLean.Paper93.DeepMath.PathB.PvsNPStructuredExtraction

/-- A correctness-derived label decoder for one claimed SAT decider.

The key field is `decode_correct_of_decides`: it is not a preservation assumption.  It says that if `D` really decides
SAT, then the compressed/projected boundary value contains enough information for `decode` to recover the fooling-family
label.

For a real P-vs-NP proof, this field must be proved from the operational semantics of `D` and the chosen hard residual
family, not postulated for an arbitrary projection. -/
structure CorrectnessDerivedLabelDecoderFor
    (U : MachineModel) (D : DecisionMachine U) where
  m : Nat
  k : Nat
  rawTranscript : Type
  boundary : Type
  fintypeBoundary : Fintype boundary
  rawObserver : TranscriptObserver rawTranscript
  project : rawTranscript -> boundary
  fam : FoolingResidualFamily m
  decode : boundary -> Assignment m
  decode_correct_of_decides :
    DecidesSAT U D ->
      forall a : Assignment m,
        decode (project (rawObserver (fam.instanceOf a))) = fam.label a
  polyBoundary : @Fintype.card boundary fintypeBoundary <= m ^ k
  expGap : m ^ k < 2 ^ m

namespace CorrectnessDerivedLabelDecoderFor

variable {U : MachineModel} {D : DecisionMachine U}

/-- The projected observer determined by the decoder extraction. -/
def projectedObserver (E : CorrectnessDerivedLabelDecoderFor U D) :
    TranscriptObserver E.boundary :=
  fun x => E.project (E.rawObserver x)

/-- Decoder correctness derived from SAT correctness gives the formerly-assumed preservation theorem. -/
theorem sound_of_decode_correct
    (E : CorrectnessDerivedLabelDecoderFor U D) (hD : DecidesSAT U D) :
    SoundOnFoolingFamily E.projectedObserver E.fam := by
  intro a b heq
  have ha := E.decode_correct_of_decides hD a
  have hb := E.decode_correct_of_decides hD b
  unfold projectedObserver at heq
  rw [heq] at ha
  exact ha.symm.trans hb

/-- Therefore any correctness-derived decoder below the exponential gap contradicts SAT correctness of `D`. -/
theorem not_decidesSAT
    (E : CorrectnessDerivedLabelDecoderFor U D) :
    ¬ DecidesSAT U D := by
  intro hD
  letI : Fintype E.boundary := E.fintypeBoundary
  exact transcript_fooling_contradicts_poly_boundary
    E.projectedObserver E.fam (E.sound_of_decode_correct hD) E.polyBoundary E.expGap

/-- Equivalently: under a claimed correct decider, the decoder theorem itself is impossible below the exponential gap. -/
theorem decoder_correctness_is_the_final_gap
    (m k : Nat) (rawTranscript boundary : Type) [Fintype boundary]
    (rawObserver : TranscriptObserver rawTranscript)
    (project : rawTranscript -> boundary)
    (fam : FoolingResidualFamily m)
    (decode : boundary -> Assignment m)
    (hpoly : Fintype.card boundary <= m ^ k)
    (hgap : m ^ k < 2 ^ m) :
    ¬ (forall a : Assignment m,
        decode (project (rawObserver (fam.instanceOf a))) = fam.label a) := by
  intro hdecode
  have hsound : SoundOnFoolingFamily (fun x => project (rawObserver x)) fam := by
    intro a b heq
    change project (rawObserver (fam.instanceOf a)) =
      project (rawObserver (fam.instanceOf b)) at heq
    have ha := hdecode a
    have hb := hdecode b
    rw [heq] at ha
    exact ha.symm.trans hb
  exact transcript_fooling_contradicts_poly_boundary
    (fun x => project (rawObserver x)) fam hsound hpoly hgap

/-- Convert a correctness-derived decoder into the earlier structured extraction once a decider correctness proof is
available.  This is the safe direction: preservation is derived first, then packaged. -/
def toStructured
    (E : CorrectnessDerivedLabelDecoderFor U D) (hD : DecidesSAT U D) :
    StructuredDynamicH4ExtractionFor U D hD where
  m := E.m
  k := E.k
  rawTranscript := E.rawTranscript
  boundary := E.boundary
  fintypeBoundary := E.fintypeBoundary
  rawObserver := E.rawObserver
  project := E.project
  fam := E.fam
  preserves := E.sound_of_decode_correct hD
  polyBoundary := E.polyBoundary
  expGap := E.expGap

end CorrectnessDerivedLabelDecoderFor

/-- Final non-vacuous theorem target, stated as an extraction principle.

For every polynomial-time SAT decision machine `D`, construct a projected boundary and a decoder such that SAT correctness
of `D` would recover exponentially many hard residual labels from polynomially many boundary cells.

The actual hard mathematical obligation is inside `decode_correct_of_decides`: derive label recovery from `DecidesSAT U D`
for a genuine NP-complete residual family. -/
abbrev CorrectnessDerivedLabelDecodersForAllMachines (U : MachineModel) : Type 1 :=
  forall D : DecisionMachine U, CorrectnessDerivedLabelDecoderFor U D

/-- Cash-out of the final theorem shape: if every claimed SAT decider admits such a correctness-derived decoder, then SAT
has no polynomial-time decider in this machine model. -/
theorem no_SATDecisionInP_of_correctnessDerivedLabelDecoders {U : MachineModel}
    (hFinal : CorrectnessDerivedLabelDecodersForAllMachines U) :
    ¬ SATDecisionInP U := by
  intro hP
  rcases hP with ⟨D, hD⟩
  exact (hFinal D).not_decidesSAT hD

/-- Same cash-out through the previous structured-H4 interface. -/
theorem no_SATDecisionInP_via_structured_of_correctnessDerivedLabelDecoders {U : MachineModel}
    (hFinal : CorrectnessDerivedLabelDecodersForAllMachines U) :
    ¬ SATDecisionInP U := by
  intro hP
  rcases hP with ⟨D, hD⟩
  exact (hFinal D).toStructured hD |>.impossible

/-!
Final theorem checklist after this file:

1. Pick a genuine NP-complete residual fooling family, not an easy linear family such as bare Tseitin.
2. For an arbitrary claimed P-time SAT decider `D`, define the operational transcript observer and polynomial projection.
3. Prove `decode_correct_of_decides`: if `D` is SAT-correct, the projected boundary decodes the residual labels.
4. Prove the polynomial boundary bound and open the exponential gap.

Then `no_SATDecisionInP_of_correctnessDerivedLabelDecoders` gives the lower bound.  If step 3 cannot be proved, the route
has not escaped the known barrier; if it is proved for an easy family, the statement is false or the boundary is
exponential.
-/

end PallLean.Paper93.DeepMath.PathB.PvsNPFinalDecoderTheorem

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPFinalDecoderTheorem.CorrectnessDerivedLabelDecoderFor.sound_of_decode_correct
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPFinalDecoderTheorem.CorrectnessDerivedLabelDecoderFor.not_decidesSAT
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPFinalDecoderTheorem.CorrectnessDerivedLabelDecoderFor.decoder_correctness_is_the_final_gap
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPFinalDecoderTheorem.CorrectnessDerivedLabelDecoderFor.toStructured
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPFinalDecoderTheorem.no_SATDecisionInP_of_correctnessDerivedLabelDecoders
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPFinalDecoderTheorem.no_SATDecisionInP_via_structured_of_correctnessDerivedLabelDecoders
