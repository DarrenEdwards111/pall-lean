import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPFinalDecoderTheorem

/-!
# Hard SAT residual family target

`ComputationalDepthPvsNPFinalDecoderTheorem.lean` isolated the right final theorem shape:

```text
SAT-correctness of D -> projected boundary decodes hard residual labels.
```

This file names the next concrete objects needed to attack that theorem without falling back into the vacuous
`preservesLabels` socket.

The central point is that the hard residual family must be **semantic and NP-complete/search-complete**, not an easy linear
family such as bare Tseitin.  The label decoder has to be derived from the correctness of an arbitrary claimed SAT decider.

The file is intentionally an interface/cash-out layer, not a fake proof of P-vs-NP.  The live theorem is exposed as
`decode_correct_of_decides_for_hard_residuals` inside `HardResidualDecoderExtractionFor`.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsNPHardResidualFamily

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPObserverSwitchToy
open PallLean.Paper93.DeepMath.PathB.PvsNPTranscriptObserver
open PallLean.Paper93.DeepMath.PathB.PvsNPFinalDecoderTheorem

/-- A semantic hard SAT residual family.

`fam` is the existing fooling-family object: it provides `2^m` indexed residual instances and injective semantic labels.
The extra fields below prevent the family from being just syntactic decoration:

* `residual_semantics` names the intended construction from real SAT/search residuals;
* `np_complete_payload` names the NP-completeness/search-completeness argument;
* `not_easy_linear_payload` is a fence excluding the bare-Tseitin mistake: the labels must not be recoverable by an easy
  global algebraic shortcut unrelated to general SAT search.

These payloads are `Prop`-level sockets because the next mathematical work is to replace them with concrete Cook-Levin /
search-verifier constructions and prove them. -/
structure HardSATResidualFamily (m : Nat) where
  fam : FoolingResidualFamily m
  residual_semantics : Prop
  residual_semantics_realized : residual_semantics
  np_complete_payload : Prop
  np_complete_realized : np_complete_payload
  not_easy_linear_payload : Prop
  not_easy_linear_realized : not_easy_linear_payload

namespace HardSATResidualFamily

/-- Forget the hardness annotations to the underlying fooling residual family. -/
def toFoolingFamily {m : Nat} (H : HardSATResidualFamily m) : FoolingResidualFamily m :=
  H.fam

/-- The hard labels are injective because the underlying fooling family labels are injective. -/
theorem label_injective {m : Nat} (H : HardSATResidualFamily m) :
    Function.Injective H.fam.label :=
  H.fam.label_injective

end HardSATResidualFamily

/-- The operational transcript/projection surface induced by one claimed SAT decider.

This structure is deliberately separate from preservation/decoding.  It only says what we observe about the alleged
solver and how we compress it.  The polynomial bound is a P-side statement; it should ultimately follow from the runtime
budget of `D` and the definition of `project`.
-/
structure SolverTranscriptProjectionFor
    (U : MachineModel) (D : DecisionMachine U) (m : Nat) where
  k : Nat
  rawTranscript : Type
  boundary : Type
  fintypeBoundary : Fintype boundary
  rawObserver : TranscriptObserver rawTranscript
  project : rawTranscript -> boundary
  polyBoundary : @Fintype.card boundary fintypeBoundary <= m ^ k
  expGap : m ^ k < 2 ^ m

namespace SolverTranscriptProjectionFor

/-- The projected residual observer. -/
def projectedObserver {U : MachineModel} {D : DecisionMachine U} {m : Nat}
    (P : SolverTranscriptProjectionFor U D m) : TranscriptObserver P.boundary :=
  fun x => P.project (P.rawObserver x)

end SolverTranscriptProjectionFor

/-- The genuinely load-bearing extraction for one claimed SAT decider.

Unlike the earlier RHA/Tseitin sockets, this does not assume `SoundOnFoolingFamily` or `preservesLabels`.  It asks for a
label decoder and the theorem deriving decoder correctness from `DecidesSAT U D`.

This is the exact next hard theorem:

```lean
decode_correct_of_decides_for_hard_residuals
```

For a real proof, it must be proved from the operational behavior/correctness of `D` on a concrete NP-complete residual
family. -/
structure HardResidualDecoderExtractionFor
    (U : MachineModel) (D : DecisionMachine U) where
  m : Nat
  hardFamily : HardSATResidualFamily m
  projection : SolverTranscriptProjectionFor U D m
  decode : projection.boundary -> Assignment m
  decode_correct_of_decides_for_hard_residuals :
    DecidesSAT U D ->
      forall a : Assignment m,
        decode (projection.project (projection.rawObserver (hardFamily.fam.instanceOf a))) =
          hardFamily.fam.label a

namespace HardResidualDecoderExtractionFor

variable {U : MachineModel} {D : DecisionMachine U}

/-- Convert the hard-residual extraction into the final decoder theorem interface. -/
def toCorrectnessDerivedLabelDecoder
    (E : HardResidualDecoderExtractionFor U D) :
    CorrectnessDerivedLabelDecoderFor U D where
  m := E.m
  k := E.projection.k
  rawTranscript := E.projection.rawTranscript
  boundary := E.projection.boundary
  fintypeBoundary := E.projection.fintypeBoundary
  rawObserver := E.projection.rawObserver
  project := E.projection.project
  fam := E.hardFamily.fam
  decode := E.decode
  decode_correct_of_decides := E.decode_correct_of_decides_for_hard_residuals
  polyBoundary := E.projection.polyBoundary
  expGap := E.projection.expGap

/-- Decoder correctness derived from SAT correctness gives projected soundness on the hard residual family. -/
theorem sound_of_decides
    (E : HardResidualDecoderExtractionFor U D) (hD : DecidesSAT U D) :
    SoundOnFoolingFamily
      (fun x => E.projection.project (E.projection.rawObserver x))
      E.hardFamily.fam := by
  exact E.toCorrectnessDerivedLabelDecoder.sound_of_decode_correct hD

/-- Any full hard-residual decoder extraction contradicts correctness of `D`. -/
theorem not_decidesSAT
    (E : HardResidualDecoderExtractionFor U D) :
    ¬ DecidesSAT U D := by
  exact E.toCorrectnessDerivedLabelDecoder.not_decidesSAT

/-- Direct pigeonhole form of the hard-residual contradiction. -/
theorem contradiction_of_decides
    (E : HardResidualDecoderExtractionFor U D) (hD : DecidesSAT U D) : False := by
  exact E.not_decidesSAT hD

end HardResidualDecoderExtractionFor

/-- The next major theorem target: every claimed polynomial-time SAT decider yields a hard-residual decoder extraction.

This is the non-vacuous P-vs-NP target now.  It says more than “there exists an impossible preserving projection”: it says
that for each concrete decider, a semantic NP-complete residual family and a polynomial projection can be built such that
SAT correctness forces label decoding.
-/
abbrev HardResidualDecoderExtractionForAllMachines (U : MachineModel) : Type 1 :=
  forall D : DecisionMachine U, HardResidualDecoderExtractionFor U D

/-- Cash-out: the hard-residual decoder theorem rules out polynomial-time SAT decision. -/
theorem no_SATDecisionInP_of_hardResidualDecoderExtraction {U : MachineModel}
    (hHard : HardResidualDecoderExtractionForAllMachines U) :
    ¬ SATDecisionInP U := by
  intro hP
  rcases hP with ⟨D, hD⟩
  exact (hHard D).not_decidesSAT hD

/-- Same cash-out routed through the final decoder theorem. -/
theorem no_SATDecisionInP_via_finalDecoder_of_hardResidualDecoderExtraction {U : MachineModel}
    (hHard : HardResidualDecoderExtractionForAllMachines U) :
    ¬ SATDecisionInP U := by
  exact no_SATDecisionInP_of_correctnessDerivedLabelDecoders
    (fun D => (hHard D).toCorrectnessDerivedLabelDecoder)

/-!
Concrete next obligations after this file:

1. Replace `HardSATResidualFamily` payloads by a real Cook-Levin/search-verifier residual construction.
2. Prove the family labels are semantic witness/search labels, not syntactic artifacts.
3. Define `SolverTranscriptProjectionFor` from an arbitrary claimed polynomial-time SAT decider `D`.
4. Prove the polynomial boundary bound from the machine budget.
5. Prove `decode_correct_of_decides_for_hard_residuals` from `DecidesSAT U D`.

Step 5 is the actual P-vs-NP core.  If it is proved with a genuinely NP-complete residual family and polynomial boundary,
the cash-out above gives `¬ SATDecisionInP U`.
-/

end PallLean.Paper93.DeepMath.PathB.PvsNPHardResidualFamily

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPHardResidualFamily.HardSATResidualFamily.label_injective
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPHardResidualFamily.HardResidualDecoderExtractionFor.toCorrectnessDerivedLabelDecoder
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPHardResidualFamily.HardResidualDecoderExtractionFor.sound_of_decides
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPHardResidualFamily.HardResidualDecoderExtractionFor.not_decidesSAT
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPHardResidualFamily.HardResidualDecoderExtractionFor.contradiction_of_decides
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPHardResidualFamily.no_SATDecisionInP_of_hardResidualDecoderExtraction
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPHardResidualFamily.no_SATDecisionInP_via_finalDecoder_of_hardResidualDecoderExtraction
