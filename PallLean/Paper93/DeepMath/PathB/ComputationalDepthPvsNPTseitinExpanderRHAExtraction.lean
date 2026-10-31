import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPRamanujanHolographicAmplituhedronExtraction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderTseitinInstance

/-!
# Tseitin-expander specialization of the Ramanujan/holographic/amplituhedron extraction

The previous file identified the geometric extraction theorem:

```text
Ramanujan boundary -> holographic screen -> amplituhedron positive cells -> structured H4 extraction.
```

This file makes the intended hard residual family more concrete: **Tseitin residuals on expander/Ramanujan graphs**.
The existing file `ComputationalDepthExpanderTseitinWidthKernel.lean` already proves the real combinatorial lever:

```lean
support_combination_eq_boundary
combination_support_card_ge_of_expansion
```

so expansion is not just decoration.  It gives a width/no-hiding certificate for Tseitin constraint combinations.

What remains, now stated sharply, is the dynamic/P-vs-NP bridge:

```text
Tseitin expander residual labels are preserved by the composed
Ramanujan -> holographic -> amplituhedron positive-cell projection
for every claimed polynomial-time SAT decider.
```

If that preservation theorem is supplied with polynomially many positive cells and an exponential gap, the existing chain
rules out `SATDecisionInP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsNPTseitinExpanderRHAExtraction

open SATDepthMachine
open Finset
open PallLean.Paper93.DeepMath.PathB.PvsNPTranscriptObserver
open PallLean.Paper93.DeepMath.PathB.PvsNPRamanujanHolographicAmplituhedronExtraction

/-- A Tseitin expander certificate packaged as the hard-family source.

The graph is fully typed internally and carries a genuine `HasExpansion c` proof.  Future work can replace this with a
formal infinite Ramanujan family; the downstream extraction/cash-out theorem will not change. -/
structure TseitinExpanderCertificate where
  V : Type
  Edge : Type
  fintypeV : Fintype V
  decidableEqV : DecidableEq V
  fintypeEdge : Fintype Edge
  decidableEqEdge : DecidableEq Edge
  c : Nat
  graph : @TseitinGraph V Edge fintypeV decidableEqV fintypeEdge decidableEqEdge
  expansion : @TseitinGraph.HasExpansion V Edge fintypeV decidableEqV fintypeEdge decidableEqEdge graph c

namespace TseitinExpanderCertificate

instance instFintypeV (T : TseitinExpanderCertificate) : Fintype T.V := T.fintypeV
instance instDecidableEqV (T : TseitinExpanderCertificate) : DecidableEq T.V := T.decidableEqV
instance instFintypeEdge (T : TseitinExpanderCertificate) : Fintype T.Edge := T.fintypeEdge
instance instDecidableEqEdge (T : TseitinExpanderCertificate) : DecidableEq T.Edge := T.decidableEqEdge

/-- Convert a Tseitin expander certificate into the lightweight Ramanujan boundary certificate used by the RHA socket. -/
def toRamanujanBoundaryCertificate (T : TseitinExpanderCertificate) : RamanujanBoundaryCertificate where
  vertices := Fintype.card T.V
  degree := T.c
  spectralSlack := T.c
  expansionPayload :=
    @TseitinGraph.HasExpansion T.V T.Edge T.fintypeV T.decidableEqV T.fintypeEdge T.decidableEqEdge
      T.graph T.c
  expansion_realized := T.expansion

/-- The existing Tseitin width kernel, specialized to the certified expander. -/
theorem combination_width
    (T : TseitinExpanderCertificate) (S : Finset T.V)
    (h1 : 1 <= S.card) (h2 : 2 * S.card <= Fintype.card T.V) :
    T.c * S.card <= (edgeSupport (T.graph.combination S)).card := by
  exact T.graph.combination_support_card_ge_of_expansion T.expansion S h1 h2

/-- With expansion at least one, every medium nonempty vertex combination has a surviving edge: no medium combination can
hide completely. -/
theorem exists_surviving_edge_of_medium_combination
    (T : TseitinExpanderCertificate) (hc : 1 <= T.c) (S : Finset T.V)
    (h1 : 1 <= S.card) (h2 : 2 * S.card <= Fintype.card T.V) :
    exists e : T.Edge, T.graph.combination S e ≠ 0 := by
  exact T.graph.exists_combination_ne_zero_of_expansion hc T.expansion S h1 h2

end TseitinExpanderCertificate

/-- Non-vacuity sanity check: the already-proved `K4` expander gives a concrete Tseitin certificate.

This is not asymptotic and not P-vs-NP; it proves the certificate type is inhabited by a real graph with proved expansion. -/
def K4_tseitinExpanderCertificate : TseitinExpanderCertificate where
  V := Fin 4
  Edge := Fin 6
  fintypeV := inferInstance
  decidableEqV := inferInstance
  fintypeEdge := inferInstance
  decidableEqEdge := inferInstance
  c := 2
  graph := K4
  expansion := K4_hasExpansion

/-- A Tseitin-expander residual family: a dynamic-H4 fooling family together with a certificate that it is the residual
family induced by the Tseitin expander source.

`residualPayload` is intentionally a `Prop` field rather than an assumed theorem about SAT hardness.  The point is to name
what a future concrete CNF construction must prove: the abstract `FoolingResidualFamily` really comes from the Tseitin
expander constraints/residual branches. -/
structure TseitinExpanderResidualFamily (m : Nat) where
  certificate : TseitinExpanderCertificate
  fam : FoolingResidualFamily m
  residualPayload : Prop
  residual_realized : residualPayload

/-- Full Tseitin-specialized RHA extraction for one claimed SAT decider.

Compared with the generic RHA extraction, this object forces the fooling family to come from a certified Tseitin expander
source and forces the holographic stage's Ramanujan certificate to be the one induced by that source. -/
structure TseitinExpanderRHAExtractionFor
    (U : MachineModel) (D : DecisionMachine U) (hD : DecidesSAT U D) where
  m : Nat
  k : Nat
  rawTranscript : Type
  holographicScreen : Type
  positiveCellType : Type
  fintypePositiveCell : Fintype positiveCellType
  rawObserver : TranscriptObserver rawTranscript
  tseitinFamily : TseitinExpanderResidualFamily m
  projectToScreen : rawTranscript -> holographicScreen
  boundary_respects_tseitin_expander : Prop
  boundary_respects_tseitin_expander_realized : boundary_respects_tseitin_expander
  amplituhedron : AmplituhedronPositiveCellStage holographicScreen positiveCellType
  preservesTseitinLabels :
    SoundOnFoolingFamily
      (fun x =>
        amplituhedron.projectToCell (projectToScreen (rawObserver x)))
      tseitinFamily.fam
  polyPositiveCells : @Fintype.card positiveCellType fintypePositiveCell <= m ^ k
  expGap : m ^ k < 2 ^ m

namespace TseitinExpanderRHAExtractionFor

variable {U : MachineModel} {D : DecisionMachine U} {hD : DecidesSAT U D}

/-- The holographic stage induced by the Tseitin expander certificate. -/
def holographic (E : TseitinExpanderRHAExtractionFor U D hD) :
    HolographicProjectionStage E.rawTranscript E.holographicScreen where
  ramanujan := E.tseitinFamily.certificate.toRamanujanBoundaryCertificate
  projectToScreen := E.projectToScreen
  boundary_respects_expander := E.boundary_respects_tseitin_expander
  boundary_respects_expander_realized := E.boundary_respects_tseitin_expander_realized

/-- Forget the Tseitin-specific fields to the generic RHA extraction interface. -/
def toRHA (E : TseitinExpanderRHAExtractionFor U D hD) :
    RamanujanHolographicAmplituhedronExtractionFor U D hD where
  m := E.m
  k := E.k
  rawTranscript := E.rawTranscript
  holographicScreen := E.holographicScreen
  positiveCellType := E.positiveCellType
  fintypePositiveCell := E.fintypePositiveCell
  rawObserver := E.rawObserver
  holographic := E.holographic
  amplituhedron := E.amplituhedron
  fam := E.tseitinFamily.fam
  preservesLabels := E.preservesTseitinLabels
  polyPositiveCells := E.polyPositiveCells
  expGap := E.expGap

/-- Therefore a full Tseitin-expander RHA extraction is impossible below the exponential gap. -/
theorem impossible (E : TseitinExpanderRHAExtractionFor U D hD) : False := by
  exact E.toRHA.impossible

/-- Diagnostic: even with a certified Tseitin expander source, polynomial positive cells cannot preserve all Tseitin
residual labels below the exponential gap.  Thus `preservesTseitinLabels` is the exact frontier. -/
theorem tseitin_label_preservation_is_the_gap
    (m k : Nat)
    (raw screen cell : Type) [Fintype cell]
    (rawObserver : TranscriptObserver raw)
    (family : TseitinExpanderResidualFamily m)
    (projectToScreen : raw -> screen)
    (A : AmplituhedronPositiveCellStage screen cell)
    (hpoly : Fintype.card cell <= m ^ k)
    (hgap : m ^ k < 2 ^ m) :
    ¬ SoundOnFoolingFamily
      (fun x => A.projectToCell (projectToScreen (rawObserver x))) family.fam := by
  let H : HolographicProjectionStage raw screen := {
    ramanujan := family.certificate.toRamanujanBoundaryCertificate
    projectToScreen := projectToScreen
    boundary_respects_expander := family.residualPayload
    boundary_respects_expander_realized := family.residual_realized
  }
  exact RamanujanHolographicAmplituhedronExtractionFor.preservation_is_still_the_gap
    m k raw screen cell rawObserver H A family.fam hpoly hgap

end TseitinExpanderRHAExtractionFor

/-- The final Tseitin-expander/RHA theorem object: every claimed polynomial-time SAT decider admits the factored
Tseitin-expander extraction. -/
abbrev TseitinExpanderRHAForPTimeSAT (U : MachineModel) : Type 1 :=
  forall (D : DecisionMachine U) (hD : DecidesSAT U D),
    TseitinExpanderRHAExtractionFor U D hD

/-- A Tseitin-expander RHA theorem implies the generic Ramanujan/holographic/amplituhedron theorem. -/
def RHA_of_TseitinExpanderRHA {U : MachineModel}
    (hT : TseitinExpanderRHAForPTimeSAT U) :
    RamanujanHolographicAmplituhedronForPTimeSAT U := by
  intro D hD
  exact (hT D hD).toRHA

/-- Cash-out: a Tseitin-expander/RHA extraction theorem rules out polynomial-time SAT decision. -/
theorem no_SATDecisionInP_of_TseitinExpanderRHA {U : MachineModel}
    (hT : TseitinExpanderRHAForPTimeSAT U) :
    ¬ SATDecisionInP U := by
  exact no_SATDecisionInP_of_RamanujanHolographicAmplituhedron
    (RHA_of_TseitinExpanderRHA hT)

/-- Direct cash-out. -/
theorem no_SATDecisionInP_of_TseitinExpanderRHA_direct {U : MachineModel}
    (hT : TseitinExpanderRHAForPTimeSAT U) :
    ¬ SATDecisionInP U := by
  intro hP
  rcases hP with ⟨D, hD⟩
  exact (hT D hD).impossible

/-!
Current exact frontier:

```lean
TseitinExpanderRHAForPTimeSAT U
```

To prove P-vs-NP by this route, instantiate `TseitinExpanderRHAExtractionFor` for every claimed SAT decider.  The hard
field is now named concretely:

```lean
preservesTseitinLabels
```

That is: the composed projection

```text
raw transcript -> holographic screen -> amplituhedron positive cell
```

must not merge distinct labels of the Tseitin-expander residual fooling family, while the positive-cell type remains
polynomially bounded.
-/

end PallLean.Paper93.DeepMath.PathB.PvsNPTseitinExpanderRHAExtraction

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPTseitinExpanderRHAExtraction.TseitinExpanderCertificate.toRamanujanBoundaryCertificate
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPTseitinExpanderRHAExtraction.TseitinExpanderCertificate.combination_width
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPTseitinExpanderRHAExtraction.TseitinExpanderCertificate.exists_surviving_edge_of_medium_combination
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPTseitinExpanderRHAExtraction.K4_tseitinExpanderCertificate
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPTseitinExpanderRHAExtraction.TseitinExpanderRHAExtractionFor.toRHA
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPTseitinExpanderRHAExtraction.TseitinExpanderRHAExtractionFor.impossible
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPTseitinExpanderRHAExtraction.TseitinExpanderRHAExtractionFor.tseitin_label_preservation_is_the_gap
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPTseitinExpanderRHAExtraction.RHA_of_TseitinExpanderRHA
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPTseitinExpanderRHAExtraction.no_SATDecisionInP_of_TseitinExpanderRHA
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPTseitinExpanderRHAExtraction.no_SATDecisionInP_of_TseitinExpanderRHA_direct
