import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPStructuredExtraction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDecisionHolonomy
import Mathlib.Data.Fintype.Pi

/-!
# Ramanujan → holographic projection → amplituhedron extraction socket

Darren's proposed refinement is the right non-circular shape:

```text
Ramanujan expander / spectral boundary
    -> holographic projection of solver transcripts
    -> amplituhedron / positive-cell boundary
    -> structured dynamic-H4 extraction
    -> SAT ∉ P
```

This file formalizes that pipeline for the dynamic-H4 P-vs-NP route.  It deliberately does **not** pretend to construct
Ramanujan graphs or amplituhedron cells.  Instead, it names the exact certificate that would link them to the already
proved structured extraction theorem.

The hard field remains visible:

```lean
preservesLabels
```

It says that equality of the final positive cells cannot merge different hard residual/search labels.  The theorem
`preservation_is_still_the_gap` proves that, once the positive-cell boundary is polynomially bounded below the
exponential gap, this preservation field is exactly where the contradiction lives.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsNPRamanujanHolographicAmplituhedronExtraction

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPTranscriptObserver
open PallLean.Paper93.DeepMath.PathB.PvsNPStructuredExtraction
open PallLean.Paper93.DeepMath.PathB.PvsNPPACAmplituhedronProjection
open PallLean.Paper93.DeepMath.PathB.DecisionHolonomy

/-- Abstract Ramanujan/expander boundary certificate for the H4 extraction route.

The numerical fields are intentionally lightweight handles.  The real future implementation can refine them to a concrete
spectral graph, two-sided expander, or Ramanujan complex without changing the downstream cash-out theorems. -/
structure RamanujanBoundaryCertificate where
  vertices : Nat
  degree : Nat
  spectralSlack : Nat
  expansionPayload : Prop
  expansion_realized : expansionPayload

/-- A holographic projection stage: raw solver transcript/state data is projected to boundary-screen data.

`boundary_respects_expander` is the place where the Ramanujan certificate is meant to constrain the screen. -/
structure HolographicProjectionStage (raw screen : Type) where
  ramanujan : RamanujanBoundaryCertificate
  projectToScreen : raw -> screen
  boundary_respects_expander : Prop
  boundary_respects_expander_realized : boundary_respects_expander

/-- An amplituhedron/positive-cell stage: holographic screen data is mapped to positive boundary cells. -/
structure AmplituhedronPositiveCellStage (screen cell : Type) where
  projectToCell : screen -> cell
  positiveCell : cell -> Prop
  project_positive : forall s : screen, positiveCell (projectToCell s)
  orientationPayload : Prop
  orientation_realized : orientationPayload

/-- The composed Ramanujan-holographic-amplituhedron projection from raw transcript states to positive cells. -/
def composedPositiveProjection {raw screen cell : Type}
    (H : HolographicProjectionStage raw screen)
    (A : AmplituhedronPositiveCellStage screen cell) : raw -> cell :=
  fun r => A.projectToCell (H.projectToScreen r)

/-- The composed projection as the PAC/amplituhedron interface used by the existing dynamic-H4 machinery. -/
def toPACProjection {raw screen cell : Type}
    (H : HolographicProjectionStage raw screen)
    (A : AmplituhedronPositiveCellStage screen cell) :
    PACAmplituhedronProjection raw cell where
  project := composedPositiveProjection H A
  positiveCell := A.positiveCell
  project_positive := by
    intro r
    exact A.project_positive (H.projectToScreen r)

/-- A full geometric extraction for one claimed SAT decider.

This is the proposed solution-shaped theorem object.  It explicitly factors the structured extraction through:

1. a Ramanujan/expander boundary certificate;
2. a holographic projection to screen variables;
3. an amplituhedron positive-cell projection;
4. fooling-label preservation on the final cells;
5. polynomial positive-cell count and exponential gap.
-/
structure RamanujanHolographicAmplituhedronExtractionFor
    (U : MachineModel) (D : DecisionMachine U) (hD : DecidesSAT U D) where
  m : Nat
  k : Nat
  rawTranscript : Type
  holographicScreen : Type
  positiveCellType : Type
  fintypePositiveCell : Fintype positiveCellType
  rawObserver : TranscriptObserver rawTranscript
  holographic : HolographicProjectionStage rawTranscript holographicScreen
  amplituhedron : AmplituhedronPositiveCellStage holographicScreen positiveCellType
  fam : FoolingResidualFamily m
  preservesLabels :
    SoundOnFoolingFamily
      (fun x => composedPositiveProjection holographic amplituhedron (rawObserver x))
      fam
  polyPositiveCells : @Fintype.card positiveCellType fintypePositiveCell <= m ^ k
  expGap : m ^ k < 2 ^ m

namespace RamanujanHolographicAmplituhedronExtractionFor

variable {U : MachineModel} {D : DecisionMachine U} {hD : DecidesSAT U D}

/-- Convert the geometric pipeline into the structured dynamic-H4 extraction interface. -/
def toStructured (E : RamanujanHolographicAmplituhedronExtractionFor U D hD) :
    StructuredDynamicH4ExtractionFor U D hD where
  m := E.m
  k := E.k
  rawTranscript := E.rawTranscript
  boundary := E.positiveCellType
  fintypeBoundary := E.fintypePositiveCell
  rawObserver := E.rawObserver
  project := composedPositiveProjection E.holographic E.amplituhedron
  positiveCell := E.amplituhedron.positiveCell
  project_positive := by
    intro r
    exact E.amplituhedron.project_positive (E.holographic.projectToScreen r)
  fam := E.fam
  preserves := E.preservesLabels
  polyBoundary := E.polyPositiveCells
  expGap := E.expGap

/-- Convert directly to the PAC/amplituhedron projection interface. -/
def toPAC (E : RamanujanHolographicAmplituhedronExtractionFor U D hD) :
    PACAmplituhedronProjection E.rawTranscript E.positiveCellType :=
  toPACProjection E.holographic E.amplituhedron

/-- A full Ramanujan-holographic-amplituhedron extraction is impossible, by the structured H4 lower-bound theorem. -/
theorem impossible (E : RamanujanHolographicAmplituhedronExtractionFor U D hD) : False := by
  exact E.toStructured.impossible

/-- Same contradiction through the PAC positive-cell projection theorem. -/
theorem impossible_via_positive_cells
    (E : RamanujanHolographicAmplituhedronExtractionFor U D hD) : False := by
  letI : Fintype E.positiveCellType := E.fintypePositiveCell
  exact PAC_projection_contradicts_poly_boundary
    E.toPAC E.rawObserver E.fam E.preservesLabels E.polyPositiveCells E.expGap

/-- Diagnostic theorem: even with Ramanujan and holographic payloads realized, polynomially many positive cells below the
exponential gap cannot preserve all fooling labels.

So the future mathematical theorem must explain why the geometry gives preservation on a genuinely hard residual family;
that is the whole live content. -/
theorem preservation_is_still_the_gap
    (m k : Nat)
    (raw screen cell : Type) [Fintype cell]
    (rawObserver : TranscriptObserver raw)
    (H : HolographicProjectionStage raw screen)
    (A : AmplituhedronPositiveCellStage screen cell)
    (fam : FoolingResidualFamily m)
    (hpoly : Fintype.card cell <= m ^ k)
    (hgap : m ^ k < 2 ^ m) :
    ¬ SoundOnFoolingFamily
      (fun x => composedPositiveProjection H A (rawObserver x)) fam := by
  exact StructuredDynamicH4ExtractionFor.preservation_is_the_only_gap
    m k raw cell rawObserver (composedPositiveProjection H A) A.positiveCell
    (by intro r; exact A.project_positive (H.projectToScreen r)) fam hpoly hgap

end RamanujanHolographicAmplituhedronExtractionFor

/-- The global geometric extraction theorem: every claimed polynomial-time SAT decider admits the factored
Ramanujan/holographic/amplituhedron extraction. -/
abbrev RamanujanHolographicAmplituhedronForPTimeSAT (U : MachineModel) : Type 1 :=
  forall (D : DecisionMachine U) (hD : DecidesSAT U D),
    RamanujanHolographicAmplituhedronExtractionFor U D hD

/-- The geometric extraction theorem implies the structured dynamic-H4 extraction theorem. -/
def structuredDynamicH4_of_RamanujanHolographicAmplituhedron {U : MachineModel}
    (hGeom : RamanujanHolographicAmplituhedronForPTimeSAT U) :
    StructuredDynamicH4ForPTimeSAT U := by
  intro D hD
  exact (hGeom D hD).toStructured

/-- Cash-out: the Ramanujan/holographic/amplituhedron extraction theorem rules out polynomial-time SAT decision. -/
theorem no_SATDecisionInP_of_RamanujanHolographicAmplituhedron {U : MachineModel}
    (hGeom : RamanujanHolographicAmplituhedronForPTimeSAT U) :
    ¬ SATDecisionInP U := by
  exact no_SATDecisionInP_of_structuredDynamicH4
    (structuredDynamicH4_of_RamanujanHolographicAmplituhedron hGeom)

/-- Direct cash-out: instantiate the geometric extraction on the alleged decider and contradict the positive-cell lower
bound. -/
theorem no_SATDecisionInP_of_RamanujanHolographicAmplituhedron_direct {U : MachineModel}
    (hGeom : RamanujanHolographicAmplituhedronForPTimeSAT U) :
    ¬ SATDecisionInP U := by
  intro hP
  rcases hP with ⟨D, hD⟩
  exact (hGeom D hD).impossible

/-! ## Complete holographic/N-frame bridge surface

The geometric extraction above already exposes finite capacity and hard-label
preservation.  To prevent the phrase "holographic projection + N-frame
Lagrangian" from hiding the remaining mathematics, the structure below records
all four requirements of a genuine completion certificate in one place:

1. small finite computational capacity;
2. preservation/injectivity on the hard SAT residual family;
3. efficient encoding and decoding extracted from the alleged solver;
4. compatibility with SPDP rank and the Cook--Levin/PAC compilation.

The N-frame Lagrangian is included as construction data, not as a proof of the
four requirements.  In particular, minimisation of an action does not by itself
imply label preservation or rank faithfulness.
-/

/-- Solver-derived efficient encoder/decoder payload.

The concrete implementation is intentionally left abstract here: it must bind
the screen/cell maps to the actual execution of `D`, and prove polynomial cost
for both directions used by the reduction. -/
structure EfficientHolographicEncodingDecodingPayload
    (U : MachineModel) (D : DecisionMachine U) (hD : DecidesSAT U D)
    (raw screen cell : Type) where
  descriptionBits : Nat -> Nat
  finitePrecisionBits : Nat -> Nat
  updateCount : Nat -> Nat
  encodingCost : Nat -> Nat
  decodingCost : Nat -> Nat
  descriptionBits_poly : PolyBounded descriptionBits
  finitePrecisionBits_poly : PolyBounded finitePrecisionBits
  updateCount_poly : PolyBounded updateCount
  encodingCost_poly : PolyBounded encodingCost
  decodingCost_poly : PolyBounded decodingCost
  derivedFromSolver : Prop
  derivedFromSolver_realized : derivedFromSolver

/-- SPDP/PAC and Cook--Levin compatibility payload.

A realization must prove the rank-faithful direction on the relevant hard
derivative space; ordinary projection monotonicity alone is insufficient. -/
structure SPDPCookLevinRankFaithfulCompatibilityPayload
    (raw screen cell : Type) where
  operationCompatibility : Prop
  operationCompatibility_realized : operationCompatibility
  cookLevinTargetCompatibility : Prop
  cookLevinTargetCompatibility_realized : cookLevinTargetCompatibility
  hardResidualKernelTrivial : Prop
  hardResidualKernelTrivial_realized : hardResidualKernelTrivial
  spdpRankFaithful : Prop
  spdpRankFaithful_realized : spdpRankFaithful

/-- N-frame Lagrangian construction payload for the selected holographic map.

This field certifies that the projection really arises from the intended
N-frame variational construction.  It is deliberately separate from semantic
preservation and SPDP rank faithfulness. -/
structure NFrameLagrangianProjectionPayload (raw screen cell : Type) where
  isNFrameLagrangianMinimizer : Prop
  isNFrameLagrangianMinimizer_realized : isNFrameLagrangianMinimizer
  minimizerInducesHolographicProjection : Prop
  minimizerInducesHolographicProjection_realized :
    minimizerInducesHolographicProjection
  unitAndIdentityMinorPreserving : Prop
  unitAndIdentityMinorPreserving_realized : unitAndIdentityMinorPreserving

/-- Polynomial capacity with an explicit coefficient and degree.  This form is
closed under finite sums without hiding the number of observer charts. -/
def AtlasPolyBounded (f : Nat -> Nat) : Prop :=
  ∃ c k, ∀ n, f n ≤ c * (n + 1) ^ k

/-- A finite atlas of observer perspectives with genuinely different boundary
interfaces.

Each perspective may expose different information about the same raw solver
state.  The capacity accounting is global: `totalCapacityBits` must include all
charts and the information needed to select/transition between them.  This
prevents an exponential family of individually tiny observers from being called
a polynomial-capacity observer. -/
structure HolographicObserverPerspectiveAtlas (raw : Type) where
  Perspective : Type
  perspectiveFintype : Fintype Perspective
  Boundary : Perspective -> Type
  boundaryFintype : ∀ i, Fintype (Boundary i)
  ObservableInterface : Perspective -> Type
  view : ∀ i, raw -> Boundary i
  observe : ∀ i, Boundary i -> ObservableInterface i
  capacityBits : Perspective -> Nat -> Nat
  capacityBits_poly : ∀ i, AtlasPolyBounded (capacityBits i)
  totalCapacityBits : Nat -> Nat
  totalCapacityBits_eq_sum :
    ∀ n, totalCapacityBits n = ∑ i, capacityBits i n
  overlapTransitionConsistency : Prop
  overlapTransitionConsistency_realized : overlapTransitionConsistency
  atlasDerivedFromSolver : Prop
  atlasDerivedFromSolver_realized : atlasDerivedFromSolver
  aggregateProjectionCompatibility : Prop
  aggregateProjectionCompatibility_realized : aggregateProjectionCompatibility

namespace HolographicObserverPerspectiveAtlas

/-- A finite atlas of polynomial-capacity perspectives has polynomial total
capacity.  The proof sums the coefficients and uses the sum of degrees as a
uniform exponent, so no separate global polynomial-capacity assumption is
needed. -/
theorem totalCapacityBits_poly {raw : Type}
    (A : HolographicObserverPerspectiveAtlas raw) :
    AtlasPolyBounded A.totalCapacityBits := by
  classical
  letI : Fintype A.Perspective := A.perspectiveFintype
  let c : A.Perspective -> Nat := fun i => Classical.choose (A.capacityBits_poly i)
  let k : A.Perspective -> Nat := fun i =>
    Classical.choose (Classical.choose_spec (A.capacityBits_poly i))
  have hcap : ∀ i n, A.capacityBits i n ≤ c i * (n + 1) ^ k i := by
    intro i n
    exact Classical.choose_spec (Classical.choose_spec (A.capacityBits_poly i)) n
  refine ⟨∑ i, c i, ∑ i, k i, ?_⟩
  intro n
  rw [A.totalCapacityBits_eq_sum]
  calc
    ∑ i, A.capacityBits i n ≤ ∑ i, c i * (n + 1) ^ k i := by
      exact Finset.sum_le_sum (fun i _ => hcap i n)
    _ ≤ ∑ i, c i * (n + 1) ^ (∑ j, k j) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_right
      · omega
      · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    _ = (∑ i, c i) * (n + 1) ^ (∑ i, k i) := by
      rw [Finset.sum_mul]

/-- The combined boundary seen by all observer perspectives. -/
def JointBoundary {raw : Type} (A : HolographicObserverPerspectiveAtlas raw) : Type :=
  ∀ i : A.Perspective, A.Boundary i

/-- The combined observer records every perspective simultaneously. -/
def jointView {raw : Type} (A : HolographicObserverPerspectiveAtlas raw) :
    raw -> A.JointBoundary :=
  fun r i => A.view i r

/-- The joint boundary is finite because the atlas and every chart are finite. -/
noncomputable def jointBoundaryFintype {raw : Type}
    (A : HolographicObserverPerspectiveAtlas raw) : Fintype A.JointBoundary := by
  classical
  letI : Fintype A.Perspective := A.perspectiveFintype
  letI : DecidableEq A.Perspective := Classical.decEq _
  letI : ∀ i : A.Perspective, Fintype (A.Boundary i) := A.boundaryFintype
  letI : ∀ i : A.Perspective, DecidableEq (A.Boundary i) := fun _ => Classical.decEq _
  change Fintype (∀ i : A.Perspective, A.Boundary i)
  infer_instance

/-- Exact state count of the multi-perspective boundary: capacities multiply
as state counts (equivalently, their logarithmic bit capacities add). -/
theorem jointBoundary_card {raw : Type}
    (A : HolographicObserverPerspectiveAtlas raw) :
    @Fintype.card A.JointBoundary A.jointBoundaryFintype =
      (@Finset.univ A.Perspective A.perspectiveFintype).prod
        (fun i => @Fintype.card (A.Boundary i) (A.boundaryFintype i)) := by
  classical
  letI : Fintype A.Perspective := A.perspectiveFintype
  letI : DecidableEq A.Perspective := Classical.decEq _
  letI : ∀ i : A.Perspective, Fintype (A.Boundary i) := A.boundaryFintype
  letI : ∀ i : A.Perspective, DecidableEq (A.Boundary i) := fun _ => Classical.decEq _
  change Fintype.card (∀ i : A.Perspective, A.Boundary i) =
    ∏ i, Fintype.card (A.Boundary i)
  exact Fintype.card_pi

/-- If the joint atlas preserves an `m`-bit hard fooling family, its combined
boundary must contain at least `2^m` states.  Different perspectives can see
different features, but jointly faithful observation pays the product of their
state spaces. -/
theorem joint_boundary_card_ge_exp_of_fooling {raw : Type} {m : Nat}
    (A : HolographicObserverPerspectiveAtlas raw)
    (rawObserver : TranscriptObserver raw)
    (fam : FoolingResidualFamily m)
    (hsound : SoundOnFoolingFamily
      (fun x => A.jointView (rawObserver x)) fam) :
    2 ^ m ≤ @Fintype.card A.JointBoundary A.jointBoundaryFintype := by
  letI : Fintype A.JointBoundary := A.jointBoundaryFintype
  exact transcript_boundary_card_ge_exp_of_fooling
    (fun x => A.jointView (rawObserver x)) fam hsound

end HolographicObserverPerspectiveAtlas

/-! ### Asymmetric NP and P observer perspectives

The NP observer and the P observer are not charts of one joint atlas.  The NP
observer receives a witness and may expose a God’s-eye view of the complete
verification geometry.  The P observer receives only the instance and evolves
through its own bounded computational boundary.  In particular, no map from
the P boundary to the NP boundary, no common boundary type, and no recovery of
the NP witness label is required below.
-/

/-- The God’s-eye NP perspective.  Its view is indexed by both an instance and
a witness; its boundary is deliberately unrelated to the P boundary. -/
structure NPVerifierGodEyePerspective (Instance Witness : Type)
    (accepts : Instance -> Witness -> Prop) where
  Boundary : Type
  view : Instance -> Witness -> Boundary
  verifierSound : Prop
  verifierSound_realized : verifierSound
  ramanujanWitnessGeometry : Prop
  ramanujanWitnessGeometry_realized : ramanujanWitnessGeometry

/-- The algorithmic P perspective.  It sees only the input instance.  Its
finite state/transcript boundary and resource accounting do not include the
NP observer's witness-bearing boundary. -/
structure PDeciderBoundaryPerspective (Instance : Type) where
  Boundary : Type
  boundaryFintype : Fintype Boundary
  view : Instance -> Boundary
  answer : Boundary -> Bool
  capacityBits : Nat -> Nat
  capacityBits_poly : AtlasPolyBounded capacityBits

/-- The only permitted connection between the asymmetric observers is the
existential language semantics.  `decisionInvariant` must be an invariant of
deciding `∃ w, accepts x w`; it may not demand witness or residual-label
reconstruction.  The two last fields isolate the genuine missing mathematics:
correct P-decision forces the invariant, while the Ramanujan/SPDP lower bound
rules it out for a polynomial boundary. -/
structure AsymmetricDecisionInvariantBridge
    (Instance Witness : Type) (accepts : Instance -> Witness -> Prop) where
  npObserver : NPVerifierGodEyePerspective Instance Witness accepts
  pObserver : PDeciderBoundaryPerspective Instance
  pDecidesExistential :
    ∀ x, pObserver.answer (pObserver.view x) = true ↔ ∃ w, accepts x w
  decisionInvariant : Prop
  decisionInvariant_of_correct_decision :
    (∀ x, pObserver.answer (pObserver.view x) = true ↔ ∃ w, accepts x w) ->
      decisionInvariant
  ramanujanSPDP_obstructs_decisionInvariant : decisionInvariant -> False

namespace AsymmetricDecisionInvariantBridge

/-- The asymmetric bridge closes using only the P-side decision invariant.
The proof never combines boundaries and never asks the P observer to decode an
NP witness or hard-residual label. -/
theorem impossible {Instance Witness : Type}
    {accepts : Instance -> Witness -> Prop}
    (B : AsymmetricDecisionInvariantBridge Instance Witness accepts) : False :=
  B.ramanujanSPDP_obstructs_decisionInvariant
    (B.decisionInvariant_of_correct_decision B.pDecidesExistential)

end AsymmetricDecisionInvariantBridge

/-- SAT-specific asymmetric payload.  The abstract `Instance`, `Witness`, and
verifier relation permit the Cook--Levin/Ramanujan development to choose its
actual encoded objects without identifying either observer boundary. -/
structure AsymmetricSATObserverBridgeFor
    (U : MachineModel) (D : DecisionMachine U) (hD : DecidesSAT U D) where
  Instance : Type
  Witness : Type
  accepts : Instance -> Witness -> Prop
  observers : AsymmetricDecisionInvariantBridge Instance Witness accepts
  derivedFromDecider : Prop
  derivedFromDecider_realized : derivedFromDecider
  cookLevinSPDPCompatibility : Prop
  cookLevinSPDPCompatibility_realized : cookLevinSPDPCompatibility

namespace AsymmetricSATObserverBridgeFor

theorem impossible {U : MachineModel} {D : DecisionMachine U}
    {hD : DecidesSAT U D} (B : AsymmetricSATObserverBridgeFor U D hD) : False :=
  B.observers.impossible

end AsymmetricSATObserverBridgeFor

/-- The corrected asymmetric completion target.  Unlike the joint-atlas
target, it never requires a P-time SAT decider to distinguish NP witnesses. -/
abbrev AsymmetricSATObserverBridgeForPTimeSAT (U : MachineModel) : Type 1 :=
  ∀ (D : DecisionMachine U) (hD : DecidesSAT U D),
    AsymmetricSATObserverBridgeFor U D hD

theorem no_SATDecisionInP_of_asymmetricObserverBridge {U : MachineModel}
    (hBridge : AsymmetricSATObserverBridgeForPTimeSAT U) :
    ¬ SATDecisionInP U := by
  rintro ⟨D, hD⟩
  exact (hBridge D hD).impossible

/-- The complete, honest certificate required for the holographic/N-frame
route to close against one alleged polynomial-time SAT decider.

The first two requirements are the corresponding fields of `extraction`:
`polyPositiveCells` and `preservesLabels`.  The remaining fields make efficient
solver extraction, SPDP/Cook--Levin rank faithfulness, and the N-frame
Lagrangian origin explicit. -/
structure CompleteHolographicNFrameBridgeFor
    (U : MachineModel) (D : DecisionMachine U) (hD : DecidesSAT U D) where
  extraction : RamanujanHolographicAmplituhedronExtractionFor U D hD
  efficientEncodingDecoding :
    EfficientHolographicEncodingDecodingPayload U D hD
      extraction.rawTranscript extraction.holographicScreen extraction.positiveCellType
  spdpCookLevinCompatibility :
    SPDPCookLevinRankFaithfulCompatibilityPayload
      extraction.rawTranscript extraction.holographicScreen extraction.positiveCellType
  nframeLagrangianProjection :
    NFrameLagrangianProjectionPayload
      extraction.rawTranscript extraction.holographicScreen extraction.positiveCellType
  observerPerspectiveAtlas :
    HolographicObserverPerspectiveAtlas extraction.rawTranscript
  atlasJointPreservesLabels :
    SoundOnFoolingFamily
      (fun x => observerPerspectiveAtlas.jointView (extraction.rawObserver x))
      extraction.fam
  atlasJointBoundaryPoly :
    @Fintype.card observerPerspectiveAtlas.JointBoundary
      observerPerspectiveAtlas.jointBoundaryFintype ≤ extraction.m ^ extraction.k

namespace CompleteHolographicNFrameBridgeFor

variable {U : MachineModel} {D : DecisionMachine U} {hD : DecidesSAT U D}

/-- A complete certificate contains the small finite-capacity proof. -/
theorem small_finite_computational_capacity
    (B : CompleteHolographicNFrameBridgeFor U D hD) :
    @Fintype.card B.extraction.positiveCellType B.extraction.fintypePositiveCell ≤
      B.extraction.m ^ B.extraction.k :=
  B.extraction.polyPositiveCells

/-- A complete certificate contains hard-residual label preservation. -/
theorem preservation_injectivity_on_hard_residuals
    (B : CompleteHolographicNFrameBridgeFor U D hD) :
    SoundOnFoolingFamily
      (fun x => composedPositiveProjection B.extraction.holographic
        B.extraction.amplituhedron (B.extraction.rawObserver x))
      B.extraction.fam :=
  B.extraction.preservesLabels

/-- The complete four-requirement certificate contradicts the alleged decider.

The proof delegates only to the already kernel-checked structured extraction
cash-out; the extra fields record why the geometric projection is a legitimate
solver-derived N-frame/SPDP construction rather than an arbitrary map. -/
theorem impossible (B : CompleteHolographicNFrameBridgeFor U D hD) : False :=
  B.extraction.impossible

/-- Direct contradiction through the combined multi-perspective boundary.

This route uses no single preferred observer chart: joint label preservation
forces at least `2^m` product states, while the solver-derived atlas certificate
bounds the same product boundary by `m^k`. -/
theorem impossible_via_observerAtlas
    (B : CompleteHolographicNFrameBridgeFor U D hD) : False := by
  letI : Fintype B.observerPerspectiveAtlas.JointBoundary :=
    B.observerPerspectiveAtlas.jointBoundaryFintype
  exact transcript_fooling_contradicts_poly_boundary
    (fun x => B.observerPerspectiveAtlas.jointView (B.extraction.rawObserver x))
    B.extraction.fam B.atlasJointPreservesLabels B.atlasJointBoundaryPoly
    B.extraction.expGap

end CompleteHolographicNFrameBridgeFor

/-- Complete holographic/N-frame bridge data for every claimed SAT decider. -/
abbrev CompleteHolographicNFrameBridgeForPTimeSAT (U : MachineModel) : Type 1 :=
  ∀ (D : DecisionMachine U) (hD : DecidesSAT U D),
    CompleteHolographicNFrameBridgeFor U D hD

/-- Cash-out for the complete four-requirement holographic/N-frame bridge. -/
theorem no_SATDecisionInP_of_completeHolographicNFrameBridge {U : MachineModel}
    (hComplete : CompleteHolographicNFrameBridgeForPTimeSAT U) :
    ¬ SATDecisionInP U := by
  intro hP
  rcases hP with ⟨D, hD⟩
  exact (hComplete D hD).impossible

/-- Vacuous reverse construction used only to calibrate logical strength.

If SAT is already known not to be decidable in polynomial time, every alleged
decider hypothesis is contradictory, so the complete certificate family is
inhabited by elimination.  This constructs no holographic projection. -/
noncomputable def completeHolographicNFrameBridge_of_no_SATDecisionInP
    {U : MachineModel} (hNo : ¬ SATDecisionInP U) :
    CompleteHolographicNFrameBridgeForPTimeSAT U := by
  intro D hD
  exact False.elim (hNo ⟨D, hD⟩)

/-- Exact logical calibration of the fully general completion target.

Constructing the complete holographic/N-frame certificate for every alleged
polynomial-time SAT decider is equivalent, in the abstract machine model, to
proving that SAT has no polynomial-time decider.  Consequently this target
cannot be discharged merely from projection existence, the area law, or
Lagrangian minimisation; one of its semantic/rank-faithfulness fields must
contain genuinely new separation-strength mathematics. -/
theorem completeHolographicNFrameBridge_iff_no_SATDecisionInP
    {U : MachineModel} :
    Nonempty (CompleteHolographicNFrameBridgeForPTimeSAT U) ↔
      ¬ SATDecisionInP U := by
  constructor
  · rintro ⟨hComplete⟩
    exact no_SATDecisionInP_of_completeHolographicNFrameBridge hComplete
  · intro hNo
    exact ⟨completeHolographicNFrameBridge_of_no_SATDecisionInP hNo⟩

/-!
### Why two-dimensional holography alone does not inhabit the certificate

The area-law pressure test has the form

```text
capacityBits <= boundaryUses * R^2.
```

A static `R^2` boundary cannot recover an injective `R^3`-bit bulk label, but
`R` sequential reuses attain `R * R^2 = R^3`.  Polynomial-time machines are
allowed polynomially many updates.  Moreover, a real-valued screen has no
finite information bound without an explicit precision/description model.
Those are the reasons `EfficientHolographicEncodingDecodingPayload` exposes
finite precision, description length, update count, and codec cost separately.

Multiple perspectives belonging to one computational observer do not evade
capacity accounting: their joint information budget includes all charts and
transitions.  `HolographicObserverPerspectiveAtlas` formalizes that statement.
It must not, however, be used to merge the NP verifier with the P decider.  The
NP observer may receive a witness and have a God’s-eye boundary wholly distinct
from the P observer's algorithmic boundary.

`AsymmetricDecisionInvariantBridge` is the corrected P-versus-NP interface.
Its observers share only the semantics `decide x ↔ ∃ w, accepts x w`; it has no
joint boundary and requires no P-side witness or residual-label reconstruction.
The remaining separation theorem is correspondingly the construction of a
decision invariant which (i) follows from correctly deciding this existential
predicate with the P boundary and (ii) is obstructed by the Ramanujan/SPDP
lower bound.  A witness-recovery lower bound cannot fill this field.

Likewise, existence or minimisation of the N-frame Lagrangian does not imply
that the selected projection preserves SAT labels or the SPDP identity minor.
The zero/low-rank collapse is excluded only by the explicit unit/identity-minor
and rank-faithfulness fields above.

The exact remaining theorem is therefore the construction of

```lean
CompleteHolographicNFrameBridgeForPTimeSAT U
```

from the concrete semantics of every alleged polynomial-time SAT decider.
Once supplied, `no_SATDecisionInP_of_completeHolographicNFrameBridge` closes
the route.  This file does not assert that construction: doing so without
realizing its fields would merely rename the P-versus-NP conjecture.
-/

/-!
Route status:

```text
RamanujanBoundaryCertificate
  -> HolographicProjectionStage
  -> AmplituhedronPositiveCellStage
  -> StructuredDynamicH4ExtractionFor
  -> ¬ SATDecisionInP
```

The named geometric theorem to prove is now:

```lean
RamanujanHolographicAmplituhedronForPTimeSAT U
```

and the unavoidable hard subclaim remains `preservesLabels`: the composed positive-cell projection must preserve the
labels of a hard residual SAT/search fooling family.
-/

end PallLean.Paper93.DeepMath.PathB.PvsNPRamanujanHolographicAmplituhedronExtraction

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPRamanujanHolographicAmplituhedronExtraction.composedPositiveProjection
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPRamanujanHolographicAmplituhedronExtraction.toPACProjection
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPRamanujanHolographicAmplituhedronExtraction.RamanujanHolographicAmplituhedronExtractionFor.toStructured
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPRamanujanHolographicAmplituhedronExtraction.RamanujanHolographicAmplituhedronExtractionFor.impossible
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPRamanujanHolographicAmplituhedronExtraction.RamanujanHolographicAmplituhedronExtractionFor.impossible_via_positive_cells
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPRamanujanHolographicAmplituhedronExtraction.RamanujanHolographicAmplituhedronExtractionFor.preservation_is_still_the_gap
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPRamanujanHolographicAmplituhedronExtraction.structuredDynamicH4_of_RamanujanHolographicAmplituhedron
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPRamanujanHolographicAmplituhedronExtraction.no_SATDecisionInP_of_RamanujanHolographicAmplituhedron
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPRamanujanHolographicAmplituhedronExtraction.no_SATDecisionInP_of_RamanujanHolographicAmplituhedron_direct
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPRamanujanHolographicAmplituhedronExtraction.CompleteHolographicNFrameBridgeFor.impossible
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPRamanujanHolographicAmplituhedronExtraction.no_SATDecisionInP_of_completeHolographicNFrameBridge
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPRamanujanHolographicAmplituhedronExtraction.completeHolographicNFrameBridge_iff_no_SATDecisionInP
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPRamanujanHolographicAmplituhedronExtraction.HolographicObserverPerspectiveAtlas.totalCapacityBits_poly
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPRamanujanHolographicAmplituhedronExtraction.HolographicObserverPerspectiveAtlas.jointBoundary_card
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPRamanujanHolographicAmplituhedronExtraction.HolographicObserverPerspectiveAtlas.joint_boundary_card_ge_exp_of_fooling
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPRamanujanHolographicAmplituhedronExtraction.CompleteHolographicNFrameBridgeFor.impossible_via_observerAtlas
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPRamanujanHolographicAmplituhedronExtraction.AsymmetricDecisionInvariantBridge.impossible
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPRamanujanHolographicAmplituhedronExtraction.no_SATDecisionInP_of_asymmetricObserverBridge
