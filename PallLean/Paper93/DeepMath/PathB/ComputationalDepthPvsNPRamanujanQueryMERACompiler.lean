import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPDynamicHolonomyQueryTranscriptBridge
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPTseitinExpanderRHAExtraction

/-!
# Ramanujan/expander routing and compiler for decision-relevant SAT queries

This file connects the concrete independent SAT-query batch to the repository's genuine Tseitin
expansion certificate and to the dynamic bounded-MERA transcript compiler.

The separation is intentional:

* `RamanujanExpanderQueryLayout n` routes the `n` SAT coordinates injectively to vertices of a certified
  expander.  Its expansion field is the real `TseitinGraph.HasExpansion` predicate, not decorative text.
* `RamanujanMERAQueryTranscript` couples that layout to an exact `MERAQueryTranscript`.
* `toDynamicHolonomyDecoder` forgets the routing metadata and compiles the certified boundary execution
  to the existing dynamic decoder.
* `RamanujanQueryMERACompiler` packages one fixed bounded-MERA family, an all-size expander layout, and
  the actual transcript realization.

Expansion supplies robust routing/no-hiding for medium vertex sets, but it does not by itself prove that
an arbitrary SAT machine's complete batch-answer transcript fits a polynomial-state MERA boundary.  The
final audit theorem makes that distinction formal.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsNPRamanujanQueryMERACompiler

open SATDepthMachine
open Finset
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.PvsNPDynamicHolonomyDecisionRelevance
open PallLean.Paper93.DeepMath.PathB.PvsNPDynamicHolonomyQueryTranscriptBridge
open PallLean.Paper93.DeepMath.PathB.PvsNPNFrameDynamicMERAHolonomy
open PallLean.Paper93.DeepMath.PathB.PvsNPNFrameDynamicMERAHolonomy.DynamicHolonomyMERADecoder
open PallLean.Paper93.DeepMath.PathB.PvsNPTseitinExpanderRHAExtraction

/-! ## Expander routing of the SAT-query coordinates -/

/-- A real expander layout for `n` independent SAT-query coordinates.

The certificate carries a concrete finite Tseitin graph and a proof of `HasExpansion c`.  The injective
map prevents two query coordinates from being identified before the dynamic computation begins. -/
structure RamanujanExpanderQueryLayout (n : Nat) where
  certificate : TseitinExpanderCertificate
  expansion_pos : 1 ≤ certificate.c
  coordinateVertex : Fin n → certificate.V
  coordinateVertex_injective : Function.Injective coordinateVertex

namespace RamanujanExpanderQueryLayout

/-- Expansion gives the usual width/no-hiding statement for every medium nonempty routed vertex set. -/
theorem combination_width (L : RamanujanExpanderQueryLayout n)
    (S : Finset L.certificate.V)
    (h1 : 1 ≤ S.card) (h2 : 2 * S.card ≤ Fintype.card L.certificate.V) :
    L.certificate.c * S.card ≤
      (edgeSupport (L.certificate.graph.combination S)).card := by
  exact L.certificate.combination_width S h1 h2

/-- Hence no medium nonempty routed vertex combination vanishes. -/
theorem exists_surviving_edge (L : RamanujanExpanderQueryLayout n)
    (S : Finset L.certificate.V)
    (h1 : 1 ≤ S.card) (h2 : 2 * S.card ≤ Fintype.card L.certificate.V) :
    ∃ e : L.certificate.Edge, L.certificate.graph.combination S e ≠ 0 := by
  exact L.certificate.exists_surviving_edge_of_medium_combination
    L.expansion_pos S h1 h2

/-- Non-vacuity: the already machine-checked `K4` expander routes four query coordinates. -/
def K4QueryLayout : RamanujanExpanderQueryLayout 4 where
  certificate := K4_tseitinExpanderCertificate
  expansion_pos := by decide
  coordinateVertex := id
  coordinateVertex_injective := Function.injective_id

end RamanujanExpanderQueryLayout

/-! ## Ramanujan-routed query transcripts -/

/-- A concrete expander-routed SAT-query batch together with its exact bounded-MERA boundary execution. -/
structure RamanujanMERAQueryTranscript
    {n : Nat} {U : MachineModel} (D : DecisionMachine U) (M : MERAFamily) where
  layout : RamanujanExpanderQueryLayout n
  transcript : MERAQueryTranscript (independentSATQueryFamily n) D M

namespace RamanujanMERAQueryTranscript

/-- Compile the routed transcript to the exact dynamic holonomy decoder.  Expansion remains available
as routing structure; exact SAT-answer preservation comes from `transcript.exactAnswers`. -/
noncomputable def toDynamicHolonomyDecoder
    {n : Nat} {U : MachineModel} {D : DecisionMachine U} {M : MERAFamily}
    (R : RamanujanMERAQueryTranscript (n := n) D M) (hD : DecidesSAT U D) :
    DynamicHolonomyMERADecoder M n :=
  R.transcript.toDynamicHolonomyDecoder hD

/-- Every intermediate boundary slice of a correct routed transcript still needs `2^n` states. -/
theorem stateAt_injective
    {n : Nat} {U : MachineModel} {D : DecisionMachine U} {M : MERAFamily}
    (R : RamanujanMERAQueryTranscript (n := n) D M) (hD : DecidesSAT U D)
    (time : Nat) (htime : time ≤ M.layers n) :
    Function.Injective ((R.toDynamicHolonomyDecoder hD).stateAt time) :=
  DynamicHolonomyMERADecoder.stateAt_injective
    (R.toDynamicHolonomyDecoder hD) time htime

/-- At a size above the MERA polynomial ceiling, no correct Ramanujan-routed transcript exists. -/
theorem no_routed_transcript_at_size
    {n : Nat} {U : MachineModel} {D : DecisionMachine U} (M : MERAFamily)
    (hn : 1 ≤ n) (hgap : n ^ M.polyExponent < 2 ^ n)
    (hD : DecidesSAT U D) :
    ¬ Nonempty (RamanujanMERAQueryTranscript (n := n) D M) := by
  rintro ⟨R⟩
  exact (DynamicHolonomyMERADecoder.no_dynamicDecoder_at_size M n hn hgap)
    ⟨R.toDynamicHolonomyDecoder hD⟩

end RamanujanMERAQueryTranscript

/-! ## The compiler and its exact frontier -/

/-- A full restricted compiler for one decision machine.

It supplies an expander layout at every batch size and realizes the corresponding independent SAT-query
answers inside one fixed bounded-bond, fixed-cone, logarithmic-depth MERA family. -/
structure RamanujanQueryMERACompiler
    (U : MachineModel) (D : DecisionMachine U) where
  mera : MERAFamily
  layout : ∀ n, RamanujanExpanderQueryLayout n
  compile : DecidesSAT U D → ∀ n,
    Nonempty (RamanujanMERAQueryTranscript (n := n) D mera)

namespace RamanujanQueryMERACompiler

/-- Forgetting expander routing yields the previously proved independent-query compiler. -/
def toIndependentQueryCompiler
    {U : MachineModel} {D : DecisionMachine U}
    (C : RamanujanQueryMERACompiler U D) :
    SATCorrectnessCompilesIndependentQueries U D C.mera := by
  intro hD n
  obtain ⟨R⟩ := C.compile hD n
  exact ⟨R.transcript⟩

/-- Therefore no SAT-correct machine admits this full Ramanujan-to-MERA compiler. -/
theorem not_decidesSAT
    {U : MachineModel} {D : DecisionMachine U}
    (C : RamanujanQueryMERACompiler U D) :
    ¬ DecidesSAT U D :=
  not_decidesSAT_of_independentQueryCompiler C.mera C.toIndependentQueryCompiler

end RamanujanQueryMERACompiler

/-- **Expansion alone does not manufacture the compiler.**  Even if an all-size expander layout family
is supplied, a SAT-correct machine cannot have an exact bounded-MERA query transcript at every size.
Thus the missing content is the claimed machine-to-local-MERA realization, not existence of expanders. -/
theorem expander_layout_does_not_supply_MERA_transcripts
    {U : MachineModel} {D : DecisionMachine U} (M : MERAFamily)
    (_layouts : ∀ n, RamanujanExpanderQueryLayout n)
    (hD : DecidesSAT U D) :
    ¬ (∀ n, Nonempty (RamanujanMERAQueryTranscript (n := n) D M)) := by
  intro hall
  obtain ⟨n, _, hnone⟩ :=
    DynamicHolonomyMERADecoder.exists_size_without_dynamicHolonomyDecoder M
  obtain ⟨R⟩ := hall n
  exact hnone ⟨R.toDynamicHolonomyDecoder hD⟩

/-! ## Honest endpoint

The Ramanujan/expander side now contributes real combinatorics: injective coordinate routing and the
machine-checked expansion width/no-vanishing theorem.  The compiler side is also explicit and connects
directly to the dynamic MERA lower bound.

What remains unproved is not a graph theorem.  It is the assertion that the internal execution of an
arbitrary polynomial-time SAT machine provides `RamanujanMERAQueryTranscript.transcript`, especially its
`exactAnswers` and `boundary_card_le` fields, for all sizes.  Expansion cannot imply those fields from
input/output SAT correctness alone.
-/

end PallLean.Paper93.DeepMath.PathB.PvsNPRamanujanQueryMERACompiler

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPRamanujanQueryMERACompiler.RamanujanExpanderQueryLayout.combination_width
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPRamanujanQueryMERACompiler.RamanujanExpanderQueryLayout.exists_surviving_edge
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPRamanujanQueryMERACompiler.RamanujanMERAQueryTranscript.toDynamicHolonomyDecoder
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPRamanujanQueryMERACompiler.RamanujanMERAQueryTranscript.no_routed_transcript_at_size
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPRamanujanQueryMERACompiler.RamanujanQueryMERACompiler.not_decidesSAT
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPRamanujanQueryMERACompiler.expander_layout_does_not_supply_MERA_transcripts
