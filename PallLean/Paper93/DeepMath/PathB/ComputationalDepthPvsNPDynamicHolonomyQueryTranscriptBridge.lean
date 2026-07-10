import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPDynamicHolonomyDecisionRelevance

/-!
# Dynamic holonomy: concrete SAT-query family and MERA transcript compiler

This file closes the two *restricted-model* bridges left by
`ComputationalDepthPvsNPDynamicHolonomyDecisionRelevance`.

First, it gives a solver-independent, syntactic query family.  An instance is an `n`-tuple of arbitrary
CNFs, coordinate `i` is exposed by projecting the `i`th CNF, and its holonomy bit is that formula's SAT
truth value.  No alleged solver and no precomputed answer is used by the query map.  Every bit-vector is
realized by explicit satisfiable/unsatisfiable CNFs, while every coordinate is SAT-hard by the identity
embedding of an arbitrary CNF into that coordinate.

Second, `MERAQueryTranscript` records a batch SAT-query execution whose final answer vector is decoded
from a fixed bounded-MERA boundary.  `toDynamicHolonomyDecoder` compiles such a transcript into the exact
dynamic decoder of the previous file.  Thus the existing dynamic no-merging theorem applies directly.

The conclusion is deliberately restricted and non-circular: no SAT-correct machine can have these
independent SAT-query batches realized at every size by one fixed-bond, fixed-cone, logarithmic-depth MERA
family.  The file does **not** prove that an arbitrary polynomial-time machine admits that realization.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsNPDynamicHolonomyQueryTranscriptBridge

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPDynamicHolonomyDecisionRelevance
open PallLean.Paper93.DeepMath.PathB.PvsNPNFrameDynamicMERAHolonomy
open PallLean.Paper93.DeepMath.PathB.PvsNPNFrameDynamicMERAHolonomy.DynamicHolonomyMERADecoder

/-! ## 1. A concrete decision-relevant SAT batch -/

/-- The Boolean SAT truth value.  It is used only to state the semantic label; the query constructor below
is the syntactic projection `batch i` and therefore does not compute this value. -/
noncomputable def satTruth (φ : CNF) : Bool :=
  by
    classical
    exact if Satisfiable φ then true else false

@[simp] theorem satTruth_eq_true_iff (φ : CNF) :
    satTruth φ = true ↔ Satisfiable φ := by
  classical
  simp [satTruth]

/-- A fixed satisfiable CNF. -/
def yesCNF : CNF := { vars := 0, clauses := [] }

/-- A fixed unsatisfiable CNF (the empty clause). -/
def noCNF : CNF := { vars := 0, clauses := [[]] }

theorem yesCNF_satisfiable : Satisfiable yesCNF := by
  exact ⟨[], by simp [yesCNF, Satisfies, CNF.eval]⟩

theorem noCNF_not_satisfiable : ¬ Satisfiable noCNF := by
  rintro ⟨a, _, heval⟩
  simp [noCNF, CNF.eval, Clause.eval] at heval

@[simp] theorem satTruth_yesCNF : satTruth yesCNF = true := by
  exact (satTruth_eq_true_iff yesCNF).2 yesCNF_satisfiable

@[simp] theorem satTruth_noCNF : satTruth noCNF = false := by
  classical
  simp [satTruth, noCNF_not_satisfiable]

/-- An `n`-coordinate batch of completely arbitrary SAT instances.

The label is their SAT truth profile and query `i` is literally the `i`th input CNF.  In particular the
query construction is uniform, solver-independent, and does not encode a previously computed answer. -/
noncomputable def independentSATQueryFamily (n : Nat) : SATQueryHolonomyFamily n where
  Instance := Fin n → CNF
  label := fun batch i => satTruth (batch i)
  query := fun batch i => batch i
  query_sat_iff := by
    intro batch i
    exact (satTruth_eq_true_iff (batch i)).symm
  label_surjective := by
    intro target
    refine ⟨fun i => if target i then yesCNF else noCNF, ?_⟩
    funext i
    cases h : target i <;> simp [h]

/-- The query constructor is purely syntactic projection. -/
@[simp] theorem independentSAT_query (n : Nat)
    (batch : Fin n → CNF) (i : Fin n) :
    (independentSATQueryFamily n).query batch i = batch i := rfl

/-- Every coordinate problem of a nonempty independent batch is SAT-hard under a direct many-one
reduction: copy the input CNF into every coordinate and project the chosen coordinate. -/
theorem SAT_reduces_to_independent_coordinate
    {n : Nat} (i : Fin n) :
    ManyOneReduces Satisfiable
      (fun batch : (independentSATQueryFamily n).Instance =>
        (independentSATQueryFamily n).label batch i = true) := by
  refine ⟨fun φ _ => φ, ?_⟩
  intro φ
  exact (satTruth_eq_true_iff φ).symm

/-- Conversely, a coordinate problem reduces back to ordinary SAT by projecting its concrete CNF.
Together with `SAT_reduces_to_independent_coordinate`, every nonempty coordinate has exactly the SAT
many-one degree in the repository's concrete CNF semantics. -/
theorem independent_coordinate_reduces_to_SAT
    {n : Nat} (i : Fin n) :
    ManyOneReduces
      (fun batch : (independentSATQueryFamily n).Instance =>
        (independentSATQueryFamily n).label batch i = true)
      Satisfiable := by
  refine ⟨fun batch => batch i, ?_⟩
  intro batch
  exact satTruth_eq_true_iff (batch i)

/-! ## 2. Compile a certified batch-query transcript into dynamic MERA -/

/-- A realization of all coordinate-query answers by one bounded-MERA boundary trajectory.

`observe` initializes the boundary from the query batch.  After the fixed `M.layers n` transitions,
`decode` must return the actual vector produced by `D` on all coordinate CNFs.  The last field is the
load-bearing restricted-model requirement: this concrete boundary must fit inside the MERA causal-cone
accessible-rank budget. -/
structure MERAQueryTranscript
    {n : Nat} {U : MachineModel} (F : SATQueryHolonomyFamily n)
    (D : DecisionMachine U) (M : MERAFamily) where
  BoundaryState : Type
  [stateFintype : Fintype BoundaryState]
  [stateDecidableEq : DecidableEq BoundaryState]
  observe : F.Instance → BoundaryState
  step : Nat → BoundaryState → BoundaryState
  decode : BoundaryState → HolonomySignature n
  exactAnswers : ∀ x,
    decode (runFrom step 0 (M.layers n) (observe x)) = F.answers D x
  boundary_card_le : Fintype.card BoundaryState ≤ M.accessibleRank n

namespace MERAQueryTranscript

/-- **Transcript-to-dynamics compiler.**  SAT correctness identifies the transcript's query-answer
vector with the semantic holonomy label.  Surjectivity chooses one concrete SAT batch for every label;
the transcript boundary trajectory on that representative is therefore an exact dynamic holonomy
decoder. -/
noncomputable def toDynamicHolonomyDecoder
    {n : Nat} {U : MachineModel} {F : SATQueryHolonomyFamily n}
    {D : DecisionMachine U} {M : MERAFamily}
    (T : MERAQueryTranscript F D M) (hD : DecidesSAT U D) :
    DynamicHolonomyMERADecoder M n where
  BoundaryState := T.BoundaryState
  stateFintype := T.stateFintype
  stateDecidableEq := T.stateDecidableEq
  encode := fun signature =>
    T.observe (Classical.choose (F.label_surjective signature))
  step := T.step
  decode := T.decode
  correct := by
    intro signature
    let x : F.Instance := Classical.choose (F.label_surjective signature)
    have hx : F.label x = signature := Classical.choose_spec (F.label_surjective signature)
    calc
      T.decode (runFrom T.step 0 (M.layers n) (T.observe x)) = F.answers D x :=
        T.exactAnswers x
      _ = F.label x := F.answers_eq_label D hD x
      _ = signature := hx
  boundary_card_le := T.boundary_card_le

/-- Any correct transcript realization inherits the dynamic no-merging theorem at every time slice. -/
theorem stateAt_injective
    {n : Nat} {U : MachineModel} {F : SATQueryHolonomyFamily n}
    {D : DecisionMachine U} {M : MERAFamily}
    (T : MERAQueryTranscript F D M) (hD : DecidesSAT U D)
    (time : Nat) (htime : time ≤ M.layers n) :
    Function.Injective ((T.toDynamicHolonomyDecoder hD).stateAt time) :=
  DynamicHolonomyMERADecoder.stateAt_injective (T.toDynamicHolonomyDecoder hD) time htime

/-- A correct fixed-boundary query transcript must expose at least `2^n` boundary states. -/
theorem two_pow_le_boundary_card
    {n : Nat} {U : MachineModel} {F : SATQueryHolonomyFamily n}
    {D : DecisionMachine U} {M : MERAFamily}
    (T : MERAQueryTranscript F D M) (hD : DecidesSAT U D) :
    2 ^ n ≤ @Fintype.card T.BoundaryState T.stateFintype := by
  exact (T.toDynamicHolonomyDecoder hD).two_pow_le_boundary_card_at_time
    (M.layers n) le_rfl

/-- At a size above the restricted MERA ceiling, no SAT-correct decision machine can have an exact
independent-query transcript realization in that MERA family. -/
theorem no_transcript_at_size
    {n : Nat} {U : MachineModel} {D : DecisionMachine U} (M : MERAFamily)
    (hn : 1 ≤ n) (hgap : n ^ M.polyExponent < 2 ^ n)
    (hD : DecidesSAT U D) :
    ¬ Nonempty (MERAQueryTranscript (independentSATQueryFamily n) D M) := by
  rintro ⟨T⟩
  exact (DynamicHolonomyMERADecoder.no_dynamicDecoder_at_size M n hn hgap)
    ⟨T.toDynamicHolonomyDecoder hD⟩

end MERAQueryTranscript

/-! ## Restricted SAT cash-out -/

/-- The precise remaining *model* compiler: SAT correctness would realize every concrete independent
SAT-query batch by one fixed bounded-MERA family.  Unlike the former semantic label bridge, the query
family here is fully constructed; only the claim that a machine's batch transcript fits this restricted
MERA architecture remains a class assumption. -/
def SATCorrectnessCompilesIndependentQueries
    (U : MachineModel) (D : DecisionMachine U) (M : MERAFamily) : Prop :=
  DecidesSAT U D → ∀ n,
    Nonempty (MERAQueryTranscript (independentSATQueryFamily n) D M)

/-- No SAT decider has an all-size independent-query compiler into one fixed bounded-bond,
fixed-cone, logarithmic-depth MERA family. -/
theorem not_decidesSAT_of_independentQueryCompiler
    {U : MachineModel} {D : DecisionMachine U} (M : MERAFamily)
    (hcompile : SATCorrectnessCompilesIndependentQueries U D M) :
    ¬ DecidesSAT U D := by
  intro hD
  obtain ⟨n, hn, hnone⟩ :=
    DynamicHolonomyMERADecoder.exists_size_without_dynamicHolonomyDecoder M
  obtain ⟨T⟩ := hcompile hD n
  exact hnone ⟨T.toDynamicHolonomyDecoder hD⟩

/-- Explicit restricted class singled out by the two completed bridges. -/
def HasIndependentSATQueryRestrictedMERA
    (U : MachineModel) (D : DecisionMachine U) : Prop :=
  ∃ M : MERAFamily, SATCorrectnessCompilesIndependentQueries U D M

/-- **Restricted lower bound.**  No machine whose independent SAT-query transcripts uniformly fit one
fixed bounded-MERA family decides SAT. -/
theorem no_SAT_decider_with_independentQueryRestrictedMERA {U : MachineModel} :
    ¬ ∃ D : DecisionMachine U,
      HasIndependentSATQueryRestrictedMERA U D ∧ DecidesSAT U D := by
  rintro ⟨D, ⟨M, hcompile⟩, hD⟩
  exact (not_decidesSAT_of_independentQueryCompiler M hcompile) hD

/-!
## Honest endpoint

Both previously named restricted bridges are now concrete:

1. `independentSATQueryFamily` is a genuine solver-independent SAT-query family, every coordinate is
   SAT-hard, and all holonomy signatures occur without placing answer bits in the query syntax.
2. `MERAQueryTranscript.toDynamicHolonomyDecoder` is the promised compilation from a certified batch
   transcript to the time-indexed bounded-MERA decoder.

The surviving boundary is architectural, not semantic: arbitrary polynomial-time SAT machines are not
known to realize their independent query batches inside one fixed-bond, logarithmic-depth local MERA.
`SATCorrectnessCompilesIndependentQueries` names exactly that restricted-class assumption; asserting it
for every polynomial-time machine would go beyond what was proved here.
-/

end PallLean.Paper93.DeepMath.PathB.PvsNPDynamicHolonomyQueryTranscriptBridge

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicHolonomyQueryTranscriptBridge.SAT_reduces_to_independent_coordinate
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicHolonomyQueryTranscriptBridge.independent_coordinate_reduces_to_SAT
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicHolonomyQueryTranscriptBridge.MERAQueryTranscript.toDynamicHolonomyDecoder
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicHolonomyQueryTranscriptBridge.MERAQueryTranscript.stateAt_injective
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicHolonomyQueryTranscriptBridge.MERAQueryTranscript.no_transcript_at_size
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicHolonomyQueryTranscriptBridge.not_decidesSAT_of_independentQueryCompiler
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicHolonomyQueryTranscriptBridge.no_SAT_decider_with_independentQueryRestrictedMERA
