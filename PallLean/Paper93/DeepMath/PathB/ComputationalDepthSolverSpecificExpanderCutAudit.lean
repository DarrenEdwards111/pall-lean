import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderSATQueryContinuation

/-!
# Solver-specific expander cut selection: construction and exact frontier

This file tests the final Route-G cut selector rather than assuming it.

There is an unconditional full-width factorization of the extensional expander
SAT-query run: expose all `r` residual coordinates and use the same `r` bits as
a crossing word over two symbols.  This is continuation-complete and has exact
capacity `2^r`.  Thus the observer/God-Move language is operational, but it has
not compressed anything.

The desired selector would instead return a factorization strictly below that
capacity for every SAT-correct decider.  At a fixed expander gap, this statement
is proved equivalent to the absence of any SAT-correct decider in the supplied
machine model.  Hence the missing selector is exactly separation-strength; it
cannot be obtained by generic minimization, diagonal choice, or trace plumbing.
-/

namespace PallLean.Paper93.DeepMath.PathB.SolverSpecificExpanderCutAudit

open SATDepthMachine
open PvsNPRunIndexedFaithfulTPhi
open PvsNPDynamicHolonomyDecisionRelevance
open PvsNPDynamicHolonomyDecisionRelevance.SATQueryHolonomyFamily
open TraceDynamicsContinuationBridge
open CrossingSequenceContinuationHolonomy
open ExpanderCrossingContinuationHolonomy
open ExpanderSATQueryContinuation

variable {V Edge ι : Type}
variable [Fintype V] [DecidableEq V]
variable [Fintype Edge] [DecidableEq Edge]
variable [Fintype ι] [DecidableEq ι]

/-- Expose every residual bit at the prefix boundary.  SAT correctness supplies
the exact finishing law for every future coordinate query. -/
noncomputable def fullResidualTraceFactorization
    {U : MachineModel} (D : DecisionMachine U) (hD : DecidesSAT U D)
    (G : TseitinGraph V Edge) {c : Nat} (hc : 1 ≤ c)
    (hexp : G.HasExpansion c)
    (readSet : ι → V) (hread : Function.Injective readSet)
    (hmed : 2 * Fintype.card ι ≤ Fintype.card V) :
    TraceContinuationFactorization
      (expanderSATQueryRun D G hc hexp readSet hread hmed)
      (Fintype.card ι) where
  time := 0
  time_le := by simp [expanderSATQueryRun]
  expose := fun state => expanderResidualBits G readSet state.1
  prefixStable := by
    intro p s t
    rfl
  finish := fun signature suffix => match suffix with
    | none => false
    | some i => signature i
  finishCorrect := by
    intro p suffix
    cases suffix with
    | none => rfl
    | some i =>
      let F := expanderResidualSATQueries G hc hexp readSet hread hmed
      have hi := congrFun (F.answers_eq_label D hD p) i
      simpa [expanderSATQueryRun, ActualDecisionRun.finalAnswer,
        ActualDecisionRun.stateAt, F] using hi.symm

/-- Encode one Boolean residual coordinate as one of two crossing symbols. -/
def boolCrossingSymbol (b : Bool) : Fin 2 :=
  if b then 1 else 0

theorem boolCrossingSymbol_injective : Function.Injective boolCrossingSymbol := by
  intro a b h
  cases a <;> cases b <;> simp [boolCrossingSymbol] at h ⊢

/-- **Constructive full-width God Move.**  The actual future-query semantics
always factor through the complete `r`-bit residual word.  This selector is
sound but pays the full residual width. -/
noncomputable def fullWidthCrossingFactorization
    {U : MachineModel} (D : DecisionMachine U) (hD : DecidesSAT U D)
    (G : TseitinGraph V Edge) {c : Nat} (hc : 1 ≤ c)
    (hexp : G.HasExpansion c)
    (readSet : ι → V) (hread : Function.Injective readSet)
    (hmed : 2 * Fintype.card ι ≤ Fintype.card V) :
    CrossingSequenceTraceFactorization
      (expanderSATQueryRun D G hc hexp readSet hread hmed)
      (Fintype.card ι) (Fintype.card ι) 2 where
  trace := fullResidualTraceFactorization
    D hD G hc hexp readSet hread hmed
  crossingView := fun x i => boolCrossingSymbol (expanderResidualBits G readSet x i)
  crossingDeterminesSignature := by
    intro x y hview
    change expanderResidualBits G readSet x = expanderResidualBits G readSet y
    funext i
    exact boolCrossingSymbol_injective (congrFun hview i)

/-- A uniform below-capacity selector at one concrete expander scale.  This is
the precise solver-specific theorem Route G would need in the supplied machine
model `U`. -/
structure SmallCutSelectorAt
    (U : MachineModel)
    (G : TseitinGraph V Edge) {c : Nat} (hc : 1 ≤ c)
    (hexp : G.HasExpansion c)
    (readSet : ι → V) (hread : Function.Injective readSet)
    (hmed : 2 * Fintype.card ι ≤ Fintype.card V) : Type where
  select : ∀ D : DecisionMachine U, DecidesSAT U D →
    SmallExpanderSATQueryCut D G hc hexp readSet hread hmed

/-- A below-capacity selector rules out every SAT-correct decider in its machine
model. -/
theorem no_SAT_decider_of_smallCutSelectorAt
    (U : MachineModel)
    (G : TseitinGraph V Edge) {c : Nat} (hc : 1 ≤ c)
    (hexp : G.HasExpansion c)
    (readSet : ι → V) (hread : Function.Injective readSet)
    (hmed : 2 * Fintype.card ι ≤ Fintype.card V)
    (S : SmallCutSelectorAt U G hc hexp readSet hread hmed) :
    ¬ ∃ D : DecisionMachine U, DecidesSAT U D := by
  rintro ⟨D, hD⟩
  exact no_small_expander_SAT_query_cut
    D hD G hc hexp readSet hread hmed (S.select D hD)

/-- Conversely, if the model has no SAT decider, the selector exists only
vacuously. -/
noncomputable def smallCutSelectorAt_of_no_SAT_decider
    (U : MachineModel)
    (G : TseitinGraph V Edge) {c : Nat} (hc : 1 ≤ c)
    (hexp : G.HasExpansion c)
    (readSet : ι → V) (hread : Function.Injective readSet)
    (hmed : 2 * Fintype.card ι ≤ Fintype.card V)
    (hno : ¬ ∃ D : DecisionMachine U, DecidesSAT U D) :
    SmallCutSelectorAt U G hc hexp readSet hread hmed where
  select D hD := False.elim (hno ⟨D, hD⟩)

/-- **Exact frontier theorem.**  At the expander gap, constructing the desired
solver-specific small-cut selector is logically equivalent to the no-SAT-
decider endpoint for the machine model. -/
theorem smallCutSelectorAt_iff_no_SAT_decider
    (U : MachineModel)
    (G : TseitinGraph V Edge) {c : Nat} (hc : 1 ≤ c)
    (hexp : G.HasExpansion c)
    (readSet : ι → V) (hread : Function.Injective readSet)
    (hmed : 2 * Fintype.card ι ≤ Fintype.card V) :
    Nonempty (SmallCutSelectorAt U G hc hexp readSet hread hmed) ↔
      ¬ ∃ D : DecisionMachine U, DecidesSAT U D := by
  constructor
  · rintro ⟨S⟩
    exact no_SAT_decider_of_smallCutSelectorAt
      U G hc hexp readSet hread hmed S
  · intro hno
    exact ⟨smallCutSelectorAt_of_no_SAT_decider
      U G hc hexp readSet hread hmed hno⟩

end PallLean.Paper93.DeepMath.PathB.SolverSpecificExpanderCutAudit

#print axioms PallLean.Paper93.DeepMath.PathB.SolverSpecificExpanderCutAudit.fullResidualTraceFactorization
#print axioms PallLean.Paper93.DeepMath.PathB.SolverSpecificExpanderCutAudit.fullWidthCrossingFactorization
#print axioms PallLean.Paper93.DeepMath.PathB.SolverSpecificExpanderCutAudit.no_SAT_decider_of_smallCutSelectorAt
#print axioms PallLean.Paper93.DeepMath.PathB.SolverSpecificExpanderCutAudit.smallCutSelectorAt_iff_no_SAT_decider
