import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderCrossingContinuationHolonomy
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPDynamicHolonomyQueryTranscriptBridge

/-!
# Expander residuals separated by explicit future SAT queries

The expander/crossing theorem leaves its semantic premise explicit: different
Tseitin residual vectors must be distinguished by genuine future decisions.
This file discharges that premise for a concrete family of SAT continuations.

An expander residual is decoded into its Boolean coordinates.  Future suffix
`i` asks a concrete SAT query whose satisfiability is exactly coordinate `i`.
Therefore every SAT-correct decider separates two different residual vectors on
some suffix.  Feeding this fact into the crossing theorem yields the exact
capacity bound and its no-small-cut form.

The resulting run is the extensional query-answer run, not a claim that the
internal execution of every SAT solver factors through a small spatial cut.
That distinction is load-bearing: the repository's crossing-bottleneck no-go
rules out a universal small-cut normal form for polynomial-time computations.
-/

namespace PallLean.Paper93.DeepMath.PathB.ExpanderSATQueryContinuation

open SATDepthMachine
open PvsNPRunIndexedFaithfulTPhi
open PvsNPDynamicHolonomyDecisionRelevance
open PvsNPDynamicHolonomyDecisionRelevance.SATQueryHolonomyFamily
open PvsNPDynamicHolonomyQueryTranscriptBridge
open CrossingSequenceContinuationHolonomy
open ExpanderCrossingContinuationHolonomy

variable {V Edge ι : Type}
variable [Fintype V] [DecidableEq V]
variable [Fintype Edge] [DecidableEq Edge]
variable [Fintype ι] [DecidableEq ι]

/-- Canonical conversion between the finite residual code and its Boolean
coordinate vector. -/
noncomputable def residualBitsEquiv (n : Nat) :
    Fin (2 ^ n) ≃ (Fin n → Bool) := by
  have hcard : Fintype.card (Fin n → Bool) = 2 ^ n := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  exact (Fintype.equivFinOfCardEq hcard).symm

/-- Boolean coordinates of the natural expander/Tseitin residual. -/
noncomputable def expanderResidualBits
    (G : TseitinGraph V Edge) (readSet : ι → V) :
    (Edge → ZMod 2) → (Fin (Fintype.card ι) → Bool) :=
  fun x => residualBitsEquiv (Fintype.card ι) (expanderResidual G readSet x)

theorem expanderResidualBits_surjective
    (G : TseitinGraph V Edge) {c : Nat} (hc : 1 ≤ c)
    (hexp : G.HasExpansion c)
    (readSet : ι → V) (hread : Function.Injective readSet)
    (hmed : 2 * Fintype.card ι ≤ Fintype.card V) :
    Function.Surjective (expanderResidualBits G readSet) := by
  exact (residualBitsEquiv (Fintype.card ι)).surjective.comp
    (expanderResidual_surjective G hc hexp readSet hread hmed)

/-- A solver-independent SAT-query family exposing every coordinate of the
natural expander residual.  The query is a concrete satisfiable or
unsatisfiable CNF selected by the corresponding linear parity coordinate. -/
noncomputable def expanderResidualSATQueries
    (G : TseitinGraph V Edge) {c : Nat} (hc : 1 ≤ c)
    (hexp : G.HasExpansion c)
    (readSet : ι → V) (hread : Function.Injective readSet)
    (hmed : 2 * Fintype.card ι ≤ Fintype.card V) :
    SATQueryHolonomyFamily (Fintype.card ι) where
  Instance := Edge → ZMod 2
  label := expanderResidualBits G readSet
  query := fun x i => if expanderResidualBits G readSet x i then yesCNF else noCNF
  query_sat_iff := by
    intro x i
    cases h : expanderResidualBits G readSet x i <;>
      simp [yesCNF_satisfiable, noCNF_not_satisfiable]
  label_surjective :=
    expanderResidualBits_surjective G hc hexp readSet hread hmed

/-- The extensional future-query run: suffix `i` asks the SAT decider for the
`i`th residual coordinate.  It records genuine SAT decisions while making no
claim about the decider's internal spatial trace. -/
noncomputable def expanderSATQueryRun
    {U : MachineModel} (D : DecisionMachine U)
    (G : TseitinGraph V Edge) {c : Nat} (hc : 1 ≤ c)
    (hexp : G.HasExpansion c)
    (readSet : ι → V) (hread : Function.Injective readSet)
    (hmed : 2 * Fintype.card ι ≤ Fintype.card V) :
    ActualDecisionRun
      ((Edge → ZMod 2) × Option (Fin (Fintype.card ι)))
      ((Edge → ZMod 2) × Option (Fin (Fintype.card ι))) where
  encode := id
  step := fun _ state => state
  steps := 0
  observe := fun xi => match xi.2 with
    | none => false
    | some i =>
      (expanderResidualSATQueries G hc hexp readSet hread hmed).answers D xi.1 i

/-- SAT correctness makes distinct natural residual vectors distinguishable by
an explicit future coordinate query. -/
theorem expanderResidual_separated_by_future_SAT_query
    {U : MachineModel} (D : DecisionMachine U) (hD : DecidesSAT U D)
    (G : TseitinGraph V Edge) {c : Nat} (hc : 1 ≤ c)
    (hexp : G.HasExpansion c)
    (readSet : ι → V) (hread : Function.Injective readSet)
    (hmed : 2 * Fintype.card ι ≤ Fintype.card V)
    {x y : Edge → ZMod 2}
    (hxy : expanderResidual G readSet x ≠ expanderResidual G readSet y) :
    ∃ i : Option (Fin (Fintype.card ι)),
      (expanderSATQueryRun D G hc hexp readSet hread hmed).finalAnswer (x, i) ≠
      (expanderSATQueryRun D G hc hexp readSet hread hmed).finalAnswer (y, i) := by
  let F := expanderResidualSATQueries G hc hexp readSet hread hmed
  have hbits : F.label x ≠ F.label y := by
    intro heq
    exact hxy ((residualBitsEquiv (Fintype.card ι)).injective heq)
  have hcoord : ∃ i, F.label x i ≠ F.label y i := by
    by_contra h
    push_neg at h
    exact hbits (funext h)
  obtain ⟨i, hi⟩ := hcoord
  refine ⟨some i, ?_⟩
  have hx := congrFun (F.answers_eq_label D hD x) i
  have hy := congrFun (F.answers_eq_label D hD y) i
  simpa [expanderSATQueryRun, ActualDecisionRun.finalAnswer,
    ActualDecisionRun.stateAt, F] using (show F.answers D x i ≠ F.answers D y i by
      intro heq
      exact hi (hx.symm.trans (heq.trans hy)))

/-- **Concrete adaptive-rereading bound.**  Any continuation-complete crossing
factorization of the actual SAT-query decisions must have capacity for every
expander residual. -/
theorem expander_SAT_query_capacity_le_crossing_capacity
    {U : MachineModel} (D : DecisionMachine U) (hD : DecidesSAT U D)
    (G : TseitinGraph V Edge) {c : Nat} (hc : 1 ≤ c)
    (hexp : G.HasExpansion c)
    (readSet : ι → V) (hread : Function.Injective readSet)
    (hmed : 2 * Fintype.card ι ≤ Fintype.card V)
    {g crossingWidth q : Nat}
    (F : CrossingSequenceTraceFactorization
      (expanderSATQueryRun D G hc hexp readSet hread hmed)
      g crossingWidth q) :
    2 ^ Fintype.card ι ≤ q ^ crossingWidth := by
  exact expander_residual_capacity_le_crossing_capacity
    G hc hexp readSet hread hmed F
    (fun _ _ hxy =>
      expanderResidual_separated_by_future_SAT_query
        D hD G hc hexp readSet hread hmed hxy)

/-- Below residual capacity, no solver-specific crossing cut can carry these
explicit future SAT decisions. -/
theorem no_expander_SAT_query_cut_below_capacity
    {U : MachineModel} (D : DecisionMachine U) (hD : DecidesSAT U D)
    (G : TseitinGraph V Edge) {c : Nat} (hc : 1 ≤ c)
    (hexp : G.HasExpansion c)
    (readSet : ι → V) (hread : Function.Injective readSet)
    (hmed : 2 * Fintype.card ι ≤ Fintype.card V)
    {g crossingWidth q : Nat}
    (hgap : q ^ crossingWidth < 2 ^ Fintype.card ι) :
    ¬ Nonempty (CrossingSequenceTraceFactorization
      (expanderSATQueryRun D G hc hexp readSet hread hmed)
      g crossingWidth q) := by
  rintro ⟨F⟩
  exact (Nat.not_le_of_lt hgap)
    (expander_SAT_query_capacity_le_crossing_capacity
      D hD G hc hexp readSet hread hmed F)

/-- The exact output a proposed solver-specific small-cut selector would have
to manufacture at this scale.  Bundling the factorization with its strict gap
makes the forbidden premise visible instead of hiding it in a normal-form
axiom. -/
structure SmallExpanderSATQueryCut
    {U : MachineModel} (D : DecisionMachine U)
    (G : TseitinGraph V Edge) {c : Nat} (hc : 1 ≤ c)
    (hexp : G.HasExpansion c)
    (readSet : ι → V) (hread : Function.Injective readSet)
    (hmed : 2 * Fintype.card ι ≤ Fintype.card V) : Type where
  generators : Nat
  crossingWidth : Nat
  controlStates : Nat
  factorization : CrossingSequenceTraceFactorization
    (expanderSATQueryRun D G hc hexp readSet hread hmed)
    generators crossingWidth controlStates
  belowResidualCapacity :
    controlStates ^ crossingWidth < 2 ^ Fintype.card ι

/-- **Cut-selection audit.**  SAT correctness rules out the output demanded by
any below-capacity selector.  Thus a purported construction of this object from
an arbitrary polynomial SAT solver cannot be harmless trace plumbing: together
with correctness it is already contradictory at the expander scale. -/
theorem no_small_expander_SAT_query_cut
    {U : MachineModel} (D : DecisionMachine U) (hD : DecidesSAT U D)
    (G : TseitinGraph V Edge) {c : Nat} (hc : 1 ≤ c)
    (hexp : G.HasExpansion c)
    (readSet : ι → V) (hread : Function.Injective readSet)
    (hmed : 2 * Fintype.card ι ≤ Fintype.card V) :
    SmallExpanderSATQueryCut D G hc hexp readSet hread hmed → False := by
  rintro ⟨g, crossingWidth, q, F, hgap⟩
  exact (Nat.not_le_of_lt hgap)
    (expander_SAT_query_capacity_le_crossing_capacity
      D hD G hc hexp readSet hread hmed F)

end PallLean.Paper93.DeepMath.PathB.ExpanderSATQueryContinuation

#print axioms PallLean.Paper93.DeepMath.PathB.ExpanderSATQueryContinuation.expanderResidual_separated_by_future_SAT_query
#print axioms PallLean.Paper93.DeepMath.PathB.ExpanderSATQueryContinuation.expander_SAT_query_capacity_le_crossing_capacity
#print axioms PallLean.Paper93.DeepMath.PathB.ExpanderSATQueryContinuation.no_expander_SAT_query_cut_below_capacity
#print axioms PallLean.Paper93.DeepMath.PathB.ExpanderSATQueryContinuation.no_small_expander_SAT_query_cut
