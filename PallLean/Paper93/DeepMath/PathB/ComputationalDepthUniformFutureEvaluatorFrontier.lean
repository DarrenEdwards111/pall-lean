import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSuccinctFutureContinuationResourceAudit

/-!
# Uniform future-evaluator frontier

The semantic continuation quotient and its succinct bit presentation are both
fully calibrated.  The only remaining possible cost is uniform computation:
given the original syntax of a legal SAT continuation, compute its answer
within the machine model's polynomial budget.

This file makes that frontier exact.  A uniform future-query evaluator is one
polynomial-budget decision machine that answers every coordinate of every
solver-independent `SATQueryHolonomyFamily`.  Such an evaluator is equivalent
to polynomial-time SAT decision in the supplied machine model.  The reverse
direction uses SAT correctness directly; the forward direction needs only the
one-coordinate independent family whose query is literally an arbitrary input
CNF.

The file also exposes a decisive weakness of the expander coordinate family
used by the preceding audits.  Its queries are selected from the fixed pair
`yesCNF`/`noCNF` after the residual bit has already been computed.  A trivial
syntactic evaluator distinguishes those two formulas.  Thus that family is
excellent for calibrating continuation faithfulness, capacity, and quotient
width, but it cannot carry a uniform SAT lower bound: the hard semantic bit is
embedded by the query constructor before the evaluator runs.
-/

namespace PallLean.Paper93.DeepMath.PathB.UniformFutureEvaluatorFrontier

open SATDepthMachine
open PvsNPDynamicHolonomyDecisionRelevance
open PvsNPDynamicHolonomyDecisionRelevance.SATQueryHolonomyFamily
open PvsNPDynamicHolonomyQueryTranscriptBridge
open ExpanderSATQueryContinuation

/-! ## Uniform evaluator equals SAT decision -/

/-- One polynomial-budget machine uniformly evaluates every genuine
solver-independent SAT future query. -/
structure UniformFutureQueryEvaluator (U : MachineModel) where
  machine : DecisionMachine U
  correct : ∀ (n : ℕ) (F : SATQueryHolonomyFamily n)
    (x : F.Instance) (i : Fin n),
    U.decisionRun machine.code (F.query x i) = F.label x i

/-- Any SAT-correct polynomial-budget decider is a uniform evaluator for all
future-query families. -/
def uniformFutureQueryEvaluatorOfDecider
    {U : MachineModel} (D : DecisionMachine U) (hD : DecidesSAT U D) :
    UniformFutureQueryEvaluator U where
  machine := D
  correct := by
    intro n F x i
    exact congrFun (F.answers_eq_label D hD x) i

/-- Conversely, the one-coordinate independent query family feeds an
arbitrary CNF unchanged to the evaluator, so uniform future evaluation already
decides all of SAT. -/
theorem UniformFutureQueryEvaluator.decidesSAT
    {U : MachineModel} (E : UniformFutureQueryEvaluator U) :
    DecidesSAT U E.machine := by
  intro φ
  let batch : Fin 1 → CNF := fun _ => φ
  have h := E.correct 1 (independentSATQueryFamily 1) batch (0 : Fin 1)
  change U.decisionRun E.machine.code φ = satTruth φ at h
  rw [h]
  exact satTruth_eq_true_iff φ

/-- **Exact uniform frontier.**  A polynomial uniform evaluator of genuine SAT
future syntax exists iff SAT has a polynomial-budget decider in the machine
model. -/
theorem uniformFutureQueryEvaluator_iff_SATDecisionInP (U : MachineModel) :
    Nonempty (UniformFutureQueryEvaluator U) ↔ SATDecisionInP U := by
  constructor
  · rintro ⟨E⟩
    exact ⟨E.machine, E.decidesSAT⟩
  · rintro ⟨D, hD⟩
    exact ⟨uniformFutureQueryEvaluatorOfDecider D hD⟩

/-- The desired superpolynomial uniform-evaluation lower bound is exactly the
no-polynomial-SAT-decider statement, not an intermediate quotient lemma. -/
theorem no_uniformFutureQueryEvaluator_iff_no_SATDecisionInP
    (U : MachineModel) :
    (¬ Nonempty (UniformFutureQueryEvaluator U)) ↔ ¬ SATDecisionInP U := by
  rw [uniformFutureQueryEvaluator_iff_SATDecisionInP]

/-! ## The expander coordinate queries are syntactically trivial -/

/-- A constant-time-style syntactic observer for the two fixed calibration
formulas: accept exactly when the clause list is empty. -/
def yesNoSyntacticEvaluator (φ : CNF) : Bool :=
  φ.clauses.isEmpty

@[simp] theorem yesNoSyntacticEvaluator_yesCNF :
    yesNoSyntacticEvaluator yesCNF = true := by
  rfl

@[simp] theorem yesNoSyntacticEvaluator_noCNF :
    yesNoSyntacticEvaluator noCNF = false := by
  rfl

variable {V Edge ι : Type}
variable [Fintype V] [DecidableEq V]
variable [Fintype Edge] [DecidableEq Edge]
variable [Fintype ι] [DecidableEq ι]

/-- Every expander coordinate query is literally one of the two fixed
calibration formulas. -/
theorem expanderQuery_eq_yesCNF_or_noCNF
    (G : TseitinGraph V Edge) {c : ℕ} (hc : 1 ≤ c)
    (hexp : G.HasExpansion c)
    (readSet : ι → V) (hread : Function.Injective readSet)
    (hmed : 2 * Fintype.card ι ≤ Fintype.card V)
    (x : Edge → ZMod 2) (i : Fin (Fintype.card ι)) :
    (expanderResidualSATQueries G hc hexp readSet hread hmed).query x i = yesCNF ∨
      (expanderResidualSATQueries G hc hexp readSet hread hmed).query x i = noCNF := by
  cases hbit : expanderResidualBits G readSet x i
  · right
    simp [expanderResidualSATQueries, hbit]
  · left
    simp [expanderResidualSATQueries, hbit]

/-- The trivial clause-list observer recovers every expander coordinate label;
no SAT solver is needed after the query constructor has selected `yesCNF` or
`noCNF`. -/
theorem yesNoSyntacticEvaluator_correct_on_expanderQueries
    (G : TseitinGraph V Edge) {c : ℕ} (hc : 1 ≤ c)
    (hexp : G.HasExpansion c)
    (readSet : ι → V) (hread : Function.Injective readSet)
    (hmed : 2 * Fintype.card ι ≤ Fintype.card V)
    (x : Edge → ZMod 2) (i : Fin (Fintype.card ι)) :
    yesNoSyntacticEvaluator
        ((expanderResidualSATQueries G hc hexp readSet hread hmed).query x i) =
      (expanderResidualSATQueries G hc hexp readSet hread hmed).label x i := by
  cases hbit : expanderResidualBits G readSet x i <;>
    simp [expanderResidualSATQueries, yesNoSyntacticEvaluator,
      yesCNF, noCNF, hbit]

/-- Package an abstract evaluator for one query family, without claiming a
machine-level resource bound. -/
structure FamilyEvaluator {n : ℕ} (F : SATQueryHolonomyFamily n) where
  evaluate : CNF → Bool
  correct : ∀ x i, evaluate (F.query x i) = F.label x i

/-- The expander family has a solver-free family evaluator because its query
constructor has already encoded the answer into the yes/no syntax. -/
noncomputable def expanderFamilyEvaluator
    (G : TseitinGraph V Edge) {c : ℕ} (hc : 1 ≤ c)
    (hexp : G.HasExpansion c)
    (readSet : ι → V) (hread : Function.Injective readSet)
    (hmed : 2 * Fintype.card ι ≤ Fintype.card V) :
    FamilyEvaluator
      (expanderResidualSATQueries G hc hexp readSet hread hmed) where
  evaluate := yesNoSyntacticEvaluator
  correct := yesNoSyntacticEvaluator_correct_on_expanderQueries
    G hc hexp readSet hread hmed

/-! ## Why genuine syntax is load-bearing -/

/-- An evaluator for the one-coordinate independent family decides arbitrary
SAT semantically, even before any machine-cost claim is imposed. -/
theorem familyEvaluator_independent_one_decides_satisfiability
    (E : FamilyEvaluator (independentSATQueryFamily 1))
    (φ : CNF) :
    E.evaluate φ = true ↔ Satisfiable φ := by
  let batch : Fin 1 → CNF := fun _ => φ
  have h := E.correct batch (0 : Fin 1)
  change E.evaluate φ = satTruth φ at h
  rw [h]
  exact satTruth_eq_true_iff φ

/-!
## Audit verdict

Uniform computation is the first resource in this Route-G sequence that does
not collapse to a small residual code.  It also does not create a shortcut:
for solver-independent genuine SAT queries, a polynomial uniform evaluator is
definitionally and theorem-level equivalent to a polynomial SAT decider.

The current expander coordinate queries cannot establish a uniform lower
bound, because they are answer-coded `yesCNF`/`noCNF` tests and have the
explicit trivial syntactic evaluator above.  Replacing them with arbitrary
genuine CNFs gives the independent query family, but then ruling out a
polynomial evaluator is exactly ruling out polynomial-time SAT.

Hence the remaining frontier is no longer a missing action, quotient,
observer, or compilation construction.  It is the original general lower
bound itself.  Any further Route-G claim must introduce genuinely new
complexity-lower-bound mathematics rather than another semantic repackaging.
-/

end PallLean.Paper93.DeepMath.PathB.UniformFutureEvaluatorFrontier

#print axioms PallLean.Paper93.DeepMath.PathB.UniformFutureEvaluatorFrontier.UniformFutureQueryEvaluator.decidesSAT
#print axioms PallLean.Paper93.DeepMath.PathB.UniformFutureEvaluatorFrontier.uniformFutureQueryEvaluator_iff_SATDecisionInP
#print axioms PallLean.Paper93.DeepMath.PathB.UniformFutureEvaluatorFrontier.no_uniformFutureQueryEvaluator_iff_no_SATDecisionInP
#print axioms PallLean.Paper93.DeepMath.PathB.UniformFutureEvaluatorFrontier.expanderQuery_eq_yesCNF_or_noCNF
#print axioms PallLean.Paper93.DeepMath.PathB.UniformFutureEvaluatorFrontier.yesNoSyntacticEvaluator_correct_on_expanderQueries
#print axioms PallLean.Paper93.DeepMath.PathB.UniformFutureEvaluatorFrontier.familyEvaluator_independent_one_decides_satisfiability
