import PallLean.Paper93.DeepMath.PathB.ComputationalDepthContextualBubbleAdaptiveMemoryAudit
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUniformFutureEvaluatorFrontier

/-!
# Contextual summary invalidation frontier

The adaptive-memory audit showed that counting continuation sections is not
enough: an observer can cache a polynomial description instead of enumerating
all semantic states.  The next proposal is to charge context changes whenever
they invalidate that cached summary.

This file tests the strongest immediate escape.  The observer stores the exact
encoded CNF syntax and updates it by genuine variable restriction.  Restriction
never increases encoded length, and an arbitrary path of context changes keeps
a correct exact summary whose size is bounded by the original formula.  Thus
summary invalidation, measured only as loss or growth of the representation,
is zero for a canonical polynomial-size cache.

What remains is evaluating the cached summary uniformly.  Combining the exact
summary with a polynomial uniform evaluator is proved equivalent to polynomial
SAT decision in the supplied machine model.  Hence invalidation alone supplies
no new lower-bound bridge; a useful thermodynamic cost must charge the work of
updating/evaluating context-sensitive summaries in a way that cannot be evaded
by retaining the syntax.
-/

namespace PallLean.Paper93.DeepMath.PathB.ContextualSummaryInvalidationFrontier

open CNFSelfReduction
open SATDepthMachine
open UniformFutureEvaluatorFrontier

/-- A finite path through nested observer bubbles, represented by successive
variable restrictions. -/
abbrev RestrictionStep (n : ℕ) := Fin n × Bool

def restrictAlong {n : ℕ} : CNF n → List (RestrictionStep n) → CNF n
  | φ, [] => φ
  | φ, step :: rest => restrictAlong (restrict φ step.1 step.2) rest

/-- Exact CNF syntax remains polynomially bounded under every context path:
restriction never grows the cached representation. -/
theorem restrictAlong_descLen_le {n : ℕ}
    (φ : CNF n) (path : List (RestrictionStep n)) :
    descLen (restrictAlong φ path) ≤ descLen φ := by
  induction path generalizing φ with
  | nil => exact Nat.le_refl _
  | cons step rest ih =>
      exact Nat.le_trans (ih (restrict φ step.1 step.2))
        (restrict_descLen_le φ step.1 step.2)

/-- An observer summary scheme for nested CNF restriction contexts. -/
structure RestrictionSummaryScheme (n : ℕ) where
  Summary : Type
  summarize : CNF n → Summary
  advance : Summary → RestrictionStep n → Summary
  realize : Summary → CNF n
  size : Summary → ℕ
  realize_summarize : ∀ φ, realize (summarize φ) = φ
  realize_advance : ∀ s step,
    realize (advance s step) = restrict (realize s) step.1 step.2
  size_summarize : ∀ φ, size (summarize φ) = descLen φ
  size_advance_le : ∀ s step, size (advance s step) ≤ size s

/-- The canonical context-stable summary is simply the exact current CNF. -/
def exactSyntaxSummaryScheme (n : ℕ) : RestrictionSummaryScheme n where
  Summary := CNF n
  summarize := fun φ ↦ φ
  advance := fun φ step ↦ restrict φ step.1 step.2
  realize := fun φ ↦ φ
  size := descLen
  realize_summarize := fun _ ↦ rfl
  realize_advance := fun _ _ ↦ rfl
  size_summarize := fun _ ↦ rfl
  size_advance_le := fun φ step ↦ restrict_descLen_le φ step.1 step.2

def RestrictionSummaryScheme.advanceAlong {n : ℕ}
    (S : RestrictionSummaryScheme n) :
    S.Summary → List (RestrictionStep n) → S.Summary
  | s, [] => s
  | s, step :: rest => S.advanceAlong (S.advance s step) rest

theorem RestrictionSummaryScheme.realize_advanceAlong {n : ℕ}
    (S : RestrictionSummaryScheme n) (s : S.Summary)
    (path : List (RestrictionStep n)) :
    S.realize (S.advanceAlong s path) = restrictAlong (S.realize s) path := by
  induction path generalizing s with
  | nil => rfl
  | cons step rest ih =>
      rw [RestrictionSummaryScheme.advanceAlong, ih, S.realize_advance]
      rfl

theorem RestrictionSummaryScheme.size_advanceAlong_le {n : ℕ}
    (S : RestrictionSummaryScheme n) (s : S.Summary)
    (path : List (RestrictionStep n)) :
    S.size (S.advanceAlong s path) ≤ S.size s := by
  induction path generalizing s with
  | nil => exact Nat.le_refl _
  | cons step rest ih =>
      exact Nat.le_trans (ih (S.advance s step)) (S.size_advance_le s step)

/-- Representation invalidation growth: extra summary space forced by one
context change.  This deliberately measures invalidation of the cached
representation, not the runtime needed to evaluate SAT. -/
def RestrictionSummaryScheme.invalidationGrowth {n : ℕ}
    (S : RestrictionSummaryScheme n) (s : S.Summary)
    (step : RestrictionStep n) : ℕ :=
  S.size (S.advance s step) - S.size s

/-- Every canonical syntax update has zero representation-growth invalidation. -/
theorem exactSyntaxSummary_invalidationGrowth_zero {n : ℕ}
    (φ : CNF n) (step : RestrictionStep n) :
    (exactSyntaxSummaryScheme n).invalidationGrowth φ step = 0 := by
  exact Nat.sub_eq_zero_of_le (restrict_descLen_le φ step.1 step.2)

/-- Exact stable summaries exist uniformly at every variable count. -/
def HasUniformStableExactSummary : Prop :=
  ∀ n : ℕ, Nonempty (RestrictionSummaryScheme n)

theorem hasUniformStableExactSummary : HasUniformStableExactSummary := by
  intro n
  exact ⟨exactSyntaxSummaryScheme n⟩

/-- Stable syntax plus uniform polynomial evaluation.  The first component is
unconditional; all computational hardness is isolated in the evaluator. -/
def StableSummaryWithUniformEvaluator (U : MachineModel) : Prop :=
  HasUniformStableExactSummary ∧ Nonempty (UniformFutureQueryEvaluator U)

/-- **Exact frontier.**  Context-stable polynomial-size summaries plus a
polynomial uniform evaluator exist iff SAT has a polynomial-budget decider.
Stable caching does not weaken the remaining lower-bound obligation. -/
theorem stableSummaryWithUniformEvaluator_iff_SATDecisionInP
    (U : MachineModel) :
    StableSummaryWithUniformEvaluator U ↔ SATDecisionInP U := by
  constructor
  · rintro ⟨_, hEval⟩
    exact (uniformFutureQueryEvaluator_iff_SATDecisionInP U).1 hEval
  · intro hSAT
    exact ⟨hasUniformStableExactSummary,
      (uniformFutureQueryEvaluator_iff_SATDecisionInP U).2 hSAT⟩

/-- The hoped-for lower bound after granting stable exact summaries is still
exactly the no-polynomial-SAT-decider statement. -/
theorem no_stableSummaryWithUniformEvaluator_iff_no_SATDecisionInP
    (U : MachineModel) :
    (¬ StableSummaryWithUniformEvaluator U) ↔ ¬ SATDecisionInP U := by
  rw [stableSummaryWithUniformEvaluator_iff_SATDecisionInP]

/-!
## Audit verdict

Exact CNF syntax is a globally reusable summary across every nested restriction
bubble.  Its representation never grows, and it loses no semantics.  Therefore
contextual invalidation cannot be defined merely as summary replacement,
section count, or representation growth.

The missing resource must include uniform update/evaluation work under a model
of computation.  But for arbitrary solver-independent CNFs, ruling out a
polynomial evaluator is already exactly `¬ SATDecisionInP`.  A future Route-G
advance would need a new independently conserved dynamical quantity—not a new
name for the evaluator lower bound—and a SAT family that forces that quantity
without forbidding the exact-syntax cache by definition.
-/

end PallLean.Paper93.DeepMath.PathB.ContextualSummaryInvalidationFrontier

#print axioms PallLean.Paper93.DeepMath.PathB.ContextualSummaryInvalidationFrontier.restrictAlong_descLen_le
#print axioms PallLean.Paper93.DeepMath.PathB.ContextualSummaryInvalidationFrontier.RestrictionSummaryScheme.realize_advanceAlong
#print axioms PallLean.Paper93.DeepMath.PathB.ContextualSummaryInvalidationFrontier.exactSyntaxSummary_invalidationGrowth_zero
#print axioms PallLean.Paper93.DeepMath.PathB.ContextualSummaryInvalidationFrontier.stableSummaryWithUniformEvaluator_iff_SATDecisionInP
#print axioms PallLean.Paper93.DeepMath.PathB.ContextualSummaryInvalidationFrontier.no_stableSummaryWithUniformEvaluator_iff_no_SATDecisionInP
