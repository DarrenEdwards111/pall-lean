import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUCRDPatternCoupledLoopsAudit
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUniformFutureEvaluatorFrontier

/-!
# UCRD genuine-SAT loop evaluator frontier

The preceding audits progressively strengthened contextual loops from a single
cheap motif to independent irreversible coordinates and then to `2^n` dense,
coupled pattern holonomies.  All remained succinctly and uniformly evaluable.

This file performs the decisive solver-independent test.  Every encoded CNF
`φ` names a legal four-stage loop by its syntax alone.  On return, the loop
irreversibly merges the genuine semantic bit `satTruth φ` into its Boolean
observer state.  Thus evaluating the loop on `false` is literally deciding
whether `φ` is satisfiable.

We prove the exact endpoint:

* a polynomial-budget machine uniformly evaluating every SAT loop exists iff
  `SATDecisionInP` holds in the supplied machine model;
* equivalently, the desired absence of a shared polynomial SAT-loop evaluator
  is exactly `¬ SATDecisionInP`;
* the loop formulation is equivalent to the earlier uniform future-query
  evaluator formulation.

This is a calibration theorem, not a separation.  Genuine SAT coupling finally
prevents the explicit OR-cache construction, but proving that no polynomial
uniform evaluator exists is precisely the original general SAT lower bound.
-/

namespace PallLean.Paper93.DeepMath.PathB.UCRDSATLoopEvaluatorFrontier

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.UCRDLegalLoopTransportAudit
open PallLean.Paper93.DeepMath.PathB.PvsNPDynamicHolonomyQueryTranscriptBridge
open PallLean.Paper93.DeepMath.PathB.UniformFutureEvaluatorFrontier

attribute [local instance] Classical.propDecidable

/-! ## Genuine solver-independent SAT loops -/

/-- The context carries the unchanged CNF syntax and one temporal stage. -/
abbrev SATLoopContext := CNF × ExperienceContext

/-- Legal transitions preserve the formula and advance through the four-stage
observer-time cycle. -/
def satLoopLegal : SATLoopContext → SATLoopContext → Prop
  | (φ, c), (ψ, d) => φ = ψ ∧ experienceLegal c d

/-- A CNF names its loop syntactically.  Only the semantic return transport
depends on satisfiability; no answer-coded `yesCNF`/`noCNF` is constructed. -/
noncomputable def satLoop (φ : CNF) :
    LegalTransportLoop SATLoopContext Bool where
  legal := satLoopLegal
  c0 := (φ, .opening)
  c1 := (φ, .rising)
  c2 := (φ, .turning)
  c3 := (φ, .returning)
  legal01 := by exact ⟨rfl, trivial⟩
  legal12 := by exact ⟨rfl, trivial⟩
  legal23 := by exact ⟨rfl, trivial⟩
  legal30 := by exact ⟨rfl, trivial⟩
  transport01 := id
  transport12 := id
  transport23 := id
  transport30 := fun s => satTruth φ || s
  cost01 := 1
  cost12 := 1
  cost23 := 1
  cost30 := φ.size

theorem satLoop_holonomy (φ : CNF) (s : Bool) :
    (satLoop φ).holonomy s = (satTruth φ || s) := by
  rfl

/-- The return action on the blank observer state is exactly SAT truth. -/
theorem satLoop_holonomy_false (φ : CNF) :
    (satLoop φ).holonomy false = satTruth φ := by
  simp [satLoop_holonomy]

theorem satLoop_holonomy_false_eq_true_iff (φ : CNF) :
    (satLoop φ).holonomy false = true ↔ Satisfiable φ := by
  rw [satLoop_holonomy_false]
  exact satTruth_eq_true_iff φ

/-- The syntactic traversal/name budget is linear.  This does not charge away
the unresolved semantic evaluation of `satTruth`. -/
theorem satLoop_work (φ : CNF) :
    (satLoop φ).loopWork = φ.size + 3 := by
  simp [LegalTransportLoop.loopWork, satLoop]
  omega

def satLoopNameWork (n : Nat) : Nat := n + 3

theorem satLoopNameWork_isPolynomialBudget :
    IsPolynomialBudget satLoopNameWork := by
  refine ⟨1, 4, ?_⟩
  intro n
  simp [satLoopNameWork, pow_one]
  omega

/-! ## Shared evaluator equals polynomial SAT decision -/

/-- One polynomial-budget machine uniformly realizes the semantic return
transport of every genuine CNF loop. -/
structure UniformSATLoopEvaluator (U : MachineModel) where
  machine : DecisionMachine U
  correct : ∀ (φ : CNF) (s : Bool),
    (U.decisionRun machine.code φ || s) = (satLoop φ).holonomy s

/-- A correct SAT decider uniformly evaluates every SAT loop. -/
noncomputable def uniformSATLoopEvaluatorOfDecider
    {U : MachineModel} (D : DecisionMachine U) (hD : DecidesSAT U D) :
    UniformSATLoopEvaluator U where
  machine := D
  correct := by
    intro φ s
    have heq : U.decisionRun D.code φ = satTruth φ := by
      apply Bool.eq_iff_iff.mpr
      exact (hD φ).trans (satTruth_eq_true_iff φ).symm
    rw [satLoop_holonomy, heq]

/-- Reading one genuine SAT loop on `false` recovers a SAT decision. -/
theorem UniformSATLoopEvaluator.decidesSAT
    {U : MachineModel} (E : UniformSATLoopEvaluator U) :
    DecidesSAT U E.machine := by
  intro φ
  have heq : U.decisionRun E.machine.code φ = satTruth φ := by
    simpa [satLoop_holonomy] using E.correct φ false
  rw [heq]
  exact satTruth_eq_true_iff φ

/-- **Exact SAT-loop frontier.** -/
theorem uniformSATLoopEvaluator_iff_SATDecisionInP (U : MachineModel) :
    Nonempty (UniformSATLoopEvaluator U) ↔ SATDecisionInP U := by
  constructor
  · rintro ⟨E⟩
    exact ⟨E.machine, E.decidesSAT⟩
  · rintro ⟨D, hD⟩
    exact ⟨uniformSATLoopEvaluatorOfDecider D hD⟩

/-- The proposed superpolynomial shared-transport obstruction is the original
no-polynomial-SAT-decider statement. -/
theorem no_uniformSATLoopEvaluator_iff_no_SATDecisionInP
    (U : MachineModel) :
    (¬ Nonempty (UniformSATLoopEvaluator U)) ↔ ¬ SATDecisionInP U := by
  rw [uniformSATLoopEvaluator_iff_SATDecisionInP]

/-- Loop evaluation and genuine future-query evaluation are the same frontier,
not two independent lower-bound opportunities. -/
theorem uniformSATLoopEvaluator_iff_uniformFutureQueryEvaluator
    (U : MachineModel) :
    Nonempty (UniformSATLoopEvaluator U) ↔
      Nonempty (UniformFutureQueryEvaluator U) := by
  rw [uniformSATLoopEvaluator_iff_SATDecisionInP,
    uniformFutureQueryEvaluator_iff_SATDecisionInP]

end PallLean.Paper93.DeepMath.PathB.UCRDSATLoopEvaluatorFrontier

#print axioms PallLean.Paper93.DeepMath.PathB.UCRDSATLoopEvaluatorFrontier.satLoop_holonomy_false_eq_true_iff
#print axioms PallLean.Paper93.DeepMath.PathB.UCRDSATLoopEvaluatorFrontier.satLoopNameWork_isPolynomialBudget
#print axioms PallLean.Paper93.DeepMath.PathB.UCRDSATLoopEvaluatorFrontier.UniformSATLoopEvaluator.decidesSAT
#print axioms PallLean.Paper93.DeepMath.PathB.UCRDSATLoopEvaluatorFrontier.uniformSATLoopEvaluator_iff_SATDecisionInP
#print axioms PallLean.Paper93.DeepMath.PathB.UCRDSATLoopEvaluatorFrontier.no_uniformSATLoopEvaluator_iff_no_SATDecisionInP
#print axioms PallLean.Paper93.DeepMath.PathB.UCRDSATLoopEvaluatorFrontier.uniformSATLoopEvaluator_iff_uniformFutureQueryEvaluator
