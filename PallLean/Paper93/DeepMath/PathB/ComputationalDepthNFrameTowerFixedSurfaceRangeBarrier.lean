import PallLean.Paper93.DeepMath.PathB.ComputationalDepthEntanglementTowerUnifiedFiniteEndpoint
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameTowerSyntacticFeedbackCollapse
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUniformFutureEvaluatorFrontier

/-!
# N-Frame tower: fixed compiler-surface range barrier

The unified entanglement/tower endpoint proved that an effective diagonal
compiler on a witness-chosen surface is exactly `SAT ∉ P`; the reverse
direction installs classically chosen counterexamples in an oracle surface.
This file tests the genuinely stronger next proposal: hold the compiler
surface fixed independently of the lower bound.

For every fixed surface, its semantic output range is an unavoidable
restriction.  If even one certified decision machine is correct on that whole
range, no program on the surface can diagonalize against every machine.

We then give a concrete strict countermodel.  The fixed compiler surface emits
only the two canonical truth-coded formulas `yesCNF` and `noCNF`, always in one
step.  The fixed machine model contains a polynomial machine that answers that
pair correctly, but no code in the model decides SAT on all finite CNFs.
Consequently:

* `SATDecisionInP` is false in the machine model;
* nevertheless the fixed surface has no `EffectiveCodeDiagonalizer`.

Thus `SAT ∉ P` does not construct a compiler on an arbitrary independently
fixed surface.  Universality/output coverage is a real extra implementation
obligation, while the solver-defeating correctness theorem remains the hard
semantic obligation.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameTowerFixedSurfaceRangeBarrier

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPDynamicHolonomyQueryTranscriptBridge
open PallLean.Paper93.DeepMath.PathB.UniformFutureEvaluatorFrontier
open PallLean.Paper93.DeepMath.PathB.NFrameTowerSolverDiagonalizationFrontier
open PallLean.Paper93.DeepMath.PathB.NFrameTowerEffectiveDiagonalCompilerAudit

/-! ## The output-range obstruction for every fixed surface -/

/-- The set of finite formulas that can be emitted anywhere on a fixed
compiler surface. -/
def CompilerOutputRange (V : CounterexampleCompilerModel) (phi : CNF) : Prop :=
  exists program solverCode, V.compileRun program solverCode = some phi

/-- A certified machine is correct on the entire semantic range of a fixed
compiler surface. -/
def CorrectOnCompilerRange
    (U : MachineModel) (V : CounterexampleCompilerModel)
    (M : DecisionMachine U) : Prop :=
  forall phi, CompilerOutputRange V phi -> CorrectOn U M.code phi

/-- One machine correct on the surface's complete output range blocks every
purported effective diagonalizer on that surface. -/
theorem no_effectiveCodeDiagonalizer_of_correctOnCompilerRange
    {U : MachineModel} {V : CounterexampleCompilerModel}
    (M : DecisionMachine U) (hRange : CorrectOnCompilerRange U V M) :
    ¬ Nonempty (EffectiveCodeDiagonalizer U V) := by
  rintro ⟨K⟩
  rcases K.halts_with_counterexample M with ⟨phi, hrun, hfail⟩
  exact hfail (hRange phi ⟨K.code, M.code, hrun⟩)

/-- A convenient range upper bound. -/
def OutputsOnly
    (V : CounterexampleCompilerModel) (R : CNF -> Prop) : Prop :=
  forall program solverCode phi,
    V.compileRun program solverCode = some phi -> R phi

/-- If all outputs lie in `R` and a certified machine is correct throughout
`R`, the fixed surface cannot host an effective diagonalizer. -/
theorem no_effectiveCodeDiagonalizer_of_outputsOnly
    {U : MachineModel} {V : CounterexampleCompilerModel}
    {R : CNF -> Prop} (M : DecisionMachine U)
    (hOutputs : OutputsOnly V R)
    (hCorrect : forall phi, R phi -> CorrectOn U M.code phi) :
    ¬ Nonempty (EffectiveCodeDiagonalizer U V) := by
  apply no_effectiveCodeDiagonalizer_of_correctOnCompilerRange M
  intro phi hphi
  rcases hphi with ⟨program, solverCode, hrun⟩
  exact hCorrect phi (hOutputs program solverCode phi hrun)

/-! ## A fixed two-formula compiler surface -/

/-- The canonical two-formula output range. -/
def CanonicalTruthRange (phi : CNF) : Prop :=
  phi = yesCNF ∨ phi = noCNF

/-- An independently fixed, total, one-step surface.  It can emit both
canonical truth-coded formulas, but no noncanonical SAT instance. -/
def canonicalTruthCompilerModel : CounterexampleCompilerModel where
  compileRun := fun program solverCode =>
    if (program + solverCode) % 2 = 0 then some yesCNF else some noCNF
  compileSteps := fun _ _ => 1

theorem canonicalTruthCompilerModel_outputsOnly :
    OutputsOnly canonicalTruthCompilerModel CanonicalTruthRange := by
  intro program solverCode phi hrun
  change (if (program + solverCode) % 2 = 0 then some yesCNF else some noCNF) =
    some phi at hrun
  split at hrun
  · left
    exact Option.some.inj hrun.symm
  · right
    exact Option.some.inj hrun.symm

/-! ## A machine model separating `SAT ∉ P` from the fixed compiler -/

/-- A small satisfiable formula whose clause list is nonempty. -/
def nonemptyYesCNF : CNF :=
  { vars := 1
    clauses := [[{ var := 0, pol := Polarity.pos }]] }

theorem nonemptyYesCNF_satisfiable : Satisfiable nonemptyYesCNF := by
  refine ⟨[true], ?_⟩
  simp [nonemptyYesCNF, Satisfies, CNF.eval, Clause.eval, Lit.eval,
    RawAssignment.lookup]

/-- Code zero recognizes only the easy canonical syntax `clauses.isEmpty`.
All other decision codes reject.  Verifier codes are successors and correctly
represent the everywhere-failing search programs. -/
def canonicalPairMachineModel : MachineModel where
  searchRun := fun _ _ => none
  searchSteps := fun _ _ => 0
  decisionRun := fun code phi =>
    if code = 0 then yesNoSyntacticEvaluator phi else false
  decisionSteps := fun _ _ => 0
  verifierCode := Nat.succ
  verifier_run := by
    intro code phi
    simp [checkSearchOutput]
  verifier_steps := by
    intro code phi
    rfl

/-- The certified constant-budget code zero. -/
def canonicalPairDecisionMachine :
    DecisionMachine canonicalPairMachineModel where
  code := 0
  budget := fun _ => 0
  polyBudget := by
    exact ⟨0, 0, by intro n; simp⟩
  steps_le_budget := by
    intro phi
    rfl

theorem canonicalPairDecisionMachine_correct_yes :
    CorrectOn canonicalPairMachineModel canonicalPairDecisionMachine.code
      yesCNF := by
  change (true = true ↔ Satisfiable yesCNF)
  constructor
  · intro _
    exact yesCNF_satisfiable
  · intro _
    rfl

theorem canonicalPairDecisionMachine_correct_no :
    CorrectOn canonicalPairMachineModel canonicalPairDecisionMachine.code
      noCNF := by
  change (false = true ↔ Satisfiable noCNF)
  constructor
  · intro h
    cases h
  · intro h
    exact (noCNF_not_satisfiable h).elim

theorem canonicalPairDecisionMachine_correctOnCanonicalRange
    (phi : CNF) (hphi : CanonicalTruthRange phi) :
    CorrectOn canonicalPairMachineModel canonicalPairDecisionMachine.code phi := by
  rcases hphi with rfl | rfl
  · exact canonicalPairDecisionMachine_correct_yes
  · exact canonicalPairDecisionMachine_correct_no

/-- The fixed two-formula compiler is blocked by code zero, which is correct
on its entire output range. -/
theorem no_effectiveCodeDiagonalizer_on_canonicalTruthCompilerModel :
    ¬ Nonempty (EffectiveCodeDiagonalizer
      canonicalPairMachineModel canonicalTruthCompilerModel) := by
  exact no_effectiveCodeDiagonalizer_of_outputsOnly
    canonicalPairDecisionMachine
    canonicalTruthCompilerModel_outputsOnly
    canonicalPairDecisionMachine_correctOnCanonicalRange

/-- Nevertheless no code in this machine model decides SAT: code zero rejects
the satisfiable nonempty formula, and every nonzero code rejects `yesCNF`. -/
theorem no_SATDecisionInP_canonicalPairMachineModel :
    ¬ SATDecisionInP canonicalPairMachineModel := by
  rintro ⟨M, hM⟩
  by_cases hcode : M.code = 0
  · have hrun :
        canonicalPairMachineModel.decisionRun M.code nonemptyYesCNF = true :=
      (hM nonemptyYesCNF).2 nonemptyYesCNF_satisfiable
    simp [canonicalPairMachineModel, hcode, yesNoSyntacticEvaluator,
      nonemptyYesCNF] at hrun
  · have hrun : canonicalPairMachineModel.decisionRun M.code yesCNF = true :=
      (hM yesCNF).2 yesCNF_satisfiable
    simp [canonicalPairMachineModel, hcode] at hrun

/-- **Strict fixed-surface countermodel.**  The SAT lower bound can hold while
an independently fixed polynomial-output compiler surface has no effective
diagonalizer. -/
theorem fixedSurface_reverse_implication_fails :
    ¬ ((¬ SATDecisionInP canonicalPairMachineModel) ->
      Nonempty (EffectiveCodeDiagonalizer
        canonicalPairMachineModel canonicalTruthCompilerModel)) := by
  intro hreverse
  exact no_effectiveCodeDiagonalizer_on_canonicalTruthCompilerModel
    (hreverse no_SATDecisionInP_canonicalPairMachineModel)

end PallLean.Paper93.DeepMath.PathB.NFrameTowerFixedSurfaceRangeBarrier

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerFixedSurfaceRangeBarrier.no_effectiveCodeDiagonalizer_of_correctOnCompilerRange
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerFixedSurfaceRangeBarrier.canonicalTruthCompilerModel_outputsOnly
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerFixedSurfaceRangeBarrier.no_SATDecisionInP_canonicalPairMachineModel
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerFixedSurfaceRangeBarrier.fixedSurface_reverse_implication_fails
