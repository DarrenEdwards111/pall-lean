import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameTowerProgramSliceCoverageBarrier

/-!
# N-Frame tower: solver-responsive coverage is still not diagonalization

The program-slice audit showed that global surface coverage is insufficient
when each fixed program is constant.  Here we grant the strongest remaining
purely syntactic repair:

* one fixed program uses the numeric solver-code input;
* that program's output slice covers every finite CNF;
* execution is total and takes one recorded step.

The fixed surface simply decodes the solver code as a CNF.  Against the
pointwise machine model from the previous audit, code `c` is correct on exactly
the formula decoded from `c`.  Therefore the compiler's perfect syntactic
coverage is aligned with correctness rather than failure.  No program on the
surface is an effective diagonalizer, although every program has full CNF
range and `SATDecisionInP` is false.

This isolates the final missing property with no coverage ambiguity:
correspondence-sensitive anti-correlation.  The compiler must not merely emit
many formulas from solver codes; its output for code `c` must be a formula on
which the machine carrying code `c` is wrong.  That is precisely the finite
semantic diagonal theorem.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameTowerSolverResponsiveCoverageBarrier

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.NFrameTowerSolverDiagonalizationFrontier
open PallLean.Paper93.DeepMath.PathB.NFrameTowerEffectiveDiagonalCompilerAudit
open PallLean.Paper93.DeepMath.PathB.NFrameTowerFixedSurfaceRangeBarrier
open PallLean.Paper93.DeepMath.PathB.NFrameTowerProgramSliceCoverageBarrier

/-! ## A fixed solver-responsive, fully covering surface -/

/-- Every program interprets its solver-code input as an encoded finite CNF.
Program zero is therefore already one fixed, total, solver-responsive emitter
whose slice covers all CNFs. -/
def solverResponsiveCNFCompilerModel : CounterexampleCompilerModel where
  compileRun := fun _ solverCode => some (decodeCNFCode solverCode)
  compileSteps := fun _ _ => 1

@[simp] theorem solverResponsiveCNFCompilerModel_run
    (program solverCode : Nat) :
    solverResponsiveCNFCompilerModel.compileRun program solverCode =
      some (decodeCNFCode solverCode) :=
  rfl

/-- Every single fixed program has full finite-CNF output coverage. -/
theorem solverResponsiveCNFCompilerModel_everyProgram_fullCoverage
    (program : Nat) (phi : CNF) :
    CompilerProgramOutputRange solverResponsiveCNFCompilerModel program phi := by
  exact ⟨encodeCNFCode phi, by simp⟩

/-- In particular, code zero is one fixed solver-responsive program with a
surjective output slice. -/
theorem solverResponsive_programZero_fullCoverage (phi : CNF) :
    CompilerProgramOutputRange solverResponsiveCNFCompilerModel 0 phi :=
  solverResponsiveCNFCompilerModel_everyProgram_fullCoverage 0 phi

/-! ## Correspondence defeats coverage -/

/-- Every numeric code is polynomially certified in the pointwise machine
model; code `c` is correct on the formula decoded from `c`. -/
noncomputable def pointwiseCodeDecisionMachine (code : Nat) :
    DecisionMachine pointwiseCNFMachineModel where
  code := code
  budget := fun _ => 0
  polyBudget := ⟨0, 0, by intro n; simp⟩
  steps_le_budget := by
    intro phi
    rfl

theorem pointwiseCodeDecisionMachine_correct_on_decode (code : Nat) :
    CorrectOn pointwiseCNFMachineModel code (decodeCNFCode code) := by
  classical
  simp [CorrectOn, pointwiseCNFMachineModel,
    PallLean.Paper93.DeepMath.PathB.PvsNPDynamicHolonomyQueryTranscriptBridge.satTruth_eq_true_iff]

/-- Every program is pointwise aligned with a certified machine it cannot
defeat: use any code `c`; the program emits `decodeCNFCode c`, and machine `c`
is correct there. -/
theorem no_effectiveCodeDiagonalizer_on_solverResponsiveSurface :
    ¬ Nonempty (EffectiveCodeDiagonalizer
      pointwiseCNFMachineModel solverResponsiveCNFCompilerModel) := by
  rintro ⟨K⟩
  let M := pointwiseCodeDecisionMachine 0
  rcases K.halts_with_counterexample M with ⟨phi, hrun, hfail⟩
  have heq : phi = decodeCNFCode M.code := by
    change some (decodeCNFCode M.code) = some phi at hrun
    exact (Option.some.inj hrun).symm
  subst phi
  exact hfail (pointwiseCodeDecisionMachine_correct_on_decode M.code)

/-! ## Exact syntactic frontier -/

/-- Full solver responsiveness, full output coverage for every fixed program,
and absence of a polynomial SAT decider coexist with failure of every
effective diagonal compiler. -/
theorem solverResponsiveCoverage_without_diagonalization :
    (forall program phi, CompilerProgramOutputRange
      solverResponsiveCNFCompilerModel program phi) ∧
    (¬ SATDecisionInP pointwiseCNFMachineModel) ∧
    (¬ Nonempty (EffectiveCodeDiagonalizer
      pointwiseCNFMachineModel solverResponsiveCNFCompilerModel)) := by
  exact ⟨solverResponsiveCNFCompilerModel_everyProgram_fullCoverage,
    no_SATDecisionInP_pointwiseCNFMachineModel,
    no_effectiveCodeDiagonalizer_on_solverResponsiveSurface⟩

/-- The demanded anti-correlation law on this fixed surface is exactly the
statement that every certified machine is wrong on the CNF decoded from its
own code. -/
def SolverCodeAntiCorrelation : Prop :=
  forall M : DecisionMachine pointwiseCNFMachineModel,
    ¬ CorrectOn pointwiseCNFMachineModel M.code (decodeCNFCode M.code)

theorem solverCodeAntiCorrelation_false : ¬ SolverCodeAntiCorrelation := by
  intro hAnti
  exact hAnti (pointwiseCodeDecisionMachine 0)
    (pointwiseCodeDecisionMachine_correct_on_decode 0)

end PallLean.Paper93.DeepMath.PathB.NFrameTowerSolverResponsiveCoverageBarrier

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerSolverResponsiveCoverageBarrier.solverResponsiveCNFCompilerModel_everyProgram_fullCoverage
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerSolverResponsiveCoverageBarrier.pointwiseCodeDecisionMachine_correct_on_decode
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerSolverResponsiveCoverageBarrier.no_effectiveCodeDiagonalizer_on_solverResponsiveSurface
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerSolverResponsiveCoverageBarrier.solverResponsiveCoverage_without_diagonalization
