import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameTowerSolverResponsiveCoverageBarrier

/-!
# N-Frame tower: fixed-program factorization endpoint

The preceding audits constructed a fixed, total, polynomial-time,
solver-responsive compiler surface on which every fixed program covers every
finite CNF.  They also proved that these operational properties do not imply
diagonalization.  This file factors the target exactly into:

1. a fixed polynomial compiler program and its run certificate;
2. the semantic anti-correlation law saying its output for each certified
   solver code is a formula that solver misclassifies.

For an arbitrary compiler surface, existence of those two components is
definitionally equivalent to `EffectiveCodeDiagonalizer`.  On the concrete
solver-responsive surface, the operational component is inhabited
unconditionally by program zero.  Its anti-correlation law reduces exactly to

`forall M, not (CorrectOn U M.code (decodeCNFCode M.code))`.

That law is equivalent to existence of an effective diagonalizer on the fixed
surface and implies `SAT ∉ P`.  The pointwise countermodel refutes it while
retaining every operational field.  Thus the fixed-machine route is now fully
factored: no runtime, totality, codec, responsiveness, or coverage socket
remains hidden; the sole missing field is the finite semantic diagonal itself.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameTowerFixedProgramFactorizationEndpoint

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.NFrameTowerSolverDiagonalizationFrontier
open PallLean.Paper93.DeepMath.PathB.NFrameTowerEffectiveDiagonalCompilerAudit
open PallLean.Paper93.DeepMath.PathB.NFrameTowerProgramSliceCoverageBarrier
open PallLean.Paper93.DeepMath.PathB.NFrameTowerSolverResponsiveCoverageBarrier

/-! ## General operational/semantic factorization -/

/-- One fixed polynomially bounded compiler program, before any claim about
the meaning of the formulas it emits. -/
structure PolynomialCompilerProgram (V : CounterexampleCompilerModel) where
  code : Nat
  budget : Nat -> Nat
  polyBudget : IsPolynomialBudget budget
  steps_le_budget : forall solverCode,
    V.compileSteps code solverCode <= budget solverCode

/-- The missing semantic field for a fixed compiler program. -/
def ProgramAntiCorrelation
    (U : MachineModel) (V : CounterexampleCompilerModel)
    (P : PolynomialCompilerProgram V) : Prop :=
  forall M : DecisionMachine U, exists phi,
    V.compileRun P.code M.code = some phi ∧
      ¬ CorrectOn U M.code phi

/-- Operational program plus anti-correlation is exactly an effective code
diagonalizer. -/
def effectiveCodeDiagonalizerOfProgramAntiCorrelation
    {U : MachineModel} {V : CounterexampleCompilerModel}
    (P : PolynomialCompilerProgram V)
    (hAnti : ProgramAntiCorrelation U V P) :
    EffectiveCodeDiagonalizer U V where
  code := P.code
  budget := P.budget
  polyBudget := P.polyBudget
  steps_le_budget := P.steps_le_budget
  halts_with_counterexample := hAnti

def polynomialCompilerProgramOfEffectiveCodeDiagonalizer
    {U : MachineModel} {V : CounterexampleCompilerModel}
    (K : EffectiveCodeDiagonalizer U V) :
    PolynomialCompilerProgram V where
  code := K.code
  budget := K.budget
  polyBudget := K.polyBudget
  steps_le_budget := K.steps_le_budget

theorem effectiveCodeDiagonalizer_iff_programAntiCorrelation
    (U : MachineModel) (V : CounterexampleCompilerModel) :
    Nonempty (EffectiveCodeDiagonalizer U V) ↔
      exists P : PolynomialCompilerProgram V,
        ProgramAntiCorrelation U V P := by
  constructor
  · rintro ⟨K⟩
    let P := polynomialCompilerProgramOfEffectiveCodeDiagonalizer K
    exact ⟨P, K.halts_with_counterexample⟩
  · rintro ⟨P, hAnti⟩
    exact ⟨effectiveCodeDiagonalizerOfProgramAntiCorrelation P hAnti⟩

/-! ## Every operational socket is inhabited on the fixed surface -/

/-- Program zero on the solver-responsive surface has constant recorded
runtime. -/
def solverResponsivePolynomialProgram :
    PolynomialCompilerProgram solverResponsiveCNFCompilerModel where
  code := 0
  budget := fun _ => 1
  polyBudget := ⟨0, 1, by intro n; simp⟩
  steps_le_budget := by
    intro solverCode
    rfl

/-- It halts with a concrete finite CNF on every numeric solver code. -/
theorem solverResponsivePolynomialProgram_total (solverCode : Nat) :
    exists phi, solverResponsiveCNFCompilerModel.compileRun
      solverResponsivePolynomialProgram.code solverCode = some phi := by
  exact ⟨decodeCNFCode solverCode, rfl⟩

/-- Its one fixed program slice covers every finite CNF. -/
theorem solverResponsivePolynomialProgram_fullCoverage (phi : CNF) :
    CompilerProgramOutputRange solverResponsiveCNFCompilerModel
      solverResponsivePolynomialProgram.code phi :=
  solverResponsiveCNFCompilerModel_everyProgram_fullCoverage
    solverResponsivePolynomialProgram.code phi

/-! ## Exact semantic endpoint on the concrete surface -/

/-- The correspondence-sensitive statement left after erasing every
operational field. -/
def DecodedSolverAntiCorrelation (U : MachineModel) : Prop :=
  forall M : DecisionMachine U,
    ¬ CorrectOn U M.code (decodeCNFCode M.code)

theorem solverResponsiveProgramAntiCorrelation_iff_decoded
    (U : MachineModel) :
    ProgramAntiCorrelation U solverResponsiveCNFCompilerModel
      solverResponsivePolynomialProgram ↔
      DecodedSolverAntiCorrelation U := by
  constructor
  · intro hAnti M
    rcases hAnti M with ⟨phi, hrun, hfail⟩
    have heq : phi = decodeCNFCode M.code := by
      change some (decodeCNFCode M.code) = some phi at hrun
      exact (Option.some.inj hrun).symm
    simpa only [heq] using hfail
  · intro hDecoded M
    exact ⟨decodeCNFCode M.code, rfl, hDecoded M⟩

/-- On this fixed surface, effective diagonalization is exactly the decoded
solver anti-correlation law.  All compiler programs have the same run
semantics, so an arbitrary effective witness can be normalized to program
zero. -/
theorem effectiveCodeDiagonalizer_iff_decodedSolverAntiCorrelation
    (U : MachineModel) :
    Nonempty (EffectiveCodeDiagonalizer U solverResponsiveCNFCompilerModel) ↔
      DecodedSolverAntiCorrelation U := by
  constructor
  · rintro ⟨K⟩ M
    rcases K.halts_with_counterexample M with ⟨phi, hrun, hfail⟩
    have heq : phi = decodeCNFCode M.code := by
      change some (decodeCNFCode M.code) = some phi at hrun
      exact (Option.some.inj hrun).symm
    simpa only [heq] using hfail
  · intro hDecoded
    exact ⟨effectiveCodeDiagonalizerOfProgramAntiCorrelation
      solverResponsivePolynomialProgram
      ((solverResponsiveProgramAntiCorrelation_iff_decoded U).2 hDecoded)⟩

/-- The semantic field alone yields the SAT lower bound because all
operational fields have already been constructed. -/
theorem no_SATDecisionInP_of_decodedSolverAntiCorrelation
    {U : MachineModel} (hAnti : DecodedSolverAntiCorrelation U) :
    ¬ SATDecisionInP U :=
  no_SATDecisionInP_of_effectiveCodeDiagonalizer
    ((effectiveCodeDiagonalizer_iff_decodedSolverAntiCorrelation U).2 hAnti).some

/-- The pointwise model satisfies every operational requirement but refutes
the remaining semantic field. -/
theorem operational_complete_but_semantic_field_false :
    (forall solverCode, exists phi,
      solverResponsiveCNFCompilerModel.compileRun
        solverResponsivePolynomialProgram.code solverCode = some phi) ∧
    (forall phi, CompilerProgramOutputRange solverResponsiveCNFCompilerModel
      solverResponsivePolynomialProgram.code phi) ∧
    (¬ DecodedSolverAntiCorrelation pointwiseCNFMachineModel) := by
  refine ⟨solverResponsivePolynomialProgram_total,
    solverResponsivePolynomialProgram_fullCoverage, ?_⟩
  intro hAnti
  exact hAnti (pointwiseCodeDecisionMachine 0)
    (pointwiseCodeDecisionMachine_correct_on_decode 0)

end PallLean.Paper93.DeepMath.PathB.NFrameTowerFixedProgramFactorizationEndpoint

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerFixedProgramFactorizationEndpoint.effectiveCodeDiagonalizer_iff_programAntiCorrelation
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerFixedProgramFactorizationEndpoint.solverResponsivePolynomialProgram
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerFixedProgramFactorizationEndpoint.effectiveCodeDiagonalizer_iff_decodedSolverAntiCorrelation
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerFixedProgramFactorizationEndpoint.operational_complete_but_semantic_field_false
