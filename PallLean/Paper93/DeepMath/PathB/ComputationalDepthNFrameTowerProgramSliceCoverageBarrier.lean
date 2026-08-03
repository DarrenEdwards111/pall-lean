import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameTowerFixedSurfaceRangeBarrier

/-!
# N-Frame tower: program-slice coverage barrier

The fixed-surface range audit showed that a surface with an impoverished
global output range cannot host a diagonal compiler.  This file closes the
next loophole: even faithful coverage of every finite CNF by the surface as a
whole is insufficient, because an `EffectiveCodeDiagonalizer` must use one
fixed program code.

We build an explicit, constructive codec between the repository's concrete
`CNF` structure and natural numbers.  The resulting fixed compiler surface is
total, runs in one step, and is globally surjective onto every finite CNF.
However, program `p` always emits the single formula decoded from `p`,
independently of the solver code.

We also build a machine model in which every individual CNF has a certified
constant-budget machine that is correct on that formula, while no single code
decides SAT globally.  Hence every fixed program slice is blocked although
the full surface covers all CNFs and `SATDecisionInP` is false.

The next genuine universal-machine requirement is therefore not merely a
surjective CNF codec.  One fixed compiler program must use its solver-code
input to range over sufficiently many formulas, and then its outputs must be
proved to defeat the corresponding solvers.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameTowerProgramSliceCoverageBarrier

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPDynamicHolonomyQueryTranscriptBridge
open PallLean.Paper93.DeepMath.PathB.EntanglementFiniteRunExtractionNoGo
open PallLean.Paper93.DeepMath.PathB.NFrameTowerSolverDiagonalizationFrontier
open PallLean.Paper93.DeepMath.PathB.NFrameTowerEffectiveDiagonalCompilerAudit
open PallLean.Paper93.DeepMath.PathB.NFrameTowerFixedSurfaceRangeBarrier

/-! ## A constructive natural-number codec for concrete CNFs -/

def polarityEquivBool : Polarity ≃ Bool where
  toFun
    | Polarity.pos => true
    | Polarity.neg => false
  invFun b := if b then Polarity.pos else Polarity.neg
  left_inv p := by cases p <;> rfl
  right_inv b := by cases b <;> rfl

local instance : Encodable Polarity :=
  Encodable.ofEquiv Bool polarityEquivBool

def litEquivData : Lit ≃ Nat × Polarity where
  toFun l := (l.var, l.pol)
  invFun p := { var := p.1, pol := p.2 }
  left_inv l := by cases l; rfl
  right_inv p := by cases p; rfl

local instance : Encodable Lit :=
  Encodable.ofEquiv (Nat × Polarity) litEquivData

def cnfEquivData : CNF ≃ Nat × List (List Lit) where
  toFun phi := (phi.vars, phi.clauses)
  invFun p := { vars := p.1, clauses := p.2 }
  left_inv phi := by cases phi; rfl
  right_inv p := by cases p; rfl

local instance : Encodable CNF :=
  Encodable.ofEquiv (Nat × List (List Lit)) cnfEquivData

local instance : DecidableEq CNF :=
  Encodable.decidableEqOfEncodable CNF

/-- Constructive code of a finite CNF. -/
def encodeCNFCode (phi : CNF) : Nat := Encodable.encode phi

/-- Total decoding, with `noCNF` as the value on unused natural codes. -/
def decodeCNFCode (code : Nat) : CNF :=
  (Encodable.decode code).getD noCNF

@[simp] theorem decodeCNFCode_encodeCNFCode (phi : CNF) :
    decodeCNFCode (encodeCNFCode phi) = phi := by
  simp [decodeCNFCode, encodeCNFCode]

theorem decodeCNFCode_surjective : Function.Surjective decodeCNFCode := by
  intro phi
  exact ⟨encodeCNFCode phi, decodeCNFCode_encodeCNFCode phi⟩

/-! ## Global coverage but constant program slices -/

/-- The fixed surface interprets a program code as a literal encoded CNF and
ignores the solver-code input. -/
def literalCNFCompilerModel : CounterexampleCompilerModel where
  compileRun := fun program _ => some (decodeCNFCode program)
  compileSteps := fun _ _ => 1

/-- The surface as a whole faithfully covers every concrete finite CNF. -/
theorem literalCNFCompilerModel_globalCoverage (phi : CNF) :
    CompilerOutputRange literalCNFCompilerModel phi := by
  exact ⟨encodeCNFCode phi, 0, by
    simp [literalCNFCompilerModel]⟩

/-- The output range of one fixed compiler program. -/
def CompilerProgramOutputRange
    (V : CounterexampleCompilerModel) (program : Nat) (phi : CNF) : Prop :=
  exists solverCode, V.compileRun program solverCode = some phi

/-- A machine correct on all formulas emitted by one fixed program. -/
def CorrectOnCompilerProgramRange
    (U : MachineModel) (V : CounterexampleCompilerModel) (program : Nat)
    (M : DecisionMachine U) : Prop :=
  forall phi, CompilerProgramOutputRange V program phi ->
    CorrectOn U M.code phi

/-- Every individual program on the literal surface has singleton range. -/
theorem literalCNFCompilerModel_programRange_iff
    (program : Nat) (phi : CNF) :
    CompilerProgramOutputRange literalCNFCompilerModel program phi ↔
      phi = decodeCNFCode program := by
  constructor
  · rintro ⟨solverCode, hrun⟩
    change some (decodeCNFCode program) = some phi at hrun
    exact (Option.some.inj hrun).symm
  · intro hphi
    subst phi
    exact ⟨0, rfl⟩

/-- If every program slice is covered by some certified machine, no single
program can defeat all machines. -/
theorem no_effectiveCodeDiagonalizer_of_everyProgramSliceCovered
    {U : MachineModel} {V : CounterexampleCompilerModel}
    (hCovered : forall program, exists M : DecisionMachine U,
      CorrectOnCompilerProgramRange U V program M) :
    ¬ Nonempty (EffectiveCodeDiagonalizer U V) := by
  rintro ⟨K⟩
  rcases hCovered K.code with ⟨M, hM⟩
  rcases K.halts_with_counterexample M with ⟨phi, hrun, hfail⟩
  exact hfail (hM phi ⟨M.code, hrun⟩)

/-! ## A pointwise-correct but globally incomplete machine model -/

/-- Code `c` recognizes the single formula decoded from `c`, returning that
formula's genuine SAT truth; it rejects every other formula. -/
noncomputable def pointwiseCNFMachineModel : MachineModel where
  searchRun := fun _ _ => none
  searchSteps := fun _ _ => 0
  decisionRun := fun code phi =>
    if phi = decodeCNFCode code then satTruth phi else false
  decisionSteps := fun _ _ => 0
  verifierCode := fun _ => encodeCNFCode noCNF
  verifier_run := by
    intro code phi
    by_cases hphi : phi = noCNF
    · subst phi
      simp [checkSearchOutput, satTruth_noCNF]
    · simp [checkSearchOutput, hphi]
  verifier_steps := by
    intro code phi
    rfl

/-- Every concrete formula has a certified constant-budget code correct on
that formula. -/
noncomputable def pointwiseDecisionMachine (phi : CNF) :
    DecisionMachine pointwiseCNFMachineModel where
  code := encodeCNFCode phi
  budget := fun _ => 0
  polyBudget := ⟨0, 0, by intro n; simp⟩
  steps_le_budget := by
    intro psi
    rfl

theorem pointwiseDecisionMachine_correct (phi : CNF) :
    CorrectOn pointwiseCNFMachineModel (pointwiseDecisionMachine phi).code phi := by
  unfold CorrectOn
  change ((if phi = decodeCNFCode (encodeCNFCode phi) then satTruth phi else false) =
    true ↔ Satisfiable phi)
  rw [decodeCNFCode_encodeCNFCode]
  simp only [if_pos, satTruth_eq_true_iff]

/-- Each fixed program slice of the globally surjective surface is covered by
the pointwise machine for its unique formula. -/
theorem literalCNFCompilerModel_everyProgramSliceCovered
    (program : Nat) :
    exists M : DecisionMachine pointwiseCNFMachineModel,
      CorrectOnCompilerProgramRange pointwiseCNFMachineModel
        literalCNFCompilerModel program M := by
  refine ⟨pointwiseDecisionMachine (decodeCNFCode program), ?_⟩
  intro phi hphi
  have heq : phi = decodeCNFCode program :=
    (literalCNFCompilerModel_programRange_iff program phi).mp hphi
  subst phi
  exact pointwiseDecisionMachine_correct (decodeCNFCode program)

theorem no_effectiveCodeDiagonalizer_on_literalCNFCompilerModel :
    ¬ Nonempty (EffectiveCodeDiagonalizer
      pointwiseCNFMachineModel literalCNFCompilerModel) :=
  no_effectiveCodeDiagonalizer_of_everyProgramSliceCovered
    literalCNFCompilerModel_everyProgramSliceCovered

/-- No pointwise code decides all of SAT.  For code `c`, choose a satisfiable
empty CNF whose size is one larger than the formula decoded from `c`; the code
rejects it because the formulas cannot be equal. -/
theorem no_SATDecisionInP_pointwiseCNFMachineModel :
    ¬ SATDecisionInP pointwiseCNFMachineModel := by
  rintro ⟨M, hM⟩
  let target := decodeCNFCode M.code
  let probe := emptyCNF (target.size + 1)
  have hne : probe ≠ target := by
    intro heq
    have hsize := congrArg CNF.size heq
    simp [probe, emptyCNF_size] at hsize
  have hrun : pointwiseCNFMachineModel.decisionRun M.code probe = true :=
    (hM probe).2 (by simpa [probe] using emptyCNF_satisfiable (target.size + 1))
  simp [pointwiseCNFMachineModel, target, hne] at hrun

/-- **Global-coverage countermodel.**  The fixed surface covers every finite
CNF and `SATDecisionInP` is false, yet no one fixed program on the surface is
an effective diagonalizer. -/
theorem globalCoverage_still_not_fixedProgramDiagonalization :
    (forall phi : CNF, CompilerOutputRange literalCNFCompilerModel phi) ∧
    (¬ SATDecisionInP pointwiseCNFMachineModel) ∧
    (¬ Nonempty (EffectiveCodeDiagonalizer
      pointwiseCNFMachineModel literalCNFCompilerModel)) := by
  exact ⟨literalCNFCompilerModel_globalCoverage,
    no_SATDecisionInP_pointwiseCNFMachineModel,
    no_effectiveCodeDiagonalizer_on_literalCNFCompilerModel⟩

end PallLean.Paper93.DeepMath.PathB.NFrameTowerProgramSliceCoverageBarrier

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerProgramSliceCoverageBarrier.decodeCNFCode_encodeCNFCode
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerProgramSliceCoverageBarrier.literalCNFCompilerModel_globalCoverage
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerProgramSliceCoverageBarrier.no_effectiveCodeDiagonalizer_of_everyProgramSliceCovered
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerProgramSliceCoverageBarrier.globalCoverage_still_not_fixedProgramDiagonalization
