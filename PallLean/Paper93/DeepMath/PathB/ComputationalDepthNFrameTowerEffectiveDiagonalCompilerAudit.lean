import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameTowerSolverDiagonalizationFrontier

/-!
# N-Frame tower: effective diagonal compiler audit

The solver-indexed frontier isolated a semantic function assigning a failing
CNF to each polynomial solver code.  This file adds the missing operational
requirements: one fixed compiler program, an explicit run semantics, a step
count, and one polynomial budget for all solver-code inputs.

For any independently fixed compiler surface, existence of such a program
still implies `SAT ∉ P`.  The converse is not automatic.  We calibrate why the
surface matters with two extremes:

* an empty surface cannot realize a compiler whenever there is even one
  certified polynomial decision machine;
* an oracle surface built from the noncomputable semantic diagonalizer realizes
  the compiler in one step.

Consequently, if the compiler execution model itself may be chosen after
assuming `SAT ∉ P`, existence of an apparently constant-time compiler is again
equivalent to the lower bound.  The Book 1 tower decoration remains free: the
same uniform Rosser escape labels every code.  Genuine progress requires a
compiler in an independently defined effective universal machine, with its
finite failure theorem proved without importing the desired separation.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameTowerEffectiveDiagonalCompilerAudit

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.NFrameGodelTowerSATBridgeAudit
open PallLean.Paper93.DeepMath.PathB.NFrameTowerSolverDiagonalizationFrontier

/-! ## A fixed coded compiler surface -/

/-- An operational model for programs that take a numeric solver code and may
return a finite CNF, together with the number of steps used. -/
structure CounterexampleCompilerModel where
  compileRun : Nat → Nat → Option CNF
  compileSteps : Nat → Nat → Nat

/-- One fixed polynomial-time compiler program that defeats every certified
polynomial SAT decision machine on the CNF it emits for that machine's code. -/
structure EffectiveCodeDiagonalizer
    (U : MachineModel) (V : CounterexampleCompilerModel) where
  code : Nat
  budget : Nat → Nat
  polyBudget : IsPolynomialBudget budget
  steps_le_budget : ∀ solverCode,
    V.compileSteps code solverCode ≤ budget solverCode
  halts_with_counterexample : ∀ M : DecisionMachine U,
    ∃ φ, V.compileRun code M.code = some φ ∧
      ¬ CorrectOn U M.code φ

/-- An effective compiler refutes any globally correct polynomial SAT
decision machine. -/
theorem no_SATDecisionInP_of_effectiveCodeDiagonalizer
    {U : MachineModel} {V : CounterexampleCompilerModel}
    (K : EffectiveCodeDiagonalizer U V) :
    ¬ SATDecisionInP U := by
  rintro ⟨M, hcorrect⟩
  rcases K.halts_with_counterexample M with ⟨φ, _, hfail⟩
  exact hfail (hcorrect φ)

/-! ## The compiler surface cannot be left unconstrained -/

/-- A surface on which no program ever emits a CNF. -/
def emptyCompilerModel : CounterexampleCompilerModel where
  compileRun := fun _ _ => none
  compileSteps := fun _ _ => 0

/-- The empty surface has no effective diagonalizer as soon as the SAT machine
model contains one certified polynomial decision program. -/
theorem no_effectiveCodeDiagonalizer_on_emptyModel
    {U : MachineModel} (M : DecisionMachine U) :
    ¬ Nonempty (EffectiveCodeDiagonalizer U emptyCompilerModel) := by
  rintro ⟨K⟩
  rcases K.halts_with_counterexample M with ⟨φ, hrun, _⟩
  simp [emptyCompilerModel] at hrun

/-- An oracle surface obtained by baking a semantic code-indexed diagonalizer
directly into the run relation.  This is intentionally non-effective unless
the supplied `D` was independently computed. -/
def oracleCompilerModel
    {U : MachineModel} (D : CodeIndexedFiniteDiagonalizer U) :
    CounterexampleCompilerModel where
  compileRun := fun _ solverCode => some (D.counterexample solverCode)
  compileSteps := fun _ _ => 1

/-- Once the answer family is built into the semantics, code zero is a
constant-time compiler. -/
def oracleEffectiveCodeDiagonalizer
    {U : MachineModel} (D : CodeIndexedFiniteDiagonalizer U) :
    EffectiveCodeDiagonalizer U (oracleCompilerModel D) where
  code := 0
  budget := fun _ => 1
  polyBudget := by
    refine ⟨0, 1, ?_⟩
    intro n
    simp
  steps_le_budget := by
    intro solverCode
    rfl
  halts_with_counterexample := by
    intro M
    exact ⟨D.counterexample M.code, rfl, D.defeats M⟩

/-- If the execution surface may itself depend on the semantic diagonalizer,
the compiler can be made constant-time after assuming the lower bound. -/
noncomputable def oracleCompilerPackageOfNoSATDecisionInP
    {U : MachineModel} (hno : ¬ SATDecisionInP U) :
    Σ V : CounterexampleCompilerModel, EffectiveCodeDiagonalizer U V :=
  let D := codeIndexedFiniteDiagonalizerOfNoSATDecisionInP hno
  ⟨oracleCompilerModel D, oracleEffectiveCodeDiagonalizer D⟩

/-- **Variable-surface collapse.**  Allowing the compiler model to be selected
as part of the witness makes existence of an effective compiler exactly
equivalent to `SAT ∉ P`; the reverse direction merely hides classical choice
inside an oracle run relation. -/
theorem exists_effectiveCompilerSurface_iff_no_SATDecisionInP
    (U : MachineModel) :
    Nonempty (Σ V : CounterexampleCompilerModel,
      EffectiveCodeDiagonalizer U V) ↔ ¬ SATDecisionInP U := by
  constructor
  · rintro ⟨⟨_, K⟩⟩
    exact no_SATDecisionInP_of_effectiveCodeDiagonalizer K
  · intro hno
    exact ⟨oracleCompilerPackageOfNoSATDecisionInP hno⟩

/-! ## The tower decoration is still free -/

/-- Add a true, uniformly escaping Book 1 statement to an effective finite
compiler. -/
structure EffectiveTowerDiagonalizer
    (U : MachineModel) (V : CounterexampleCompilerModel)
    (T : UniformRosserTower) where
  compiler : EffectiveCodeDiagonalizer U V
  statement : Nat → T.Sentence
  statement_true : ∀ solverCode, T.True_ (statement solverCode)
  statement_escapes : ∀ solverCode n, ¬ T.Prov n (statement solverCode)

/-- The one tower escape supplies all meta-statements once an effective finite
compiler already exists. -/
def EffectiveTowerDiagonalizer.ofCompiler
    {U : MachineModel} {V : CounterexampleCompilerModel}
    {T : UniformRosserTower}
    (K : EffectiveCodeDiagonalizer U V) :
    EffectiveTowerDiagonalizer U V T where
  compiler := K
  statement := fun _ => T.escape
  statement_true := fun _ => T.escape_true
  statement_escapes := fun _ n => T.escape_unprovable n

/-- For a fixed operational compiler surface, tower decoration neither adds
nor removes a compiler: it is logically equivalent to the compiler alone. -/
theorem effectiveTowerDiagonalizer_iff_effectiveCodeDiagonalizer
    (U : MachineModel) (V : CounterexampleCompilerModel)
    (T : UniformRosserTower) :
    Nonempty (EffectiveTowerDiagonalizer U V T) ↔
      Nonempty (EffectiveCodeDiagonalizer U V) := by
  constructor
  · rintro ⟨K⟩
    exact ⟨K.compiler⟩
  · rintro ⟨K⟩
    exact ⟨EffectiveTowerDiagonalizer.ofCompiler K⟩

/-- Hence an effective tower diagonalizer on any fixed surface implies the SAT
lower bound solely through its finite compiler component. -/
theorem no_SATDecisionInP_of_effectiveTowerDiagonalizer
    {U : MachineModel} {V : CounterexampleCompilerModel}
    {T : UniformRosserTower}
    (K : EffectiveTowerDiagonalizer U V T) :
    ¬ SATDecisionInP U :=
  no_SATDecisionInP_of_effectiveCodeDiagonalizer K.compiler

end PallLean.Paper93.DeepMath.PathB.NFrameTowerEffectiveDiagonalCompilerAudit

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerEffectiveDiagonalCompilerAudit.no_SATDecisionInP_of_effectiveCodeDiagonalizer
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerEffectiveDiagonalCompilerAudit.no_effectiveCodeDiagonalizer_on_emptyModel
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerEffectiveDiagonalCompilerAudit.oracleEffectiveCodeDiagonalizer
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerEffectiveDiagonalCompilerAudit.exists_effectiveCompilerSurface_iff_no_SATDecisionInP
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerEffectiveDiagonalCompilerAudit.effectiveTowerDiagonalizer_iff_effectiveCodeDiagonalizer
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerEffectiveDiagonalCompilerAudit.no_SATDecisionInP_of_effectiveTowerDiagonalizer
