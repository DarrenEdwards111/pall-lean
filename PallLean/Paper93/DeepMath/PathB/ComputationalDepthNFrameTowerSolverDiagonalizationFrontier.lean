import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameTowerParameterizedEscapeNoGo

/-!
# N-Frame tower: solver-indexed finite diagonalization frontier

The preceding audit showed that a Rosser fixed point cannot be copied across
arbitrary SAT inputs.  The correctly typed alternative diagonalizes against
solver descriptions: given a certified polynomial decision machine, produce a
finite CNF on which that machine is wrong.

This file tests that replacement exactly.  A code-indexed finite diagonalizer
stores one counterexample CNF for every numeric machine code and must defeat
every polynomial-budget `DecisionMachine` carrying that code.  We prove that
existence of such a diagonalizer is equivalent to `¬ SATDecisionInP`.

The reverse construction is deliberately classical: from the assertion that
no polynomial SAT decider exists, choose a failing CNF for each code that has a
polynomial certificate.  It does not provide an effective compiler.

We then add the Book 1 tower data.  The same uniform Rosser escape can be used
as the meta-statement for every solver code, so the tower-decorated
diagonalizer is still equivalent to `¬ SATDecisionInP`.  Tower non-escape
certifies the vertical meta-level obstruction, but it does not compute the
finite counterexample.  The remaining load-bearing target is therefore an
effective, independently justified code-to-CNF compiler, not mere existence
of a solver-indexed escape family.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameTowerSolverDiagonalizationFrontier

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.NFrameGodelTowerSATBridgeAudit
open PallLean.Paper93.DeepMath.PathB.PvsNPDynamicHolonomyQueryTranscriptBridge

attribute [local instance] Classical.propDecidable

/-! ## Finite counterexamples to certified polynomial machines -/

/-- Correctness of numeric decision code `code` on one finite CNF. -/
def CorrectOn (U : MachineModel) (code : Nat) (φ : CNF) : Prop :=
  U.decisionRun code φ = true ↔ Satisfiable φ

/-- Every non-decider has a concrete finite input witnessing its failure. -/
theorem exists_finite_counterexample_of_not_decidesSAT
    {U : MachineModel} (M : DecisionMachine U)
    (hnot : ¬ DecidesSAT U M) :
    ∃ φ, ¬ CorrectOn U M.code φ := by
  unfold DecidesSAT at hnot
  simpa [CorrectOn] using (not_forall.mp hnot)

/-- If SAT has no polynomial decider, every certified polynomial decision
machine has a finite counterexample. -/
theorem exists_finite_counterexample_of_no_SATDecisionInP
    {U : MachineModel} (hno : ¬ SATDecisionInP U)
    (M : DecisionMachine U) :
    ∃ φ, ¬ CorrectOn U M.code φ := by
  apply exists_finite_counterexample_of_not_decidesSAT M
  intro hcorrect
  exact hno ⟨M, hcorrect⟩

/-- The same conclusion indexed by the numeric code.  The premise says that
the code actually carries at least one polynomial-budget certificate. -/
theorem exists_code_counterexample_of_no_SATDecisionInP
    {U : MachineModel} (hno : ¬ SATDecisionInP U)
    (code : Nat) (hcert : ∃ M : DecisionMachine U, M.code = code) :
    ∃ φ, ¬ CorrectOn U code φ := by
  rcases hcert with ⟨M, rfl⟩
  exact exists_finite_counterexample_of_no_SATDecisionInP hno M

/-- A single code-indexed assignment of finite counterexamples.  Codes without
a polynomial certificate are irrelevant; every certified polynomial machine
must fail on the CNF assigned to its code. -/
structure CodeIndexedFiniteDiagonalizer (U : MachineModel) where
  counterexample : Nat → CNF
  defeats : ∀ M : DecisionMachine U,
    ¬ CorrectOn U M.code (counterexample M.code)

/-- Classical choice extracts a code-indexed family from the already-assumed
lower bound.  This is existence, not an algorithm for producing the CNFs. -/
noncomputable def codeIndexedFiniteDiagonalizerOfNoSATDecisionInP
    {U : MachineModel} (hno : ¬ SATDecisionInP U) :
    CodeIndexedFiniteDiagonalizer U where
  counterexample := fun code =>
    if hcert : ∃ M : DecisionMachine U, M.code = code then
      Classical.choose
        (exists_code_counterexample_of_no_SATDecisionInP hno code hcert)
    else
      noCNF
  defeats := by
    intro M
    let hcert : ∃ D : DecisionMachine U, D.code = M.code := ⟨M, rfl⟩
    rw [dif_pos hcert]
    exact Classical.choose_spec
      (exists_code_counterexample_of_no_SATDecisionInP hno M.code hcert)

/-- A finite diagonalizer immediately refutes a purported globally correct
polynomial SAT decider. -/
theorem no_SATDecisionInP_of_codeIndexedFiniteDiagonalizer
    {U : MachineModel} (D : CodeIndexedFiniteDiagonalizer U) :
    ¬ SATDecisionInP U := by
  rintro ⟨M, hcorrect⟩
  exact D.defeats M (hcorrect (D.counterexample M.code))

/-- **Exact finite-diagonal frontier.**  Merely asserting one finite failing
CNF per polynomial machine code is equivalent to the desired SAT lower bound. -/
theorem codeIndexedFiniteDiagonalizer_iff_no_SATDecisionInP
    (U : MachineModel) :
    Nonempty (CodeIndexedFiniteDiagonalizer U) ↔ ¬ SATDecisionInP U := by
  constructor
  · rintro ⟨D⟩
    exact no_SATDecisionInP_of_codeIndexedFiniteDiagonalizer D
  · intro hno
    exact ⟨codeIndexedFiniteDiagonalizerOfNoSATDecisionInP hno⟩

/-! ## Adding the tower does not manufacture the finite compiler -/

/-- The solver-indexed Book 1 package: a true sentence outside every finite
rung, plus a genuine finite counterexample to each certified polynomial code. -/
structure SolverIndexedTowerDiagonalizer
    (U : MachineModel) (T : UniformRosserTower) where
  finite : CodeIndexedFiniteDiagonalizer U
  statement : Nat → T.Sentence
  statement_true : ∀ code, T.True_ (statement code)
  statement_escapes : ∀ code n, ¬ T.Prov n (statement code)

/-- Once the finite diagonalizer is supplied, the tower decoration is free:
the one uniform Rosser sentence can label every solver code. -/
def SolverIndexedTowerDiagonalizer.ofFinite
    {U : MachineModel} {T : UniformRosserTower}
    (D : CodeIndexedFiniteDiagonalizer U) :
    SolverIndexedTowerDiagonalizer U T where
  finite := D
  statement := fun _ => T.escape
  statement_true := fun _ => T.escape_true
  statement_escapes := fun _ n => T.escape_unprovable n

/-- **Tower-decorated frontier.**  Adding true, uniformly escaping Book 1
meta-sentences changes no finite complexity strength: existence of the whole
package remains exactly `SAT ∉ P` in the repository machine semantics. -/
theorem solverIndexedTowerDiagonalizer_iff_no_SATDecisionInP
    (U : MachineModel) (T : UniformRosserTower) :
    Nonempty (SolverIndexedTowerDiagonalizer U T) ↔ ¬ SATDecisionInP U := by
  constructor
  · rintro ⟨D⟩
    exact no_SATDecisionInP_of_codeIndexedFiniteDiagonalizer D.finite
  · intro hno
    exact
      ⟨SolverIndexedTowerDiagonalizer.ofFinite
        (codeIndexedFiniteDiagonalizerOfNoSATDecisionInP hno)⟩

/-- Every solver-indexed tower statement is absent from the finite union. -/
theorem SolverIndexedTowerDiagonalizer.statement_not_in_union
    {U : MachineModel} {T : UniformRosserTower}
    (D : SolverIndexedTowerDiagonalizer U T) (code : Nat) :
    ¬ T.InUnion (D.statement code) := by
  rintro ⟨n, hn⟩
  exact D.statement_escapes code n hn

end PallLean.Paper93.DeepMath.PathB.NFrameTowerSolverDiagonalizationFrontier

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerSolverDiagonalizationFrontier.exists_finite_counterexample_of_not_decidesSAT
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerSolverDiagonalizationFrontier.exists_finite_counterexample_of_no_SATDecisionInP
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerSolverDiagonalizationFrontier.codeIndexedFiniteDiagonalizer_iff_no_SATDecisionInP
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerSolverDiagonalizationFrontier.solverIndexedTowerDiagonalizer_iff_no_SATDecisionInP
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerSolverDiagonalizationFrontier.SolverIndexedTowerDiagonalizer.statement_not_in_union
