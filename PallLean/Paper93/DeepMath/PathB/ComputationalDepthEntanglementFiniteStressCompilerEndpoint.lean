import PallLean.Paper93.DeepMath.PathB.ComputationalDepthEntanglementFiniteRunExtractionNoGo

/-!
# Finite solver stress compiler: runtime-or-error collapses to error

The finite-run audit leaves one plausible operational target: assign every
certified polynomial SAT machine a concrete finite CNF on which either

1. the machine gives the wrong SAT answer, or
2. its execution exceeds its certified polynomial budget.

This file formalizes that target.  The second arm is impossible by the
definition of `DecisionMachine`, for every formula and independently of SAT
correctness.  Hence every successful stress family already supplies a finite
semantic counterexample to every machine and rules out `SATDecisionInP`.

Conversely, after assuming `¬ SATDecisionInP`, classical choice selects an
already-missed formula for each machine and makes it the constant stress
family.  Thus existence of an unrestricted stress family is exactly the SAT
lower bound.  The reverse construction is noncomputable and contains no
solver-to-counterexample algorithm.
-/

namespace PallLean.Paper93.DeepMath.PathB.EntanglementFiniteStressCompilerEndpoint

open SATDepthMachine

/-- Correctness of one machine on one finite CNF. -/
def CorrectOn (U : MachineModel) (D : DecisionMachine U) (φ : CNF) : Prop :=
  U.decisionRun D.code φ = true <-> Satisfiable φ

/-- A proposed uniform finite stress family.  Each certified machine receives
an explicit sequence of finite CNFs, one of which must expose either semantic
failure or a violation of its own runtime certificate. -/
structure FiniteRuntimeOrErrorStressFamily (U : MachineModel) where
  challenge : DecisionMachine U -> Nat -> CNF
  hits : forall D : DecisionMachine U, exists n : Nat,
    ¬ CorrectOn U D (challenge D n) \/
      D.budget (challenge D n).size <
        U.decisionSteps D.code (challenge D n)

/-! ## The runtime escape is definitionally closed -/

/-- A certified decision machine never exceeds its stated budget on a finite
formula. -/
theorem no_runtimeViolation
    {U : MachineModel} (D : DecisionMachine U) (φ : CNF) :
    ¬ D.budget φ.size < U.decisionSteps D.code φ := by
  exact Nat.not_lt_of_ge (D.steps_le_budget φ)

/-- Therefore every stress-family hit is necessarily a semantic error. -/
theorem FiniteRuntimeOrErrorStressFamily.exists_semantic_error
    {U : MachineModel} (F : FiniteRuntimeOrErrorStressFamily U)
    (D : DecisionMachine U) :
    exists n : Nat, ¬ CorrectOn U D (F.challenge D n) := by
  obtain ⟨n, hwrong | htime⟩ := F.hits D
  · exact ⟨n, hwrong⟩
  · exact False.elim (no_runtimeViolation D (F.challenge D n) htime)

/-- Every successful finite stress family rules out a correct polynomial SAT
decider. -/
theorem FiniteRuntimeOrErrorStressFamily.no_SATDecisionInP
    {U : MachineModel} (F : FiniteRuntimeOrErrorStressFamily U) :
    ¬ SATDecisionInP U := by
  rintro ⟨D, hD⟩
  obtain ⟨n, hwrong⟩ := F.exists_semantic_error D
  exact hwrong (hD (F.challenge D n))

/-! ## The reverse direction is noncomputable counterexample choice -/

/-- If there is no correct SAT decider, each individual certified machine
misses at least one finite CNF. -/
theorem exists_missed_formula_of_no_SATDecisionInP
    {U : MachineModel} (hNo : ¬ SATDecisionInP U)
    (D : DecisionMachine U) :
    exists φ : CNF, ¬ CorrectOn U D φ := by
  have hnot : ¬ DecidesSAT U D := by
    intro hD
    exact hNo ⟨D, hD⟩
  unfold DecidesSAT at hnot
  simpa [CorrectOn] using hnot

/-- Classical selection of one already-missed formula per machine. -/
noncomputable def chosenMissedFormula
    {U : MachineModel} (hNo : ¬ SATDecisionInP U)
    (D : DecisionMachine U) : CNF :=
  Classical.choose (exists_missed_formula_of_no_SATDecisionInP hNo D)

theorem chosenMissedFormula_is_missed
    {U : MachineModel} (hNo : ¬ SATDecisionInP U)
    (D : DecisionMachine U) :
    ¬ CorrectOn U D (chosenMissedFormula hNo D) :=
  Classical.choose_spec (exists_missed_formula_of_no_SATDecisionInP hNo D)

/-- The reverse stress family simply repeats the noncomputably selected
counterexample at every index. -/
noncomputable def stressFamily_of_no_SATDecisionInP
    {U : MachineModel} (hNo : ¬ SATDecisionInP U) :
    FiniteRuntimeOrErrorStressFamily U where
  challenge := fun D _ => chosenMissedFormula hNo D
  hits := by
    intro D
    exact ⟨0, Or.inl (chosenMissedFormula_is_missed hNo D)⟩

/-- Exact endpoint: an unrestricted finite runtime-or-error stress family
exists iff SAT has no certified polynomial decider. -/
theorem finiteStressFamily_iff_no_SATDecisionInP
    (U : MachineModel) :
    Nonempty (FiniteRuntimeOrErrorStressFamily U) <-> ¬ SATDecisionInP U := by
  constructor
  · rintro ⟨F⟩
    exact F.no_SATDecisionInP
  · intro hNo
    exact ⟨stressFamily_of_no_SATDecisionInP hNo⟩

/-- The chosen reverse family never uses the runtime-violation arm. -/
theorem chosenStressFamily_hit_is_semantic
    {U : MachineModel} (hNo : ¬ SATDecisionInP U)
    (D : DecisionMachine U) :
    ¬ CorrectOn U D ((stressFamily_of_no_SATDecisionInP hNo).challenge D 0) :=
  chosenMissedFormula_is_missed hNo D

end PallLean.Paper93.DeepMath.PathB.EntanglementFiniteStressCompilerEndpoint

#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementFiniteStressCompilerEndpoint.no_runtimeViolation
#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementFiniteStressCompilerEndpoint.FiniteRuntimeOrErrorStressFamily.exists_semantic_error
#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementFiniteStressCompilerEndpoint.FiniteRuntimeOrErrorStressFamily.no_SATDecisionInP
#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementFiniteStressCompilerEndpoint.finiteStressFamily_iff_no_SATDecisionInP
