import PallLean.Paper93.DeepMath.PathB.ComputationalDepthEntanglementFiniteStressCompilerEndpoint
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameTowerEffectiveDiagonalCompilerAudit

/-!
# Entanglement and tower routes share one finite endpoint

The entanglement audit ends with a finite stress family indexed by certified
machines.  The tower audit ends with a finite counterexample family indexed by
numeric solver codes, and then an effective compiler on a chosen execution
surface.  This file identifies those endpoints exactly.

The strongest direct map is constructive: a code-indexed counterexample is a
stress family constant in its auxiliary index.  The reverse map is
noncomputable: from a stress family we first obtain `¬ SATDecisionInP`, then use
the tower audit's classical choice of one counterexample for each certified
code.  Likewise, a variable compiler surface can always hide that chosen
family in an oracle run relation.

Consequently the following three existence statements are equivalent:

* finite entanglement stress family;
* code-indexed finite tower diagonalizer;
* effective code diagonalizer on some witness-chosen compiler surface.

All are exactly `¬ SATDecisionInP`.  Only an effective compiler on an
independently fixed surface could contain additional constructive content.
-/

namespace PallLean.Paper93.DeepMath.PathB.EntanglementTowerUnifiedFiniteEndpoint

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.EntanglementFiniteStressCompilerEndpoint
open PallLean.Paper93.DeepMath.PathB.NFrameTowerSolverDiagonalizationFrontier
open PallLean.Paper93.DeepMath.PathB.NFrameTowerEffectiveDiagonalCompilerAudit

/-! ## Direct code-indexed family to entanglement stress family -/

/-- Correctness on a machine and correctness on its numeric code are the same
predicate. -/
theorem correctOn_machine_iff_code
    {U : MachineModel} (D : DecisionMachine U) (φ : CNF) :
    EntanglementFiniteStressCompilerEndpoint.CorrectOn U D φ <->
      NFrameTowerSolverDiagonalizationFrontier.CorrectOn U D.code φ :=
  Iff.rfl

/-- A code-indexed diagonalizer constructively yields a stress family; no
choice or tower data is used. -/
def stressFamilyOfCodeIndexed
    {U : MachineModel} (K : CodeIndexedFiniteDiagonalizer U) :
    FiniteRuntimeOrErrorStressFamily U where
  challenge := fun D _ => K.counterexample D.code
  hits := by
    intro D
    exact ⟨0, Or.inl (K.defeats D)⟩

theorem stressFamilyOfCodeIndexed_challenge
    {U : MachineModel} (K : CodeIndexedFiniteDiagonalizer U)
    (D : DecisionMachine U) (n : Nat) :
    (stressFamilyOfCodeIndexed K).challenge D n = K.counterexample D.code :=
  rfl

/-! ## The reverse direction factors through the separation -/

/-- Recovering one counterexample per numeric code from a machine-indexed
stress family uses the tower audit's noncomputable choice construction. -/
noncomputable def codeIndexedOfStressFamily
    {U : MachineModel} (F : FiniteRuntimeOrErrorStressFamily U) :
    CodeIndexedFiniteDiagonalizer U :=
  codeIndexedFiniteDiagonalizerOfNoSATDecisionInP F.no_SATDecisionInP

/-- A stress family can also be turned into an apparently effective compiler
only by choosing the oracle surface that already contains those answers. -/
noncomputable def oracleCompilerOfStressFamily
    {U : MachineModel} (F : FiniteRuntimeOrErrorStressFamily U) :
    Sigma fun V : CounterexampleCompilerModel => EffectiveCodeDiagonalizer U V :=
  let K := codeIndexedOfStressFamily F
  ⟨oracleCompilerModel K, oracleEffectiveCodeDiagonalizer K⟩

/-- Conversely, any effective compiler on any fixed surface gives a stress
family after erasing to its SAT lower-bound consequence.  The extraction is
noncomputable because the stress-family representation chooses explicit
challenges from the negative correctness statement. -/
noncomputable def stressFamilyOfEffectiveCompiler
    {U : MachineModel} {V : CounterexampleCompilerModel}
    (K : EffectiveCodeDiagonalizer U V) :
    FiniteRuntimeOrErrorStressFamily U :=
  stressFamily_of_no_SATDecisionInP
    (no_SATDecisionInP_of_effectiveCodeDiagonalizer K)

/-! ## Complete equivalence line -/

theorem stressFamily_iff_codeIndexedDiagonalizer
    (U : MachineModel) :
    Nonempty (FiniteRuntimeOrErrorStressFamily U) <->
      Nonempty (CodeIndexedFiniteDiagonalizer U) := by
  constructor
  · rintro ⟨F⟩
    exact ⟨codeIndexedOfStressFamily F⟩
  · rintro ⟨K⟩
    exact ⟨stressFamilyOfCodeIndexed K⟩

theorem stressFamily_iff_variableSurfaceEffectiveCompiler
    (U : MachineModel) :
    Nonempty (FiniteRuntimeOrErrorStressFamily U) <->
      Nonempty (Sigma fun V : CounterexampleCompilerModel =>
        EffectiveCodeDiagonalizer U V) := by
  constructor
  · rintro ⟨F⟩
    exact ⟨oracleCompilerOfStressFamily F⟩
  · rintro ⟨⟨_V, K⟩⟩
    exact ⟨stressFamilyOfEffectiveCompiler K⟩

/-- Unified endpoint for both research branches. -/
theorem entanglement_tower_effective_exact_endpoint
    (U : MachineModel) :
    (Nonempty (FiniteRuntimeOrErrorStressFamily U) <->
      Nonempty (CodeIndexedFiniteDiagonalizer U)) /\
    (Nonempty (CodeIndexedFiniteDiagonalizer U) <->
      ¬ SATDecisionInP U) /\
    (Nonempty (Sigma fun V : CounterexampleCompilerModel =>
      EffectiveCodeDiagonalizer U V) <->
      ¬ SATDecisionInP U) := by
  exact ⟨stressFamily_iff_codeIndexedDiagonalizer U,
    codeIndexedFiniteDiagonalizer_iff_no_SATDecisionInP U,
    exists_effectiveCompilerSurface_iff_no_SATDecisionInP U⟩

end PallLean.Paper93.DeepMath.PathB.EntanglementTowerUnifiedFiniteEndpoint

#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementTowerUnifiedFiniteEndpoint.correctOn_machine_iff_code
#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementTowerUnifiedFiniteEndpoint.stressFamilyOfCodeIndexed
#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementTowerUnifiedFiniteEndpoint.stressFamily_iff_codeIndexedDiagonalizer
#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementTowerUnifiedFiniteEndpoint.entanglement_tower_effective_exact_endpoint
