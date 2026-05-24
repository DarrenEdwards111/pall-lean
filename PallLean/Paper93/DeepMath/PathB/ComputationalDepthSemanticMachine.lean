import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMachineCompiler
import Mathlib.Data.Nat.Pairing
import Mathlib.Tactic

/-
# A self-reduction-closed semantic machine model

The previous files proved the SAT prefix-unit self-reduction and packaged the
compiler/accounting socket for an abstract `MachineModel`.

This file instantiates that socket for a concrete semantic closure model.  Codes
are natural numbers with one reserved search tag:

* tag `1`: a search code compiled from a decision code, interpreted by the
  bit-by-bit prefix self-reduction.

The decision and verifier behavior are supplied by `SemanticClosureSurface`.
That is intentional: this is not a universal Turing-machine interpreter.  It is
the exact semantic machine layer needed to show that the prefix-unit compiler is
no longer an informal paragraph.  The remaining lower bound is still precisely
`DeepSATSearch (semanticMachineModel S)`.
-/

namespace SATDepthMachine

/-! ## Tagged compiled-search codes -/

def compiledSearchTag : Nat := 1

def compiledSearchCode (decisionCode : Nat) : Nat :=
  Nat.pair compiledSearchTag decisionCode

/-- Core search semantics added by this file.  A compiled search code runs the
proved prefix-unit decision-to-search self-reduction against the decision code
stored in its payload; every other search code is delegated to the base search
surface. -/
def semanticSearchRunCore
    (baseSearchRun : Nat -> CNF -> Option RawAssignment)
    (decisionRun : Nat -> CNF -> Bool)
    (code : Nat) (φ : CNF) :
    Option RawAssignment :=
  if (Nat.unpair code).1 = compiledSearchTag then
    let decisionCode := (Nat.unpair code).2
    some (searchFromPrefixOracle
      (prefixOracleOfSATDecider prefixUnitCNFReduction
        (fun ψ => decisionRun decisionCode ψ)) φ)
  else
    baseSearchRun code φ

/-- Concrete step counter for the semantic compiled-search tag.  The compiled
tag is assigned a polynomial semantic cost; base search codes keep the supplied
base counter. -/
def semanticSearchStepsCore
    (baseSearchSteps : Nat -> CNF -> Nat)
    (code : Nat) (φ : CNF) : Nat :=
  if (Nat.unpair code).1 = compiledSearchTag then
    φ.size + 1
  else
    baseSearchSteps code φ

theorem semanticSearchRunCore_compiled
    (baseSearchRun : Nat -> CNF -> Option RawAssignment)
    (decisionRun : Nat -> CNF -> Bool)
    (decisionCode : Nat) (φ : CNF) :
    semanticSearchRunCore baseSearchRun decisionRun
        (compiledSearchCode decisionCode) φ =
      some (searchFromPrefixOracle
        (prefixOracleOfSATDecider prefixUnitCNFReduction
          (fun ψ => decisionRun decisionCode ψ)) φ) := by
  simp [semanticSearchRunCore, compiledSearchCode, compiledSearchTag]

theorem semanticSearchStepsCore_compiled
    (baseSearchSteps : Nat -> CNF -> Nat)
    (decisionCode : Nat) (φ : CNF) :
    semanticSearchStepsCore baseSearchSteps
        (compiledSearchCode decisionCode) φ = φ.size + 1 := by
  simp [semanticSearchStepsCore, compiledSearchCode, compiledSearchTag]

/-! ## Semantic closure surface -/

/-- Data needed to turn the compiled-search core into a full `MachineModel`.

The verifier fields are exactly the `MachineModel` verifier requirements for
the search semantics defined above.  They are not lower-bound assumptions. -/
structure SemanticClosureSurface where
  baseSearchRun : Nat -> CNF -> Option RawAssignment
  baseSearchSteps : Nat -> CNF -> Nat
  decisionRun : Nat -> CNF -> Bool
  decisionSteps : Nat -> CNF -> Nat
  verifierCode : Nat -> Nat
  verifier_run :
    ∀ (code : Nat) (φ : CNF),
      decisionRun (verifierCode code) φ =
        checkSearchOutput φ
          (semanticSearchRunCore baseSearchRun decisionRun code φ)
  verifier_steps :
    ∀ (code : Nat) (φ : CNF),
      decisionSteps (verifierCode code) φ =
        semanticSearchStepsCore baseSearchSteps code φ

/-- Search semantics for a semantic closure surface. -/
def semanticSearchRun
    (S : SemanticClosureSurface) (code : Nat) (φ : CNF) :
    Option RawAssignment :=
  semanticSearchRunCore S.baseSearchRun S.decisionRun code φ

/-- Step semantics for a semantic closure surface. -/
def semanticSearchSteps
    (S : SemanticClosureSurface) (code : Nat) (φ : CNF) : Nat :=
  semanticSearchStepsCore S.baseSearchSteps code φ

theorem semanticSearchRun_compiled
    (S : SemanticClosureSurface) (decisionCode : Nat) (φ : CNF) :
    semanticSearchRun S (compiledSearchCode decisionCode) φ =
      some (searchFromPrefixOracle
        (prefixOracleOfSATDecider prefixUnitCNFReduction
          (fun ψ => S.decisionRun decisionCode ψ)) φ) :=
  semanticSearchRunCore_compiled S.baseSearchRun S.decisionRun decisionCode φ

theorem semanticSearchSteps_compiled
    (S : SemanticClosureSurface) (decisionCode : Nat) (φ : CNF) :
    semanticSearchSteps S (compiledSearchCode decisionCode) φ = φ.size + 1 :=
  semanticSearchStepsCore_compiled S.baseSearchSteps decisionCode φ

/-- The semantic self-reduction-closed machine model. -/
def semanticMachineModel (S : SemanticClosureSurface) : MachineModel where
  searchRun := semanticSearchRun S
  searchSteps := semanticSearchSteps S
  decisionRun := S.decisionRun
  decisionSteps := S.decisionSteps
  verifierCode := S.verifierCode
  verifier_run := S.verifier_run
  verifier_steps := S.verifier_steps

theorem semanticCompiledBudget_poly :
    IsPolynomialBudget (fun n : Nat => n + 1) := by
  refine ⟨1, 1, ?_⟩
  intro n
  simp

/-- The concrete compiler/accounting instance for the semantic closure model. -/
def semanticPrefixUnitMachineCompiler
    (S : SemanticClosureSurface) :
    PrefixUnitMachineCompiler (semanticMachineModel S) where
  compileCode := fun D _hD => compiledSearchCode D.code
  budget := fun _D _hD n => n + 1
  polyBudget := fun _D _hD => semanticCompiledBudget_poly
  steps_le_budget := by
    intro D _hD φ
    simp [semanticMachineModel, semanticSearchSteps_compiled]
  run_eq := by
    intro D _hD φ
    simp [semanticMachineModel, semanticSearchRun_compiled]

/-- In the semantic closure model, the compiler layer is fully discharged:
computational depth of SAT search is equivalent to the no-polynomial SAT
decider statement for that same model. -/
theorem semanticDeepSATSearch_iff_no_decider
    (S : SemanticClosureSurface) :
    DeepSATSearch (semanticMachineModel S) ↔
      ¬ SATDecisionInP (semanticMachineModel S) :=
  deepSATSearch_iff_no_decider_with_prefixUnitCompiler
    (semanticPrefixUnitMachineCompiler S)

/-- Positive closure still requires the genuine metacomplexity lower bound. -/
def SemanticClosureRemainingLowerBound
    (S : SemanticClosureSurface) : Prop :=
  DeepSATSearch (semanticMachineModel S)

theorem semanticNoDecider_of_remainingLowerBound
    (S : SemanticClosureSurface)
    (hdeep : SemanticClosureRemainingLowerBound S) :
    ¬ SATDecisionInP (semanticMachineModel S) :=
  (semanticDeepSATSearch_iff_no_decider S).mp hdeep

/-! ## Kernel-only axiom trace -/

#print axioms semanticSearchRunCore_compiled
#print axioms semanticMachineModel
#print axioms semanticPrefixUnitMachineCompiler
#print axioms semanticDeepSATSearch_iff_no_decider
#print axioms semanticNoDecider_of_remainingLowerBound

end SATDepthMachine
