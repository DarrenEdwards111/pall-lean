import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPrefixCNFReduction

/-
# Machine compiler/accounting socket for the concrete prefix-unit reduction

`ComputationalDepthPrefixCNFReduction.lean` proves the semantic SAT
decision-to-search self-reduction using concrete unit clauses.

This file packages the remaining implementation requirement for a chosen coded
machine model `U`: compile a SAT decider code into the bit-by-bit searcher code
and certify its polynomial step budget.

The file does not assert that such a compiler exists for every `MachineModel`;
that would require a concrete universal-machine development.  Instead it shows
that once the compiler/accounting data exists, the earlier
`DecisionToSearchSelfReduction` socket is fully discharged for the concrete
prefix-unit CNF reduction.
-/

namespace SATDepthMachine

/-- Concrete machine-level compiler for the prefix-unit self-reduction.

The `budget` and `steps_le_budget` fields are the polynomial-overhead
accounting: the compiled searcher may ask at most linearly many SAT queries, and
the chosen machine model must certify the resulting runtime bound. -/
structure PrefixUnitMachineCompiler (U : MachineModel) where
  compileCode :
    (D : DecisionMachine U) -> DecidesSAT U D -> Nat
  budget :
    (D : DecisionMachine U) -> DecidesSAT U D -> Nat -> Nat
  polyBudget :
    ∀ (D : DecisionMachine U) (hD : DecidesSAT U D),
      IsPolynomialBudget (budget D hD)
  steps_le_budget :
    ∀ (D : DecisionMachine U) (hD : DecidesSAT U D) (φ : CNF),
      U.searchSteps (compileCode D hD) φ ≤ budget D hD φ.size
  run_eq :
    ∀ (D : DecisionMachine U) (hD : DecidesSAT U D) (φ : CNF),
      U.searchRun (compileCode D hD) φ =
        some (searchFromPrefixOracle
          (prefixOracleOfSATDecider prefixUnitCNFReduction
            (fun ψ => U.decisionRun D.code ψ)) φ)

/-- The compiled search machine associated to a decider. -/
def PrefixUnitMachineCompiler.toSearchMachine
    {U : MachineModel}
    (C : PrefixUnitMachineCompiler U)
    (D : DecisionMachine U)
    (hD : DecidesSAT U D) : SearchMachine U where
  code := C.compileCode D hD
  budget := C.budget D hD
  polyBudget := C.polyBudget D hD
  steps_le_budget := C.steps_le_budget D hD

/-- A concrete prefix-unit compiler discharges the generic
`MachineDecisionToSearchCompiler` socket. -/
def PrefixUnitMachineCompiler.toMachineDecisionToSearchCompiler
    {U : MachineModel}
    (C : PrefixUnitMachineCompiler U) :
    MachineDecisionToSearchCompiler U prefixUnitCNFReduction where
  compile := C.toSearchMachine
  run_eq := C.run_eq

/-- A concrete prefix-unit compiler gives the decision-to-search
self-reduction for `U`. -/
def PrefixUnitMachineCompiler.toSelfReduction
    {U : MachineModel}
    (C : PrefixUnitMachineCompiler U) :
    DecisionToSearchSelfReduction U :=
  C.toMachineDecisionToSearchCompiler.toSelfReduction

/-- With the concrete compiler/accounting layer in place, computational-depth
SAT search is equivalent to the no-polynomial-SAT-decider statement for `U`. -/
theorem deepSATSearch_iff_no_decider_with_prefixUnitCompiler
    {U : MachineModel}
    (C : PrefixUnitMachineCompiler U) :
    DeepSATSearch U ↔ ¬ SATDecisionInP U :=
  deepSATSearch_iff_no_decider_with_selfReduction C.toSelfReduction

/-- Contrapositive form useful for the positive program: a proof of
`DeepSATSearch` closes the SAT decider lower bound once the concrete compiler is
available. -/
theorem no_decider_of_deepSATSearch_with_prefixUnitCompiler
    {U : MachineModel}
    (C : PrefixUnitMachineCompiler U)
    (hdeep : DeepSATSearch U) :
    ¬ SATDecisionInP U :=
  (deepSATSearch_iff_no_decider_with_prefixUnitCompiler C).mp hdeep

/-! ## Kernel-only axiom trace -/

#print axioms PrefixUnitMachineCompiler.toSearchMachine
#print axioms PrefixUnitMachineCompiler.toMachineDecisionToSearchCompiler
#print axioms PrefixUnitMachineCompiler.toSelfReduction
#print axioms deepSATSearch_iff_no_decider_with_prefixUnitCompiler
#print axioms no_decider_of_deepSATSearch_with_prefixUnitCompiler

end SATDepthMachine
