import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRuntimeFaithfulGodMoveFrame

/-
# No-go audit for constructing a super-polynomial runtime-faithful frame

`ComputationalDepthRuntimeFaithfulGodMoveFrame` identified the exact positive
object that would close the route:

  a runtime-faithful God-Move frame with super-polynomial family mass.

This file proves why constructing that object is the hard theorem, not a
remaining Lean-plumbing task.  If any correct polynomial SAT search machine
exists, runtime faithfulness forces the frame's family mass to be polynomially
bounded by that machine's runtime budget.  Therefore no super-polynomial
runtime-faithful frame can coexist with shallow SAT search.
-/

namespace SATDepthMachine

/-! ## A generic domination guard -/

/-- A profile that is pointwise below a polynomial profile cannot be
super-polynomial in the sense used by the God-Move route. -/
theorem not_superPolynomialMass_of_polynomialTransportCapacity
    {mass : Nat -> Nat}
    (hcap : PolynomialTransportCapacity mass) :
    ¬ SuperPolynomialMass mass := by
  intro hsuper
  rcases hcap with ⟨B, hBpoly, hmass_le_B⟩
  rcases hsuper B hBpoly with ⟨n, hB_lt_mass⟩
  exact (Nat.not_lt_of_ge (hmass_le_B n)) hB_lt_mass

/-! ## Runtime faithfulness plus correctness polynomially bounds family mass -/

/-- For a correct SAT searcher, a runtime-faithful frame's whole family mass is
bounded by the searcher's runtime budget.  Correctness transports every
certified satisfiable challenge; runtime faithfulness injects those transported
events into one size-`n` computation budget. -/
theorem godMoveFamilyMass_le_budget_of_runtimeFaithful_and_searchCorrect
    {C : CanonicalMachineSurface}
    (R : RuntimeFaithfulGodMoveFrame C)
    (M : SearchMachine C.toMachineModel)
    (hM : SearchCorrect C.toMachineModel M)
    (n : Nat) :
    R.frame.familyMass n <= M.budget n := by
  have hfamily_le_transport :
      R.frame.familyMass n <= GodMoveFrame.transportedMass R.frame M n :=
    godMove_faithfulTransport_of_searchCorrect R.frame M hM n
  have htransport_le_budget :
      GodMoveFrame.transportedMass R.frame M n <= M.budget n :=
    godMoveTransportedMassConsumesRuntimeBudget_of_runtimeFaithful R M hM n
  exact Nat.le_trans hfamily_le_transport htransport_le_budget

/-- Hence a runtime-faithful frame has polynomial family mass whenever a correct
polynomial SAT searcher exists. -/
theorem polynomialFamilyMass_of_runtimeFaithful_and_searchCorrect
    {C : CanonicalMachineSurface}
    (R : RuntimeFaithfulGodMoveFrame C)
    (M : SearchMachine C.toMachineModel)
    (hM : SearchCorrect C.toMachineModel M) :
    PolynomialTransportCapacity R.frame.familyMass := by
  exact ⟨M.budget, M.polyBudget,
    godMoveFamilyMass_le_budget_of_runtimeFaithful_and_searchCorrect R M hM⟩

/-- A runtime-faithful frame with super-polynomial family mass is incompatible
with one correct polynomial SAT searcher. -/
theorem not_godMoveFamilyMassLowerBound_of_runtimeFaithful_and_searchCorrect
    {C : CanonicalMachineSurface}
    (R : RuntimeFaithfulGodMoveFrame C)
    (M : SearchMachine C.toMachineModel)
    (hM : SearchCorrect C.toMachineModel M) :
    ¬ GodMoveFamilyMassLowerBound R.frame :=
  not_superPolynomialMass_of_polynomialTransportCapacity
    (polynomialFamilyMass_of_runtimeFaithful_and_searchCorrect R M hM)

/-! ## Construction of the target object is P-vs-NP-strength -/

/-- The positive construction target: a runtime-faithful God-Move frame whose
family mass is super-polynomial. -/
def RuntimeFaithfulGodMoveLowerBoundConstruction
    (C : CanonicalMachineSurface) : Prop :=
  ∃ R : RuntimeFaithfulGodMoveFrame C,
    GodMoveFamilyMassLowerBound R.frame

/-- If shallow SAT search exists, the runtime-faithful lower-bound construction
cannot exist. -/
theorem not_runtimeFaithfulGodMoveLowerBoundConstruction_of_shallowSearch
    {C : CanonicalMachineSurface}
    (hshallow : ShallowSATSearch C.toMachineModel) :
    ¬ RuntimeFaithfulGodMoveLowerBoundConstruction C := by
  intro hconstruct
  rcases hshallow with ⟨M, hM⟩
  rcases hconstruct with ⟨R, hlower⟩
  exact not_godMoveFamilyMassLowerBound_of_runtimeFaithful_and_searchCorrect
    R M hM hlower

/-- Conversely, constructing the target object rules out shallow SAT search.
This is the direct form of the existing closure theorem. -/
theorem deepSATSearch_of_runtimeFaithfulGodMoveLowerBoundConstruction
    (C : CanonicalMachineSurface)
    (hconstruct : RuntimeFaithfulGodMoveLowerBoundConstruction C) :
    DeepSATSearch C.toMachineModel := by
  intro hshallow
  exact not_runtimeFaithfulGodMoveLowerBoundConstruction_of_shallowSearch
    hshallow hconstruct

/-- The construction target closes canonical SAT decision. -/
theorem noCanonicalSATDecisionInP_of_runtimeFaithfulGodMoveLowerBoundConstruction
    (C : CanonicalMachineSurface)
    (hconstruct : RuntimeFaithfulGodMoveLowerBoundConstruction C) :
    ¬ CanonicalSATDecisionInP C :=
  canonicalNoDecider_of_deepSATSearch C
    (deepSATSearch_of_runtimeFaithfulGodMoveLowerBoundConstruction
      C hconstruct)

/-! ## Axiom trace -/

#print axioms not_superPolynomialMass_of_polynomialTransportCapacity
#print axioms godMoveFamilyMass_le_budget_of_runtimeFaithful_and_searchCorrect
#print axioms polynomialFamilyMass_of_runtimeFaithful_and_searchCorrect
#print axioms not_godMoveFamilyMassLowerBound_of_runtimeFaithful_and_searchCorrect
#print axioms not_runtimeFaithfulGodMoveLowerBoundConstruction_of_shallowSearch
#print axioms deepSATSearch_of_runtimeFaithfulGodMoveLowerBoundConstruction
#print axioms noCanonicalSATDecisionInP_of_runtimeFaithfulGodMoveLowerBoundConstruction

end SATDepthMachine
