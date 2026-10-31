import PallLean.Paper93.DeepMath.PathB.ComputationalDepthEntanglementRuntimeCalibrationEndpoint

/-!
# Construction-derived finite-run entanglement still has no hardness leverage

The runtime-calibration endpoint allowed an abstract charge.  The natural next
repair is to remove that freedom and derive the charge from actual finite
machine dynamics.  This file performs the strongest simple calibration:

* `emptyCNF n` is an explicit satisfiable formula of exact size `n`;
* `finiteRunCharge U D n` is exactly the machine model's recorded number of
  decision steps on that formula;
* the charge is automatically bounded by `D.budget n`, hence polynomial for
  every certified decision machine.

We then ask for the construction-derived hard statement saying this exact
finite-run profile is non-polynomial for every correct SAT decider.  Its
existence is again equivalent to `¬ SATDecisionInP U`: forward, it contradicts
the certified polynomial budget; backward, it holds vacuously when there are
no correct deciders.

Thus replacing an abstract entanglement observer with genuine run data removes
the zero-charge naming cheat, but does not supply the missing lower bound.  The
hardness theorem about those runs remains the separation itself.
-/

namespace PallLean.Paper93.DeepMath.PathB.EntanglementFiniteRunExtractionNoGo

open SATDepthMachine

/-! ## Explicit all-size finite probes -/

/-- A genuine CNF of exact syntactic size `n`, with `n` variables and no
clauses. -/
def emptyCNF (n : Nat) : CNF where
  vars := n
  clauses := []

theorem emptyCNF_size (n : Nat) : (emptyCNF n).size = n := by
  simp [emptyCNF, CNF.size]

/-- Every probe is satisfiable; the construction never answer-codes a hard
SAT bit. -/
theorem emptyCNF_satisfiable (n : Nat) : Satisfiable (emptyCNF n) := by
  refine ⟨List.replicate n false, ?_⟩
  constructor
  · simp [emptyCNF]
  · simp [emptyCNF, CNF.eval]

/-! ## The charge is the actual recorded finite runtime -/

/-- No observer choice: the charge is exactly the machine model's step count
on the explicit size-`n` probe. -/
def finiteRunCharge (U : MachineModel) (D : DecisionMachine U) (n : Nat) : Nat :=
  U.decisionSteps D.code (emptyCNF n)

/-- The actual run charge is pointwise below the machine's own budget at the
same input size. -/
theorem finiteRunCharge_le_budget
    (U : MachineModel) (D : DecisionMachine U) (n : Nat) :
    finiteRunCharge U D n <= D.budget n := by
  simpa [finiteRunCharge, emptyCNF_size] using
    D.steps_le_budget (emptyCNF n)

/-- Therefore the construction-derived charge is polynomial for every
certified machine, with no correctness assumption. -/
theorem finiteRunCharge_isPolynomialBudget
    (U : MachineModel) (D : DecisionMachine U) :
    IsPolynomialBudget (finiteRunCharge U D) := by
  obtain ⟨k, c, hbudget⟩ := D.polyBudget
  exact ⟨k, c, fun n => le_trans
    (finiteRunCharge_le_budget U D n) (hbudget n)⟩

/-! ## The demanded hard theorem and its exact strength -/

/-- The proposed construction-derived entanglement theorem: the actual probe
runtimes are non-polynomial for every correct SAT decider. -/
def FiniteRunEntanglementHard (U : MachineModel) : Prop :=
  forall D : DecisionMachine U,
    DecidesSAT U D -> ¬ IsPolynomialBudget (finiteRunCharge U D)

/-- Such a hard theorem immediately rules out polynomial SAT decision. -/
theorem no_SATDecisionInP_of_finiteRunEntanglementHard
    {U : MachineModel} (hHard : FiniteRunEntanglementHard U) :
    ¬ SATDecisionInP U := by
  rintro ⟨D, hD⟩
  exact hHard D hD (finiteRunCharge_isPolynomialBudget U D)

/-- Conversely, absence of a SAT decider makes the hard statement vacuous,
despite its charge being fully construction-derived. -/
theorem finiteRunEntanglementHard_of_no_SATDecisionInP
    {U : MachineModel} (hNo : ¬ SATDecisionInP U) :
    FiniteRunEntanglementHard U := by
  intro D hD
  exact False.elim (hNo ⟨D, hD⟩)

/-- Exact endpoint: hardness of the actual finite-run charge is precisely the
unrestricted SAT lower bound. -/
theorem finiteRunEntanglementHard_iff_no_SATDecisionInP
    (U : MachineModel) :
    FiniteRunEntanglementHard U <-> ¬ SATDecisionInP U := by
  constructor
  · exact no_SATDecisionInP_of_finiteRunEntanglementHard
  · exact finiteRunEntanglementHard_of_no_SATDecisionInP

/-- The attempted hard field is incompatible with even one correct certified
decider, because the extracted run profile is already proved polynomial. -/
theorem no_finiteRunEntanglementHard_of_decider
    {U : MachineModel} (hP : SATDecisionInP U) :
    ¬ FiniteRunEntanglementHard U := by
  intro hHard
  exact no_SATDecisionInP_of_finiteRunEntanglementHard hHard hP

end PallLean.Paper93.DeepMath.PathB.EntanglementFiniteRunExtractionNoGo

#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementFiniteRunExtractionNoGo.emptyCNF_satisfiable
#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementFiniteRunExtractionNoGo.finiteRunCharge_isPolynomialBudget
#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementFiniteRunExtractionNoGo.finiteRunEntanglementHard_iff_no_SATDecisionInP
#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementFiniteRunExtractionNoGo.no_finiteRunEntanglementHard_of_decider
