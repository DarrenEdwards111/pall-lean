import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCanonicalMachineTarget

/-
# Universal canonical surface and completeness target

The closed canonical surface is concrete but not universal.  This file adds the
next layer needed for the positive route: an intended oracle-free machine class
and a completeness map from that class into a canonical small-step surface.

This file still does not prove P vs NP.  It proves the exact metatheorem:

  if an intended machine class is complete for a canonical surface, and that
  canonical surface has deep SAT search, then no represented intended
  polynomial-time SAT decider exists.

Thus the remaining constructive work is now explicit:

* build a real universal oracle-free `CanonicalMachineSurface`;
* prove `UniversalCanonicalCompleteness` for the intended machine class;
* prove `CanonicalDeepSATSearch` for that surface.
-/

namespace SATDepthMachine

/-! ## Intended oracle-free machine classes -/

/-- A machine class outside the canonical surface, used as the source language
for a universality/completeness theorem. -/
structure IntendedMachineClass where
  SearchProgram : Type
  DecisionProgram : Type
  searchRun : SearchProgram -> CNF -> Option RawAssignment
  searchSteps : SearchProgram -> CNF -> Nat
  decisionRun : DecisionProgram -> CNF -> Bool
  decisionSteps : DecisionProgram -> CNF -> Nat
  oracleFree : Prop
  oracleFree_cert : oracleFree

/-- Polynomial-budget search program in an intended class. -/
structure IntendedSearchMachine (E : IntendedMachineClass) where
  program : E.SearchProgram
  budget : Nat -> Nat
  polyBudget : IsPolynomialBudget budget
  steps_le_budget :
    ∀ φ : CNF, E.searchSteps program φ ≤ budget φ.size

/-- Polynomial-budget decision program in an intended class. -/
structure IntendedDecisionMachine (E : IntendedMachineClass) where
  program : E.DecisionProgram
  budget : Nat -> Nat
  polyBudget : IsPolynomialBudget budget
  steps_le_budget :
    ∀ φ : CNF, E.decisionSteps program φ ≤ budget φ.size

/-- Search correctness in an intended machine class. -/
def IntendedSearchCorrect
    (E : IntendedMachineClass) (M : IntendedSearchMachine E) : Prop :=
  ∀ φ : CNF, Satisfiable φ ->
    ∃ a : RawAssignment, E.searchRun M.program φ = some a ∧ Satisfies φ a

/-- Decision correctness in an intended machine class. -/
def IntendedDecidesSAT
    (E : IntendedMachineClass) (M : IntendedDecisionMachine E) : Prop :=
  ∀ φ : CNF, E.decisionRun M.program φ = true ↔ Satisfiable φ

/-- Shallow SAT search in the intended class. -/
def IntendedShallowSATSearch (E : IntendedMachineClass) : Prop :=
  ∃ M : IntendedSearchMachine E, IntendedSearchCorrect E M

/-- SAT decision in polynomial time in the intended class. -/
def IntendedSATDecisionInP (E : IntendedMachineClass) : Prop :=
  ∃ M : IntendedDecisionMachine E, IntendedDecidesSAT E M

/-- The intended class's own oracle-free certificate. -/
abbrev IntendedOracleFree (E : IntendedMachineClass) : Prop :=
  E.oracleFree

theorem intendedOracleFree_cert
    (E : IntendedMachineClass) : IntendedOracleFree E :=
  E.oracleFree_cert

/-! ## Completeness into a canonical surface -/

/-- Completeness of an intended machine class for a canonical small-step
surface.

The two compile maps are code generators.  The run-equality fields say that the
canonical surface faithfully simulates the intended program.  The step-bound
fields say the compiled canonical code stays within the original polynomial
budget of each intended program. -/
structure UniversalCanonicalCompleteness
    (E : IntendedMachineClass) (C : CanonicalMachineSurface) where
  compileSearchCode : E.SearchProgram -> Nat
  compileDecisionCode : E.DecisionProgram -> Nat
  search_run_eq :
    ∀ (P : E.SearchProgram) (φ : CNF),
      C.searchRun (compileSearchCode P) φ = E.searchRun P φ
  decision_run_eq :
    ∀ (P : E.DecisionProgram) (φ : CNF),
      C.decisionRun (compileDecisionCode P) φ = E.decisionRun P φ
  search_steps_le_budget :
    ∀ (M : IntendedSearchMachine E) (φ : CNF),
      C.searchRuntime (compileSearchCode M.program) φ ≤ M.budget φ.size
  decision_steps_le_budget :
    ∀ (M : IntendedDecisionMachine E) (φ : CNF),
      C.decisionRuntime (compileDecisionCode M.program) φ ≤ M.budget φ.size

/-- Compile an intended search machine into the canonical surface. -/
def UniversalCanonicalCompleteness.toSearchMachine
    {E : IntendedMachineClass} {C : CanonicalMachineSurface}
    (H : UniversalCanonicalCompleteness E C)
    (M : IntendedSearchMachine E) :
    SearchMachine C.toMachineModel where
  code := H.compileSearchCode M.program
  budget := M.budget
  polyBudget := M.polyBudget
  steps_le_budget := H.search_steps_le_budget M

/-- Compile an intended decision machine into the canonical surface. -/
def UniversalCanonicalCompleteness.toDecisionMachine
    {E : IntendedMachineClass} {C : CanonicalMachineSurface}
    (H : UniversalCanonicalCompleteness E C)
    (M : IntendedDecisionMachine E) :
    DecisionMachine C.toMachineModel where
  code := H.compileDecisionCode M.program
  budget := M.budget
  polyBudget := M.polyBudget
  steps_le_budget := H.decision_steps_le_budget M

/-- Intended shallow SAT search transfers to canonical shallow SAT search. -/
theorem canonicalShallowSATSearch_of_intendedShallowSATSearch
    {E : IntendedMachineClass} {C : CanonicalMachineSurface}
    (H : UniversalCanonicalCompleteness E C)
    (hshallow : IntendedShallowSATSearch E) :
    ShallowSATSearch C.toMachineModel := by
  rcases hshallow with ⟨M, hM⟩
  refine ⟨H.toSearchMachine M, ?_⟩
  intro φ hsat
  rcases hM φ hsat with ⟨a, hrun, ha⟩
  refine ⟨a, ?_, ha⟩
  change C.searchRun (H.compileSearchCode M.program) φ = some a
  rw [H.search_run_eq]
  exact hrun

/-- Intended polynomial SAT decision transfers to canonical polynomial SAT
decision. -/
theorem canonicalSATDecisionInP_of_intendedSATDecisionInP
    {E : IntendedMachineClass} {C : CanonicalMachineSurface}
    (H : UniversalCanonicalCompleteness E C)
    (hdec : IntendedSATDecisionInP E) :
    CanonicalSATDecisionInP C := by
  rcases hdec with ⟨M, hM⟩
  refine ⟨H.toDecisionMachine M, ?_⟩
  intro φ
  change C.decisionRun (H.compileDecisionCode M.program) φ = true ↔
    Satisfiable φ
  rw [H.decision_run_eq]
  exact hM φ

/-- A canonical depth lower bound rules out intended shallow search once the
intended class is complete for the canonical surface. -/
theorem no_intendedShallowSATSearch_of_canonicalDeepSATSearch
    {E : IntendedMachineClass} {C : CanonicalMachineSurface}
    (H : UniversalCanonicalCompleteness E C)
    (hdeep : CanonicalDeepSATSearch C) :
    ¬ IntendedShallowSATSearch E := by
  intro hshallow
  exact hdeep (canonicalShallowSATSearch_of_intendedShallowSATSearch H hshallow)

/-- A canonical depth lower bound rules out intended polynomial SAT decision
once the intended class is complete for the canonical surface. -/
theorem no_intendedSATDecisionInP_of_canonicalDeepSATSearch
    {E : IntendedMachineClass} {C : CanonicalMachineSurface}
    (H : UniversalCanonicalCompleteness E C)
    (hdeep : CanonicalDeepSATSearch C) :
    ¬ IntendedSATDecisionInP E := by
  intro hdec
  have hcanonical : CanonicalSATDecisionInP C :=
    canonicalSATDecisionInP_of_intendedSATDecisionInP H hdec
  exact (canonicalNoDecider_of_deepSATSearch C hdeep) hcanonical

/-! ## Packaged universal target -/

/-- A universal canonical package: an intended oracle-free machine class, a
canonical oracle-free surface, and a completeness proof from the intended class
into that surface. -/
structure UniversalCanonicalSurface where
  intended : IntendedMachineClass
  surface : CanonicalMachineSurface
  completeness : UniversalCanonicalCompleteness intended surface

abbrev UniversalCanonicalDeepSATSearch
    (U : UniversalCanonicalSurface) : Prop :=
  CanonicalDeepSATSearch U.surface

abbrev UniversalIntendedSATDecisionInP
    (U : UniversalCanonicalSurface) : Prop :=
  IntendedSATDecisionInP U.intended

abbrev UniversalIntendedShallowSATSearch
    (U : UniversalCanonicalSurface) : Prop :=
  IntendedShallowSATSearch U.intended

theorem universalNoIntendedShallowSATSearch_of_deepSATSearch
    (U : UniversalCanonicalSurface)
    (hdeep : UniversalCanonicalDeepSATSearch U) :
    ¬ UniversalIntendedShallowSATSearch U :=
  no_intendedShallowSATSearch_of_canonicalDeepSATSearch
    U.completeness hdeep

theorem universalNoIntendedSATDecisionInP_of_deepSATSearch
    (U : UniversalCanonicalSurface)
    (hdeep : UniversalCanonicalDeepSATSearch U) :
    ¬ UniversalIntendedSATDecisionInP U :=
  no_intendedSATDecisionInP_of_canonicalDeepSATSearch
    U.completeness hdeep

/-! ## Kernel-only axiom trace -/

#print axioms UniversalCanonicalCompleteness.toSearchMachine
#print axioms UniversalCanonicalCompleteness.toDecisionMachine
#print axioms canonicalShallowSATSearch_of_intendedShallowSATSearch
#print axioms canonicalSATDecisionInP_of_intendedSATDecisionInP
#print axioms no_intendedSATDecisionInP_of_canonicalDeepSATSearch
#print axioms universalNoIntendedSATDecisionInP_of_deepSATSearch

end SATDepthMachine
