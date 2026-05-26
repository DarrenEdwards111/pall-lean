import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDiagonalSATSelfReference

/-
# Restricted concrete instance: blind SAT searchers

This file gives a genuinely constructive end-to-end instance of the diagonal
SAT self-reference shape on a weak restricted class.

The restricted class is `BlindSearchMachine`: machines that always return
`none`.  For this class, we can construct a satisfiable CNF missed by every
machine in the class, and package the full diagonal self-reference object.

This is not a P-vs-NP result.  It is a concrete sanity check that the bridge
shape can be instantiated non-vacuously on a weak class.
-/

namespace SATDepthMachine

/-- Weak restricted class: the machine never outputs a candidate witness. -/
def BlindSearchMachine
    (U : MachineModel)
    (M : SearchMachine U) : Prop :=
  ∀ φ : CNF, U.searchRun M.code φ = none

/-- A fixed satisfiable CNF used for the restricted-class construction. -/
def trivialSATFormula : CNF :=
  { vars := 0, clauses := [] }

/-- `trivialSATFormula` is satisfiable by the empty assignment. -/
theorem trivialSATFormula_satisfiable :
    Satisfiable trivialSATFormula := by
  refine ⟨[], ?_⟩
  unfold Satisfies trivialSATFormula CNF.eval
  simp

/-- Any blind machine fails on every formula, in particular on
`trivialSATFormula`. -/
theorem searchFailureOnFormula_of_blind
    (U : MachineModel)
    (M : SearchMachine U)
    (hblind : BlindSearchMachine U M)
    (φ : CNF) :
    SearchFailureOnFormula U M φ := by
  intro h
  rcases h with ⟨a, hrun, _hsat⟩
  have hnone : U.searchRun M.code φ = none := hblind φ
  rw [hnone] at hrun
  cases hrun

/-- Concrete diagonal SAT self-reference for blind machines. -/
def diagonalSATSelfReference_of_blind
    (U : MachineModel)
    (M : SearchMachine U)
    (hblind : BlindSearchMachine U M) :
    DiagonalSATSelfReference U M where
  formula := trivialSATFormula
  formula_satisfiable := trivialSATFormula_satisfiable
  witness_refutes_output := by
    intro _a _hsat
    exact searchFailureOnFormula_of_blind U M hblind trivialSATFormula

/-- Restricted-class compiler: every blind machine gets a concrete diagonal
self-reference SAT miss instance. -/
def BlindDiagonalSATSelfReferenceCompiler
    (U : MachineModel) : Prop :=
  ∀ M : SearchMachine U,
    BlindSearchMachine U M -> Nonempty (DiagonalSATSelfReference U M)

/-- The blind-class compiler is constructively inhabited. -/
theorem blindDiagonalSATSelfReferenceCompiler_exists
    (U : MachineModel) :
    BlindDiagonalSATSelfReferenceCompiler U := by
  intro M hblind
  exact ⟨diagonalSATSelfReference_of_blind U M hblind⟩

/-- Consequently, every blind machine has a satisfiable SAT instance it misses.
-/
theorem blindMachine_has_missedSATInstance
    (U : MachineModel)
    (M : SearchMachine U)
    (hblind : BlindSearchMachine U M) :
    ∃ φ : CNF, SearchMachineMissesSATInstance U M φ := by
  refine ⟨trivialSATFormula, ?_⟩
  refine ⟨trivialSATFormula_satisfiable, ?_⟩
  exact searchFailureOnFormula_of_blind U M hblind trivialSATFormula

/-! ## Axiom trace -/

#print axioms trivialSATFormula_satisfiable
#print axioms searchFailureOnFormula_of_blind
#print axioms diagonalSATSelfReference_of_blind
#print axioms blindDiagonalSATSelfReferenceCompiler_exists
#print axioms blindMachine_has_missedSATInstance

end SATDepthMachine
