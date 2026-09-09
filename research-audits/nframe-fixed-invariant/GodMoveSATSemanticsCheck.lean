import PallLean.GodMoveCore

/-!
# Scope check of the legacy God-Move SAT predicate

`PaperFaithfulSeparation.ThreeCNF` records variable triples without literal
polarity.  Its `clauseSatisfied` is the positive OR of those variables, so
every formula is satisfied by the all-true assignment.  The legacy
`DecidesSAT` also has no relation connecting its accepted input to the
formula.  Consequently it is equivalent to the existence of some accepted
input at each positive length; its rejection premise is never inhabited.

This file gives that equivalence and an explicit always-accepting machine.
It does not modify production definitions or claim a SAT algorithm or a
complexity separation.  The same monotone-formula issue is already described
in `Step4Compiler` section 206; these narrow imports expose it independently
of the much larger separation wrappers.

The faithful separate target is
`PallLean.Paper93.DeepMath.PathB.SeparationTarget.SAT_not_in_P`, in
`ComputationalDepthSeparationTarget.lean`.  That target uses signed literals,
an actual formula codec, and correctness on every input word.  Changing only
the length parameter below would not supply those missing semantics.
-/

namespace GodMoveSATSemanticsCheck

open PaperFaithfulSeparation TuringMachine

/-- All legacy `ThreeCNF` formulas are monotone and hence satisfiable. -/
theorem every_legacy_ThreeCNF_satisfiable (phi : ThreeCNF) : phi.IsSatisfiable := by
  refine ⟨fun _ => true, ?_⟩
  intro c _hc
  exact Or.inl rfl

/-- A zero-size formula used to test the quantifiers in the legacy predicate. -/
def emptyLegacyFormula : ThreeCNF where
  numVars := 0
  clauses := []

@[simp] theorem emptyLegacyFormula_encodingSize : emptyLegacyFormula.encodingSize = 0 := rfl

/-- Exact meaning of the current predicate: one accepted input per positive length.
No formula-to-input encoding relation occurs in either direction. -/
theorem legacy_DecidesSAT_iff_accepts_some_input_each_length (M : DTM) :
    DecidesSAT M ↔
      ∀ (n : ℕ) (hn : 1 ≤ n), ∃ input : Fin n → Bool, accepts M n hn input := by
  constructor
  · intro hdec n hn
    exact hdec.accepts_sat emptyLegacyFormula n hn
      (by simp) (every_legacy_ThreeCNF_satisfiable emptyLegacyFormula)
  · intro haccepts
    refine ⟨?_, ?_⟩
    · intro _phi n hn _hsize _hsat
      exact haccepts n hn
    · intro phi _n _hn _hsize hnot
      exact False.elim (hnot (every_legacy_ThreeCNF_satisfiable phi))

/-- A fixed machine which enters the accepting state on its first step. -/
def alwaysAcceptMachine : DTM where
  numStates := 3
  hStates := by decide
  transition := fun _ bit => (1, bit, true)
  timeBound := 1
  hTimeBound := by decide

theorem alwaysAcceptMachine_accepts (n : ℕ) (hn : 1 ≤ n) (input : Fin n → Bool) :
    accepts alwaysAcceptMachine n hn input := by
  refine ⟨1, ?_, ?_⟩
  · simpa [timeSteps, alwaysAcceptMachine] using hn
  · rfl

/-- The current SAT-named predicate is inhabited by this trivial machine. -/
theorem alwaysAcceptMachine_legacy_DecidesSAT : DecidesSAT alwaysAcceptMachine := by
  apply (legacy_DecidesSAT_iff_accepts_some_input_each_length alwaysAcceptMachine).mpr
  intro n hn
  exact ⟨fun _ => false, alwaysAcceptMachine_accepts n hn _⟩

/-- This witness also lies inside the legacy bounded-machine regime. -/
theorem legacy_bounded_decider_exists :
    ∃ M : DTM, M.timeBound ≤ 4 ∧ M.numStates = 3 ∧ DecidesSAT M := by
  exact ⟨alwaysAcceptMachine, by decide, rfl, alwaysAcceptMachine_legacy_DecidesSAT⟩

end GodMoveSATSemanticsCheck

#print axioms GodMoveSATSemanticsCheck.every_legacy_ThreeCNF_satisfiable
#print axioms GodMoveSATSemanticsCheck.legacy_DecidesSAT_iff_accepts_some_input_each_length
#print axioms GodMoveSATSemanticsCheck.alwaysAcceptMachine_accepts
#print axioms GodMoveSATSemanticsCheck.alwaysAcceptMachine_legacy_DecidesSAT
#print axioms GodMoveSATSemanticsCheck.legacy_bounded_decider_exists
