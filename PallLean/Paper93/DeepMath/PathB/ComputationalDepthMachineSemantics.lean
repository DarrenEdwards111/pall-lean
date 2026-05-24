/-
# Machine-level computational-depth semantics for SAT search

This file tightens `ComputationalDepthFraming.lean`.

The earlier file intentionally used a small abstract skeleton.  This one fixes
the two main weaknesses:

* the input object is now the full SAT language, represented by concrete CNF
  formulas, not a single length-indexed instance `F n`;
* a shallow observer is represented by a numeric code in an abstract machine
  model, with a certified polynomial step budget, not an arbitrary
  length-indexed function.

This is still not a proof of P vs NP.  The machine semantics are abstract
certificate semantics: a machine model interprets numeric codes as search and
decision behavior.  The file does not construct a concrete universal Turing
interpreter.  The load-bearing lower bound remains `DeepSATSearch`.

What is proved:

* bounded SAT search implies bounded SAT decision;
* if no bounded SAT decider exists, then SAT search is deep;
* with a SAT decision-to-search self-reduction theorem, SAT search depth is
  equivalent to the no-bounded-decider statement.

The self-reduction is isolated as a separate structure instead of smuggled in as
an axiom or `sorry`.
-/

namespace SATDepthMachine

/-! ## CNF SAT semantics -/

/-- A raw assignment is a bitstring.  The verifier checks the required length. -/
abbrev RawAssignment := List Bool

/-- Version-stable list lookup for raw assignments. -/
def RawAssignment.lookup : RawAssignment -> Nat -> Option Bool
  | [], _ => none
  | b :: _, 0 => some b
  | _ :: rest, n + 1 => RawAssignment.lookup rest n

/-- Literal polarity. -/
inductive Polarity where
  | pos
  | neg
deriving DecidableEq, Repr

/-- A literal is a variable index together with a polarity. -/
structure Lit where
  var : Nat
  pol : Polarity
deriving DecidableEq, Repr

/-- A clause is a disjunction of literals. -/
abbrev Clause := List Lit

/-- A CNF formula over `vars` variables. -/
structure CNF where
  vars : Nat
  clauses : List Clause
deriving Repr

/-- A simple syntactic size measure used for machine budgets. -/
def CNF.size (φ : CNF) : Nat :=
  φ.vars + φ.clauses.length + φ.clauses.foldl (fun acc c => acc + c.length) 0

/-- Evaluate a literal under a raw assignment.  Out-of-range variables evaluate
to false, so malformed literals cannot create fake satisfying assignments. -/
def Lit.eval (a : RawAssignment) (l : Lit) : Bool :=
  match RawAssignment.lookup a l.var with
  | none => false
  | some b =>
      match l.pol with
      | Polarity.pos => b
      | Polarity.neg => !b

/-- Evaluate one clause. -/
def Clause.eval (a : RawAssignment) (c : Clause) : Bool :=
  c.any (fun l => l.eval a)

/-- Evaluate a CNF formula. -/
def CNF.eval (φ : CNF) (a : RawAssignment) : Bool :=
  φ.clauses.all (fun c => c.eval a)

/-- A raw assignment satisfies a formula exactly when it has the right length
and makes every clause true. -/
def Satisfies (φ : CNF) (a : RawAssignment) : Prop :=
  a.length = φ.vars ∧ φ.eval a = true

/-- SAT semantics over all formulas. -/
def Satisfiable (φ : CNF) : Prop :=
  ∃ a : RawAssignment, Satisfies φ a

instance (φ : CNF) (a : RawAssignment) : Decidable (Satisfies φ a) := by
  unfold Satisfies
  infer_instance

/-! ## Time-bounded machine surfaces -/

/-- Concrete polynomial-budget predicate. -/
def IsPolynomialBudget (t : Nat -> Nat) : Prop :=
  ∃ k c : Nat, ∀ n : Nat, t n ≤ c * (n + 1) ^ k

/-- Verify a candidate output from a search machine. -/
def checkSearchOutput (φ : CNF) : Option RawAssignment -> Bool
  | none => false
  | some a => decide (Satisfies φ a)

theorem checkSearchOutput_true_iff
    (φ : CNF) (out : Option RawAssignment) :
    checkSearchOutput φ out = true ↔
      ∃ a : RawAssignment, out = some a ∧ Satisfies φ a := by
  cases out with
  | none =>
      constructor
      · intro h
        cases h
      · intro h
        rcases h with ⟨a, hout, _hsat⟩
        cases hout
  | some a =>
      constructor
      · intro h
        by_cases hsat : Satisfies φ a
        · exact ⟨a, rfl, hsat⟩
        · have hfalse : decide (Satisfies φ a) = false :=
            decide_eq_false hsat
          rw [checkSearchOutput, hfalse] at h
          cases h
      · intro h
        rcases h with ⟨b, hb, hsat⟩
        cases hb
        exact decide_eq_true hsat

/-- Abstract machine model for coded SAT search and decision programs.

`verifierCode` is the standard compiler turning a search program into a
decision program that runs the searcher and verifies the candidate witness. -/
structure MachineModel where
  searchRun : Nat -> CNF -> Option RawAssignment
  searchSteps : Nat -> CNF -> Nat
  decisionRun : Nat -> CNF -> Bool
  decisionSteps : Nat -> CNF -> Nat
  verifierCode : Nat -> Nat
  verifier_run :
    ∀ (code : Nat) (φ : CNF),
      decisionRun (verifierCode code) φ =
        checkSearchOutput φ (searchRun code φ)
  verifier_steps :
    ∀ (code : Nat) (φ : CNF),
      decisionSteps (verifierCode code) φ = searchSteps code φ

/-- A coded producer machine for SAT search in a fixed machine model. -/
structure SearchMachine (U : MachineModel) where
  code : Nat
  budget : Nat -> Nat
  polyBudget : IsPolynomialBudget budget
  steps_le_budget : ∀ φ : CNF, U.searchSteps code φ ≤ budget φ.size

/-- A coded decision machine for SAT in a fixed machine model. -/
structure DecisionMachine (U : MachineModel) where
  code : Nat
  budget : Nat -> Nat
  polyBudget : IsPolynomialBudget budget
  steps_le_budget : ∀ φ : CNF, U.decisionSteps code φ ≤ budget φ.size

/-- Search correctness over every satisfiable formula. -/
def SearchCorrect (U : MachineModel) (M : SearchMachine U) : Prop :=
  ∀ φ : CNF, Satisfiable φ ->
    ∃ a : RawAssignment, U.searchRun M.code φ = some a ∧ Satisfies φ a

/-- Decision correctness over every formula. -/
def DecidesSAT (U : MachineModel) (M : DecisionMachine U) : Prop :=
  ∀ φ : CNF, U.decisionRun M.code φ = true ↔ Satisfiable φ

/-- Shallow SAT search: one polynomial-budget coded producer works uniformly on
all satisfiable formulas.  This is the metacomplexity/K^t version of the
observer being able to decompress witnesses under the polynomial constraint. -/
def ShallowSATSearch (U : MachineModel) : Prop :=
  ∃ M : SearchMachine U, SearchCorrect U M

/-- Deep SAT search: no such uniform polynomial-budget producer exists. -/
def DeepSATSearch (U : MachineModel) : Prop :=
  ¬ ShallowSATSearch U

/-- Polynomial-time SAT decision in this abstract machine surface. -/
def SATDecisionInP (U : MachineModel) : Prop :=
  ∃ M : DecisionMachine U, DecidesSAT U M

/-! ## Search-to-decision, fully over formulas -/

/-- Easy direction: a bounded search producer gives a bounded decider by running
the producer and checking the returned witness. -/
theorem decider_of_shallowSATSearch
    (U : MachineModel)
    (h : ShallowSATSearch U) : SATDecisionInP U := by
  rcases h with ⟨M, hM⟩
  let D : DecisionMachine U := {
    code := U.verifierCode M.code
    budget := M.budget
    polyBudget := M.polyBudget
    steps_le_budget := by
      intro φ
      rw [U.verifier_steps]
      exact M.steps_le_budget φ
  }
  refine ⟨D, ?_⟩
  intro φ
  change U.decisionRun (U.verifierCode M.code) φ = true ↔ Satisfiable φ
  rw [U.verifier_run]
  rw [checkSearchOutput_true_iff]
  constructor
  · intro hgood
    rcases hgood with ⟨a, _hrun, hsat⟩
    exact ⟨a, hsat⟩
  · intro hsat
    exact hM φ hsat

/-- Contrapositive of the easy direction.  If no polynomial-budget SAT decider
exists, then search is deep. -/
theorem deepSATSearch_of_no_decider
    (U : MachineModel)
    (h : ¬ SATDecisionInP U) : DeepSATSearch U := by
  intro hshallow
  exact h (decider_of_shallowSATSearch U hshallow)

/-! ## The missing converse as an explicit self-reduction socket -/

/-- A polynomial-budget Cook self-reduction from SAT decision to SAT search.

This is the honest missing formal ingredient for the converse.  For SAT it is
standard mathematics, but this repository has not built the full reduction over
these concrete CNF formulas yet. -/
structure DecisionToSearchSelfReduction (U : MachineModel) where
  fromDecider : (D : DecisionMachine U) -> DecidesSAT U D -> SearchMachine U
  correct : ∀ (D : DecisionMachine U) (hD : DecidesSAT U D),
    SearchCorrect U (fromDecider D hD)

/-- With a decision-to-search self-reduction, any bounded decider yields shallow
search. -/
theorem shallowSATSearch_of_decider_with_selfReduction
    {U : MachineModel}
    (R : DecisionToSearchSelfReduction U)
    (h : SATDecisionInP U) : ShallowSATSearch U := by
  rcases h with ⟨D, hD⟩
  exact ⟨R.fromDecider D hD, R.correct D hD⟩

/-- With the self-reduction socket discharged, deep search rules out bounded
SAT decision. -/
theorem no_decider_of_deepSATSearch_with_selfReduction
    {U : MachineModel}
    (R : DecisionToSearchSelfReduction U)
    (hdeep : DeepSATSearch U) : ¬ SATDecisionInP U := by
  intro hdec
  exact hdeep (shallowSATSearch_of_decider_with_selfReduction R hdec)

/-- Once the SAT decision-to-search self-reduction is formalized, computational
depth of SAT search is exactly the no-bounded-decider statement. -/
theorem deepSATSearch_iff_no_decider_with_selfReduction
    {U : MachineModel}
    (R : DecisionToSearchSelfReduction U) :
    DeepSATSearch U ↔ ¬ SATDecisionInP U := by
  constructor
  · exact no_decider_of_deepSATSearch_with_selfReduction R
  · exact deepSATSearch_of_no_decider U

/-! ## Kernel-only axiom trace -/

#print axioms checkSearchOutput_true_iff
#print axioms decider_of_shallowSATSearch
#print axioms deepSATSearch_of_no_decider
#print axioms shallowSATSearch_of_decider_with_selfReduction
#print axioms no_decider_of_deepSATSearch_with_selfReduction
#print axioms deepSATSearch_iff_no_decider_with_selfReduction

end SATDepthMachine
