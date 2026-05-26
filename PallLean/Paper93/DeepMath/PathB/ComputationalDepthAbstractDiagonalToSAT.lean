import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDiagonalHierarchyBridge

/-
# Abstract diagonal theorem and the SAT transfer bridge

The previous file isolated the SAT-level hierarchy target:

  every polynomial SAT-search machine has a satisfiable CNF instance it misses.

This file splits that target into two parts:

1. a genuine diagonal theorem, which is easy and unconditional for an abstract
   enumerated Boolean machine family;
2. the hard transfer bridge, which would have to turn the abstract diagonal
   miss into a satisfiable SAT instance missed by the corresponding SAT-search
   machine.

This is the honest Williams/Gödel decomposition.  The diagonal itself is real.
The SAT transfer is the open P-vs-NP-strength step.
-/

namespace SATDepthMachine

/-! ## Abstract diagonal language -/

/-- An abstract enumerated Boolean observer family.  `run code input` is the
answer produced by observer/program `code` on encoded input `input`. -/
structure BooleanObserverFamily where
  run : Nat -> Nat -> Bool

/-- The standard diagonal language against an observer family:
on input `i`, answer the opposite of observer `i` on `i`. -/
def diagonalLanguage
    (F : BooleanObserverFamily) (i : Nat) : Bool :=
  ! F.run i i

/-- The diagonal language disagrees with observer `i` on input `i`. -/
theorem diagonalLanguage_disagrees
    (F : BooleanObserverFamily) (i : Nat) :
    diagonalLanguage F i ≠ F.run i i := by
  cases h : F.run i i <;> simp [diagonalLanguage, h]

/-- A named package for the abstract diagonal escape. -/
structure AbstractDiagonalEscape
    (F : BooleanObserverFamily) where
  inputOf : Nat -> Nat
  target : Nat -> Bool
  target_eq_diagonal :
    ∀ code : Nat, target (inputOf code) = diagonalLanguage F code
  observer_answer_eq :
    ∀ code : Nat, F.run code (inputOf code) = F.run code code

/-- The canonical abstract diagonal escape, using `code` itself as the input. -/
def canonicalAbstractDiagonalEscape
    (F : BooleanObserverFamily) : AbstractDiagonalEscape F where
  inputOf := fun code => code
  target := diagonalLanguage F
  target_eq_diagonal := by
    intro code
    rfl
  observer_answer_eq := by
    intro code
    rfl

/-- Every observer in the family misses the abstract diagonal target at its own
diagonal input. -/
theorem abstractDiagonalEscape_missed
    (F : BooleanObserverFamily)
    (E : AbstractDiagonalEscape F)
    (code : Nat) :
    E.target (E.inputOf code) ≠ F.run code (E.inputOf code) := by
  rw [E.target_eq_diagonal code, E.observer_answer_eq code]
  exact diagonalLanguage_disagrees F code

/-! ## Connecting abstract observers to SAT search machines -/

/-- A coding of SAT-search machines into an abstract Boolean observer family.

The Boolean family is the diagonal side.  The `machineOfCode` map says which
SAT-search machine the diagonal observer code represents. -/
structure SATSearchObserverCoding
    (U : MachineModel)
    (F : BooleanObserverFamily) where
  codeOfMachine : SearchMachine U -> Nat
  machineOfCode : Nat -> SearchMachine U
  roundTrip : ∀ M : SearchMachine U, machineOfCode (codeOfMachine M) = M

/-- The hard SAT transfer bridge.

For each SAT-search machine `M`, the abstract diagonal miss for its encoded
observer must be converted into a satisfiable CNF `φ_M` that `M` misses.

This is the missing Cook-Levin / Williams-style content.  It must connect the
abstract self-reference to actual SAT witness semantics without using an oracle
or assuming `DeepSATSearch`.
-/
structure AbstractDiagonalToSATTransfer
    (U : MachineModel)
    (F : BooleanObserverFamily)
    (C : SATSearchObserverCoding U F)
    (E : AbstractDiagonalEscape F) where
  formulaOfMachine : SearchMachine U -> CNF
  formula_satisfiable :
    ∀ M : SearchMachine U, Satisfiable (formulaOfMachine M)
  machine_misses :
    ∀ M : SearchMachine U,
      ¬ ∃ a : RawAssignment,
        U.searchRun M.code (formulaOfMachine M) = some a ∧
          Satisfies (formulaOfMachine M) a

/-- The SAT transfer bridge gives the constructive SAT diagonal escape. -/
theorem constructiveSATDiagonalEscape_of_abstractDiagonalTransfer
    (U : MachineModel)
    (F : BooleanObserverFamily)
    (C : SATSearchObserverCoding U F)
    (E : AbstractDiagonalEscape F)
    (T : AbstractDiagonalToSATTransfer U F C E) :
    ConstructiveSATDiagonalEscape U := by
  intro M
  exact ⟨T.formulaOfMachine M,
    ⟨T.formula_satisfiable M, T.machine_misses M⟩⟩

/-- Therefore the transfer bridge closes the deep SAT-search target. -/
theorem deepSATSearch_of_abstractDiagonalTransfer
    (U : MachineModel)
    (F : BooleanObserverFamily)
    (C : SATSearchObserverCoding U F)
    (E : AbstractDiagonalEscape F)
    (T : AbstractDiagonalToSATTransfer U F C E) :
    DeepSATSearch U :=
  deepSATSearch_of_constructiveSATDiagonalEscape U
    (constructiveSATDiagonalEscape_of_abstractDiagonalTransfer U F C E T)

/-- The abstract diagonal theorem is unconditional; the SAT transfer is the
load-bearing theorem.  This packages the honest route. -/
structure AbstractDiagonalSATRoute
    (U : MachineModel) where
  family : BooleanObserverFamily
  coding : SATSearchObserverCoding U family
  escape : AbstractDiagonalEscape family
  transfer : AbstractDiagonalToSATTransfer U family coding escape

/-- A full abstract-diagonal-to-SAT route supplies the hierarchy transport. -/
def hierarchyTransport_of_abstractDiagonalSATRoute
    (U : MachineModel)
    (R : AbstractDiagonalSATRoute U) :
    ResourceBoundedGodelHierarchyTransport U where
  escapeInstance := R.transfer.formulaOfMachine
  escape_satisfiable := R.transfer.formula_satisfiable
  escape_missed := R.transfer.machine_misses

/-- A full abstract-diagonal-to-SAT route closes deep SAT search. -/
theorem deepSATSearch_of_abstractDiagonalSATRoute
    (U : MachineModel)
    (R : AbstractDiagonalSATRoute U) :
    DeepSATSearch U :=
  deepSATSearch_of_hierarchyTransport U
    (hierarchyTransport_of_abstractDiagonalSATRoute U R)

/-
There is deliberately no converse here.  A hierarchy transport already lives at
the SAT level, while this file is about the possible proof strategy that would
produce it from an abstract diagonal language.  The intended positive theorem is
`AbstractDiagonalToSATTransfer` for a real coding of search machines and a real
Cook-Levin diagonal formula family.
-/

/-! ## Axiom trace -/

#print axioms diagonalLanguage_disagrees
#print axioms canonicalAbstractDiagonalEscape
#print axioms abstractDiagonalEscape_missed
#print axioms constructiveSATDiagonalEscape_of_abstractDiagonalTransfer
#print axioms deepSATSearch_of_abstractDiagonalTransfer
#print axioms hierarchyTransport_of_abstractDiagonalSATRoute
#print axioms deepSATSearch_of_abstractDiagonalSATRoute

end SATDepthMachine
