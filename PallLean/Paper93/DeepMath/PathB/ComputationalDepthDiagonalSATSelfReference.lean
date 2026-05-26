import PallLean.Paper93.DeepMath.PathB.ComputationalDepthAbstractDiagonalToSAT

/-
# Diagonal SAT self-reference compiler

`ComputationalDepthAbstractDiagonalToSAT.lean` split the positive route into:

* an unconditional abstract diagonal theorem;
* a hard transfer from that diagonal miss to actual SAT witness semantics.

This file lowers the transfer to the exact self-referential SAT object needed.
For each polynomial SAT-search machine `M`, build a satisfiable CNF `φ_M` whose
satisfying witnesses certify that `M` does not output a satisfying witness for
that very same `φ_M`.

That is the Cook-Levin/Gödel fixed-point shape the route needs.  The file proves
that such a compiler would discharge `AbstractDiagonalToSATTransfer`,
`ResourceBoundedGodelHierarchyTransport`, and `DeepSATSearch`.

No such compiler is constructed here.  The point is to isolate the exact
non-circular object the proof would need.
-/

namespace SATDepthMachine

/-! ## Self-referential SAT miss predicate -/

/-- The ordinary SAT-search miss predicate for one machine/formula pair. -/
def SearchFailureOnFormula
    (U : MachineModel)
    (M : SearchMachine U)
    (φ : CNF) : Prop :=
  ¬ ∃ a : RawAssignment,
    U.searchRun M.code φ = some a ∧ Satisfies φ a

/-- A diagonal SAT self-reference for `M`.

The formula is satisfiable, but every satisfying witness proves the global fact
that `M` has no satisfying output for this same formula.  This is the exact
fixed-point/Cook-Levin object needed to turn abstract diagonalization into a
SAT-search lower bound. -/
structure DiagonalSATSelfReference
    (U : MachineModel)
    (M : SearchMachine U) where
  formula : CNF
  formula_satisfiable : Satisfiable formula
  witness_refutes_output :
    ∀ a : RawAssignment,
      Satisfies formula a -> SearchFailureOnFormula U M formula

/-- A diagonal self-reference forces the machine to miss its formula. -/
theorem searchFailureOnFormula_of_diagonalSATSelfReference
    (U : MachineModel)
    (M : SearchMachine U)
    (D : DiagonalSATSelfReference U M) :
    SearchFailureOnFormula U M D.formula := by
  rcases D.formula_satisfiable with ⟨a, ha⟩
  exact D.witness_refutes_output a ha

/-- A diagonal self-reference is exactly a SAT miss instance in the previous
file's sense. -/
theorem searchMachineMisses_of_diagonalSATSelfReference
    (U : MachineModel)
    (M : SearchMachine U)
    (D : DiagonalSATSelfReference U M) :
    SearchMachineMissesSATInstance U M D.formula :=
  ⟨D.formula_satisfiable,
    searchFailureOnFormula_of_diagonalSATSelfReference U M D⟩

/-! ## Compiler from machines to self-referential SAT formulas -/

/-- The load-bearing compiler the positive route needs.

For every ordinary polynomial SAT-search machine, produce a diagonal
self-referential satisfiable CNF that the machine misses. -/
structure DiagonalSATSelfReferenceCompiler
    (U : MachineModel) where
  compile :
    ∀ M : SearchMachine U, DiagonalSATSelfReference U M

/-- The self-reference compiler gives the constructive SAT diagonal escape. -/
theorem constructiveSATDiagonalEscape_of_selfReferenceCompiler
    (U : MachineModel)
    (K : DiagonalSATSelfReferenceCompiler U) :
    ConstructiveSATDiagonalEscape U := by
  intro M
  let D := K.compile M
  exact ⟨D.formula, searchMachineMisses_of_diagonalSATSelfReference U M D⟩

/-- The self-reference compiler gives the hierarchy transport. -/
def hierarchyTransport_of_selfReferenceCompiler
    (U : MachineModel)
    (K : DiagonalSATSelfReferenceCompiler U) :
    ResourceBoundedGodelHierarchyTransport U where
  escapeInstance := fun M => (K.compile M).formula
  escape_satisfiable := fun M => (K.compile M).formula_satisfiable
  escape_missed := fun M =>
    searchFailureOnFormula_of_diagonalSATSelfReference U M (K.compile M)

/-- The self-reference compiler closes deep SAT search. -/
theorem deepSATSearch_of_selfReferenceCompiler
    (U : MachineModel)
    (K : DiagonalSATSelfReferenceCompiler U) :
    DeepSATSearch U :=
  deepSATSearch_of_hierarchyTransport U
    (hierarchyTransport_of_selfReferenceCompiler U K)

/-! ## Filling the previous abstract transfer socket -/

/-- A self-reference compiler discharges `AbstractDiagonalToSATTransfer` for
any abstract diagonal observer coding.  Notice that the proof does not depend on
the abstract family once the SAT self-reference exists; this shows the real load
is the SAT fixed point itself. -/
def abstractDiagonalToSATTransfer_of_selfReferenceCompiler
    (U : MachineModel)
    (F : BooleanObserverFamily)
    (C : SATSearchObserverCoding U F)
    (E : AbstractDiagonalEscape F)
    (K : DiagonalSATSelfReferenceCompiler U) :
    AbstractDiagonalToSATTransfer U F C E where
  formulaOfMachine := fun M => (K.compile M).formula
  formula_satisfiable := fun M => (K.compile M).formula_satisfiable
  machine_misses := fun M =>
    searchFailureOnFormula_of_diagonalSATSelfReference U M (K.compile M)

/-- A self-reference compiler produces a full abstract-diagonal-to-SAT route
once an observer coding is supplied. -/
def abstractDiagonalSATRoute_of_selfReferenceCompiler
    (U : MachineModel)
    (F : BooleanObserverFamily)
    (C : SATSearchObserverCoding U F)
    (E : AbstractDiagonalEscape F)
    (K : DiagonalSATSelfReferenceCompiler U) :
    AbstractDiagonalSATRoute U where
  family := F
  coding := C
  escape := E
  transfer :=
    abstractDiagonalToSATTransfer_of_selfReferenceCompiler U F C E K

/-! ## Guard: this compiler is P-vs-NP strength -/

/-- If shallow SAT search exists, no diagonal SAT self-reference compiler can
exist. -/
theorem no_selfReferenceCompiler_of_shallowSATSearch
    (U : MachineModel)
    (hshallow : ShallowSATSearch U) :
    ¬ Nonempty (DiagonalSATSelfReferenceCompiler U) := by
  intro hK
  rcases hK with ⟨K⟩
  exact (deepSATSearch_of_selfReferenceCompiler U K) hshallow

/-- Conversely, a self-reference compiler rules out every ordinary shallow SAT
searcher. -/
theorem no_shallowSATSearch_of_selfReferenceCompiler
    (U : MachineModel)
    (K : DiagonalSATSelfReferenceCompiler U) :
    ¬ ShallowSATSearch U :=
  deepSATSearch_of_selfReferenceCompiler U K

/-- With prefix-unit decision-to-search accounting, a self-reference compiler
rules out polynomial-time SAT decision. -/
theorem no_decider_of_selfReferenceCompiler
    {U : MachineModel}
    (C : PrefixUnitMachineCompiler U)
    (K : DiagonalSATSelfReferenceCompiler U) :
    ¬ SATDecisionInP U :=
  no_decider_of_hierarchyTransport C
    (hierarchyTransport_of_selfReferenceCompiler U K)

/-! ## Axiom trace -/

#print axioms searchFailureOnFormula_of_diagonalSATSelfReference
#print axioms searchMachineMisses_of_diagonalSATSelfReference
#print axioms constructiveSATDiagonalEscape_of_selfReferenceCompiler
#print axioms hierarchyTransport_of_selfReferenceCompiler
#print axioms deepSATSearch_of_selfReferenceCompiler
#print axioms abstractDiagonalToSATTransfer_of_selfReferenceCompiler
#print axioms abstractDiagonalSATRoute_of_selfReferenceCompiler
#print axioms no_selfReferenceCompiler_of_shallowSATSearch
#print axioms no_shallowSATSearch_of_selfReferenceCompiler
#print axioms no_decider_of_selfReferenceCompiler

end SATDepthMachine
