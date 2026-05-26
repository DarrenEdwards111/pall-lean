import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDiagonalSATSelfReference

/-
# Self-reference compiler equivalence

`ComputationalDepthDiagonalSATSelfReference.lean` isolated the fixed-point
object that would close the route:

  `DiagonalSATSelfReferenceCompiler U`.

This file proves the guard/equivalence theorem around that object.  A compiler
of those self-referential SAT instances is not a smaller technical lemma; it is
exactly the deep SAT-search lower bound.

It also proves the per-machine obstruction: if a candidate machine is actually
correct for SAT search, then no satisfiable self-referential formula defeating
that machine can exist.  This is the consistency check on the fixed-point
proposal.
-/

namespace SATDepthMachine

/-! ## Per-machine guards -/

/-- A correct SAT-search machine cannot have a satisfiable diagonal
self-reference defeating it. -/
theorem no_diagonalSATSelfReference_of_searchCorrect
    (U : MachineModel)
    (M : SearchMachine U)
    (hM : SearchCorrect U M) :
    ¬ Nonempty (DiagonalSATSelfReference U M) := by
  intro hD
  rcases hD with ⟨D⟩
  have hfail : SearchFailureOnFormula U M D.formula :=
    searchFailureOnFormula_of_diagonalSATSelfReference U M D
  exact hfail (hM D.formula D.formula_satisfiable)

/-- A self-reference compiler proves that every candidate SAT-search machine is
incorrect. -/
theorem not_searchCorrect_of_selfReferenceCompiler
    (U : MachineModel)
    (K : DiagonalSATSelfReferenceCompiler U)
    (M : SearchMachine U) :
    ¬ SearchCorrect U M := by
  intro hM
  exact no_diagonalSATSelfReference_of_searchCorrect U M hM
    ⟨K.compile M⟩

/-- A missed SAT instance can be viewed as a diagonal SAT self-reference:
because the machine already globally fails on the formula, any satisfying
witness certifies that failure. -/
def diagonalSATSelfReference_of_missedInstance
    (U : MachineModel)
    (M : SearchMachine U)
    (φ : CNF)
    (hmiss : SearchMachineMissesSATInstance U M φ) :
    DiagonalSATSelfReference U M where
  formula := φ
  formula_satisfiable := hmiss.1
  witness_refutes_output := by
    intro _a _ha
    exact hmiss.2

/-! ## Compiler equivalences -/

/-- A constructive SAT diagonal escape noncomputably packages into a
self-reference compiler.  The noncomputability is only choice over the missed
formula supplied by the escape theorem; the mathematical load is the escape. -/
noncomputable def selfReferenceCompiler_of_constructiveSATDiagonalEscape
    (U : MachineModel)
    (hdiag : ConstructiveSATDiagonalEscape U) :
    DiagonalSATSelfReferenceCompiler U where
  compile := by
    intro M
    let φ := Classical.choose (hdiag M)
    have hmiss : SearchMachineMissesSATInstance U M φ :=
      Classical.choose_spec (hdiag M)
    exact diagonalSATSelfReference_of_missedInstance U M φ hmiss

/-- The self-reference compiler is exactly the constructive SAT diagonal escape.
-/
theorem selfReferenceCompiler_iff_constructiveSATDiagonalEscape
    (U : MachineModel) :
    Nonempty (DiagonalSATSelfReferenceCompiler U) ↔
      ConstructiveSATDiagonalEscape U := by
  constructor
  · intro hK
    rcases hK with ⟨K⟩
    exact constructiveSATDiagonalEscape_of_selfReferenceCompiler U K
  · intro hdiag
    exact ⟨selfReferenceCompiler_of_constructiveSATDiagonalEscape U hdiag⟩

/-- The self-reference compiler is exactly deep SAT search. -/
theorem selfReferenceCompiler_iff_deepSATSearch
    (U : MachineModel) :
    Nonempty (DiagonalSATSelfReferenceCompiler U) ↔ DeepSATSearch U := by
  constructor
  · intro hK
    rcases hK with ⟨K⟩
    exact deepSATSearch_of_selfReferenceCompiler U K
  · intro hdeep
    exact (selfReferenceCompiler_iff_constructiveSATDiagonalEscape U).mpr
      ((constructiveSATDiagonalEscape_iff_deepSATSearch U).mpr hdeep)

/-- With prefix-unit decision-to-search accounting, the self-reference compiler
is exactly the no-polynomial-SAT-decider target. -/
theorem selfReferenceCompiler_iff_no_decider
    {U : MachineModel}
    (C : PrefixUnitMachineCompiler U) :
    Nonempty (DiagonalSATSelfReferenceCompiler U) ↔ ¬ SATDecisionInP U := by
  constructor
  · intro hK
    rcases hK with ⟨K⟩
    exact no_decider_of_selfReferenceCompiler C K
  · intro hnodec
    have hdeep : DeepSATSearch U :=
      (deepSATSearch_iff_no_decider_with_prefixUnitCompiler C).mpr hnodec
    exact (selfReferenceCompiler_iff_deepSATSearch U).mpr hdeep

/-! ## Equivalent pointwise failure form -/

/-- If one can prove every search machine is not correct, then each machine has
a missed satisfiable instance. -/
theorem constructiveSATDiagonalEscape_of_forall_not_searchCorrect
    (U : MachineModel)
    (hfail : ∀ M : SearchMachine U, ¬ SearchCorrect U M) :
    ConstructiveSATDiagonalEscape U := by
  intro M
  by_contra hnoMiss
  apply hfail M
  intro φ hsat
  by_contra hnoWitness
  exact hnoMiss ⟨φ, hsat, hnoWitness⟩

/-- A self-reference compiler is also exactly the pointwise statement that every
polynomial SAT-search machine is incorrect. -/
theorem selfReferenceCompiler_iff_forall_not_searchCorrect
    (U : MachineModel) :
    Nonempty (DiagonalSATSelfReferenceCompiler U) ↔
      ∀ M : SearchMachine U, ¬ SearchCorrect U M := by
  constructor
  · intro hK
    rcases hK with ⟨K⟩
    exact not_searchCorrect_of_selfReferenceCompiler U K
  · intro hfail
    exact (selfReferenceCompiler_iff_constructiveSATDiagonalEscape U).mpr
      (constructiveSATDiagonalEscape_of_forall_not_searchCorrect U hfail)

/-! ## Axiom trace -/

#print axioms no_diagonalSATSelfReference_of_searchCorrect
#print axioms not_searchCorrect_of_selfReferenceCompiler
#print axioms diagonalSATSelfReference_of_missedInstance
#print axioms selfReferenceCompiler_of_constructiveSATDiagonalEscape
#print axioms selfReferenceCompiler_iff_constructiveSATDiagonalEscape
#print axioms selfReferenceCompiler_iff_deepSATSearch
#print axioms selfReferenceCompiler_iff_no_decider
#print axioms constructiveSATDiagonalEscape_of_forall_not_searchCorrect
#print axioms selfReferenceCompiler_iff_forall_not_searchCorrect

end SATDepthMachine
