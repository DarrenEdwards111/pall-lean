import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHyperBoundaryClassicalBridge
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthStandardTuringBoundaryTerm

/-
# Diagonal / hierarchy bridge

This file formalizes the Williams/Gödel-style target that would have to replace
rank, area, gravity, or hyper-boundary bookkeeping.

The required theorem is not "SAT has high SPDP rank"; it is a resource-bounded
diagonal escape:

  for every ordinary polynomial search machine `M`, construct a satisfiable CNF
  formula `φ_M` on which `M` fails to output a satisfying witness.

That is the machine-level form of the book's Gödel hierarchy intuition applied
to SAT search: every bounded observer has an escape instance.

The file proves the exact accounting facts:

* such a diagonal escape implies `DeepSATSearch`;
* conversely, `DeepSATSearch` is equivalent to the existence of such escapes;
* packaged as a named hierarchy transport, the target is also equivalent to
  ruling out classical simulation of the hyper-boundary term and to ruling out
  any SPDP-proved standard Turing SAT term.

No P-vs-NP lower bound is asserted.  The missing mathematical breakthrough is
the construction of the escape formula `φ_M` by a genuine non-natural,
non-local hierarchy argument.
-/

namespace SATDepthMachine

/-! ## Concrete diagonal miss predicate -/

/-- `M` misses `φ` as a SAT-search instance: `φ` is satisfiable, but `M` does
not output any satisfying assignment for it. -/
def SearchMachineMissesSATInstance
    (U : MachineModel)
    (M : SearchMachine U)
    (φ : CNF) : Prop :=
  Satisfiable φ ∧
    ¬ ∃ a : RawAssignment,
      U.searchRun M.code φ = some a ∧ Satisfies φ a

/-- Resource-bounded SAT diagonal escape: every polynomial search machine has
a satisfiable CNF instance it misses. -/
def ConstructiveSATDiagonalEscape
    (U : MachineModel) : Prop :=
  ∀ M : SearchMachine U,
    ∃ φ : CNF, SearchMachineMissesSATInstance U M φ

/-- A constructive SAT diagonal escape immediately rules out shallow SAT
search. -/
theorem deepSATSearch_of_constructiveSATDiagonalEscape
    (U : MachineModel)
    (hdiag : ConstructiveSATDiagonalEscape U) :
    DeepSATSearch U := by
  intro hshallow
  rcases hshallow with ⟨M, hM⟩
  rcases hdiag M with ⟨φ, hmiss⟩
  exact hmiss.2 (hM φ hmiss.1)

/-- Deep SAT search gives the same diagonal-escape formulation: every candidate
search machine has some satisfiable instance on which it fails. -/
theorem constructiveSATDiagonalEscape_of_deepSATSearch
    (U : MachineModel)
    (hdeep : DeepSATSearch U) :
    ConstructiveSATDiagonalEscape U := by
  intro M
  by_contra hnofail
  apply hdeep
  refine ⟨M, ?_⟩
  intro φ hsat
  by_contra hnowitness
  exact hnofail ⟨φ, hsat, hnowitness⟩

/-- The diagonal-escape target is exactly deep SAT search. -/
theorem constructiveSATDiagonalEscape_iff_deepSATSearch
    (U : MachineModel) :
    ConstructiveSATDiagonalEscape U ↔ DeepSATSearch U :=
  ⟨deepSATSearch_of_constructiveSATDiagonalEscape U,
    constructiveSATDiagonalEscape_of_deepSATSearch U⟩

/-! ## Named Gödel/Williams hierarchy transport -/

/-- A packaged non-natural hierarchy transport.

The data are intentionally stronger than an abstract negation: it supplies an
actual escape formula for each bounded search machine.  This is where a real
Williams/Gödel argument would have to live.
-/
structure ResourceBoundedGodelHierarchyTransport
    (U : MachineModel) where
  escapeInstance : SearchMachine U -> CNF
  escape_satisfiable :
    ∀ M : SearchMachine U, Satisfiable (escapeInstance M)
  escape_missed :
    ∀ M : SearchMachine U,
      ¬ ∃ a : RawAssignment,
        U.searchRun M.code (escapeInstance M) = some a ∧
          Satisfies (escapeInstance M) a

/-- A hierarchy transport gives the constructive diagonal escape. -/
theorem constructiveSATDiagonalEscape_of_hierarchyTransport
    (U : MachineModel)
    (T : ResourceBoundedGodelHierarchyTransport U) :
    ConstructiveSATDiagonalEscape U := by
  intro M
  exact ⟨T.escapeInstance M,
    ⟨T.escape_satisfiable M, T.escape_missed M⟩⟩

/-- A hierarchy transport closes the deep-search lower-bound target. -/
theorem deepSATSearch_of_hierarchyTransport
    (U : MachineModel)
    (T : ResourceBoundedGodelHierarchyTransport U) :
    DeepSATSearch U :=
  deepSATSearch_of_constructiveSATDiagonalEscape U
    (constructiveSATDiagonalEscape_of_hierarchyTransport U T)

/-- Conversely, deep search noncomputably packages into a hierarchy transport.
This theorem is not a construction method; it records that the hierarchy
transport is exactly the same target, not a weaker lemma. -/
noncomputable def hierarchyTransport_of_deepSATSearch
    (U : MachineModel)
    (hdeep : DeepSATSearch U) :
    ResourceBoundedGodelHierarchyTransport U where
  escapeInstance := fun M =>
    Classical.choose
      (constructiveSATDiagonalEscape_of_deepSATSearch U hdeep M)
  escape_satisfiable := by
    intro M
    exact
      (Classical.choose_spec
        (constructiveSATDiagonalEscape_of_deepSATSearch U hdeep M)).1
  escape_missed := by
    intro M
    exact
      (Classical.choose_spec
        (constructiveSATDiagonalEscape_of_deepSATSearch U hdeep M)).2

/-- Existence of the packaged hierarchy transport is exactly deep SAT search. -/
theorem hierarchyTransport_iff_deepSATSearch
    (U : MachineModel) :
    Nonempty (ResourceBoundedGodelHierarchyTransport U) ↔
      DeepSATSearch U := by
  constructor
  · intro hT
    rcases hT with ⟨T⟩
    exact deepSATSearch_of_hierarchyTransport U T
  · intro hdeep
    exact ⟨hierarchyTransport_of_deepSATSearch U hdeep⟩

/-! ## Closure against the previous observer routes -/

/-- With the prefix-unit compiler/accounting layer, a hierarchy transport rules
out ordinary polynomial SAT decision. -/
theorem no_decider_of_hierarchyTransport
    {U : MachineModel}
    (C : PrefixUnitMachineCompiler U)
    (T : ResourceBoundedGodelHierarchyTransport U) :
    ¬ SATDecisionInP U :=
  (deepSATSearch_iff_no_decider_with_prefixUnitCompiler C).mp
    (deepSATSearch_of_hierarchyTransport U T)

/-- A hierarchy transport rules out classical simulation of any
hypercomputational SAT boundary term. -/
theorem no_hyperBoundaryClassicalSimulation_of_hierarchyTransport
    (H : HypercomputationalSATBoundaryTerm)
    (U : MachineModel)
    (T : ResourceBoundedGodelHierarchyTransport U) :
    ¬ HyperBoundaryClassicallySimulable H U :=
  (deepSATSearch_iff_no_hyperBoundaryClassicalSimulation H U).mp
    (deepSATSearch_of_hierarchyTransport U T)

/-- A hierarchy transport rules out SPDP-proved standard Turing SAT terms. -/
theorem no_spdpProvedStandardTuringBoundaryTerm_of_hierarchyTransport
    (U : MachineModel)
    (T : ResourceBoundedGodelHierarchyTransport U) :
    ¬ Nonempty (SPDPProvedStandardTuringBoundaryTerm U) :=
  no_spdpProvedStandardTuringBoundaryTerm_of_deepSATSearch U
    (deepSATSearch_of_hierarchyTransport U T)

/-- Final packaged bridge: this is the exact theorem a positive
Williams/Gödel route must supply. -/
theorem hierarchyTransport_closes_observer_routes
    (H : HypercomputationalSATBoundaryTerm)
    {U : MachineModel}
    (C : PrefixUnitMachineCompiler U)
    (T : ResourceBoundedGodelHierarchyTransport U) :
    (¬ SATDecisionInP U) ∧
      (¬ HyperBoundaryClassicallySimulable H U) ∧
        (¬ Nonempty (SPDPProvedStandardTuringBoundaryTerm U)) :=
  ⟨no_decider_of_hierarchyTransport C T,
    no_hyperBoundaryClassicalSimulation_of_hierarchyTransport H U T,
    no_spdpProvedStandardTuringBoundaryTerm_of_hierarchyTransport U T⟩

/-! ## Axiom trace -/

#print axioms deepSATSearch_of_constructiveSATDiagonalEscape
#print axioms constructiveSATDiagonalEscape_of_deepSATSearch
#print axioms constructiveSATDiagonalEscape_iff_deepSATSearch
#print axioms constructiveSATDiagonalEscape_of_hierarchyTransport
#print axioms deepSATSearch_of_hierarchyTransport
#print axioms hierarchyTransport_of_deepSATSearch
#print axioms hierarchyTransport_iff_deepSATSearch
#print axioms no_decider_of_hierarchyTransport
#print axioms no_hyperBoundaryClassicalSimulation_of_hierarchyTransport
#print axioms no_spdpProvedStandardTuringBoundaryTerm_of_hierarchyTransport
#print axioms hierarchyTransport_closes_observer_routes

end SATDepthMachine
