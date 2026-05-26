import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMachineCompiler

/-
# Standard Turing boundary term

This file tests the non-hypercomputational alternative to the boundary term.

In the book language:

* `L_eff` is the ordinary Turing-computable observer-boundary dynamics;
* SPDP/log-det certificates may be used as proof metadata for such a term;
* `L_H(H(φ_obs))` is the separate hypercomputational channel, handled in
  `ComputationalDepthHypercomputationalBoundaryTerm.lean`.

The key accounting fact is simple but important: if the boundary term is
standard Turing-computable, then a correct SAT-witness term is exactly an
ordinary polynomial SAT search machine.  Therefore an SPDP proof attached to
such a standard term can only close the route if it proves ordinary
`ShallowSATSearch`.  Under the prefix-unit compiler, this is exactly
`SATDecisionInP`.

So SPDP can be proof metadata for a standard term, but it is not a separate
way around the classical lower-bound target.
-/

namespace SATDepthMachine

/-! ## Standard Turing boundary terms -/

/-- A non-hypercomputational observer-boundary term.

This is just an ordinary coded polynomial-budget search machine in the chosen
machine surface `U`.  It represents the `L_eff` / standard Turing part of the
N-Frame boundary dynamics. -/
structure StandardTuringBoundaryTerm (U : MachineModel) where
  machine : SearchMachine U

/-- Correctness for a standard boundary term: it uniformly returns satisfying
witnesses for satisfiable CNF formulas. -/
def StandardTuringBoundaryTermCorrect
    {U : MachineModel}
    (T : StandardTuringBoundaryTerm U) : Prop :=
  SearchCorrect U T.machine

/-- There exists a standard Turing boundary term that solves SAT search. -/
def StandardTuringBoundarySolvesSAT
    (U : MachineModel) : Prop :=
  ∃ T : StandardTuringBoundaryTerm U,
    StandardTuringBoundaryTermCorrect T

/-- A correct standard boundary term is exactly an ordinary shallow SAT
searcher. -/
theorem standardTuringBoundarySolvesSAT_iff_shallowSATSearch
    (U : MachineModel) :
    StandardTuringBoundarySolvesSAT U ↔ ShallowSATSearch U := by
  constructor
  · intro h
    rcases h with ⟨T, hT⟩
    exact ⟨T.machine, hT⟩
  · intro h
    rcases h with ⟨M, hM⟩
    exact ⟨⟨M⟩, hM⟩

/-- Under deep SAT search, no standard Turing boundary term can solve SAT. -/
theorem no_standardTuringBoundarySolvesSAT_of_deepSATSearch
    (U : MachineModel)
    (hdeep : DeepSATSearch U) :
    ¬ StandardTuringBoundarySolvesSAT U := by
  intro hterm
  exact hdeep
    ((standardTuringBoundarySolvesSAT_iff_shallowSATSearch U).mp hterm)

/-! ## SPDP/log-det as proof metadata for a standard term -/

/-- A standard Turing boundary term equipped with an SPDP/log-det proof
certificate.

The actual SPDP algebra is deliberately not imported here.  The point of this
interface is independent of the certificate's internal representation: if the
certificate proves SAT-witness correctness for a standard Turing term, then it
has proved ordinary shallow SAT search. -/
structure SPDPProvedStandardTuringBoundaryTerm
    (U : MachineModel) where
  term : StandardTuringBoundaryTerm U
  spdpCertificate : Prop
  has_spdpCertificate : spdpCertificate
  spdp_proves_correct :
    spdpCertificate -> StandardTuringBoundaryTermCorrect term

/-- An SPDP-proved standard Turing term yields ordinary shallow SAT search. -/
theorem shallowSATSearch_of_spdpProvedStandardTuringBoundaryTerm
    (U : MachineModel)
    (T : SPDPProvedStandardTuringBoundaryTerm U) :
    ShallowSATSearch U :=
  ⟨T.term.machine, T.spdp_proves_correct T.has_spdpCertificate⟩

/-- With the prefix-unit compiler/accounting layer, an SPDP-proved standard
Turing term yields SAT decision in P for the same ordinary machine model. -/
theorem SATDecisionInP_of_spdpProvedStandardTuringBoundaryTerm
    {U : MachineModel}
    (_C : PrefixUnitMachineCompiler U)
    (T : SPDPProvedStandardTuringBoundaryTerm U) :
    SATDecisionInP U :=
  decider_of_shallowSATSearch U
    (shallowSATSearch_of_spdpProvedStandardTuringBoundaryTerm U T)

/-- Under deep SAT search, there is no SPDP-proved standard Turing SAT term.
This does not refute SPDP certificates in general; it only says that an SPDP
certificate proving full SAT search correctness for a standard polynomial
machine is already the forbidden shallow-search object. -/
theorem no_spdpProvedStandardTuringBoundaryTerm_of_deepSATSearch
    (U : MachineModel)
    (hdeep : DeepSATSearch U) :
    ¬ Nonempty (SPDPProvedStandardTuringBoundaryTerm U) := by
  intro hT
  rcases hT with ⟨T⟩
  exact hdeep (shallowSATSearch_of_spdpProvedStandardTuringBoundaryTerm U T)

/-! ## Equivalence to the decision target under the compiler -/

/-- Existence of an SPDP-proved standard Turing SAT term implies the ordinary
decision target.  The converse would require an SPDP certificate for the
compiled searcher, so it is intentionally not asserted here. -/
def SPDPStandardTuringTermWouldClose
    (U : MachineModel) : Prop :=
  Nonempty (SPDPProvedStandardTuringBoundaryTerm U)

/-- The SPDP-standard-term route is at least as strong as ordinary shallow SAT
search, and hence as SAT decision in P after verification. -/
theorem shallowSATSearch_of_SPDPStandardTuringTermWouldClose
    (U : MachineModel)
    (h : SPDPStandardTuringTermWouldClose U) :
    ShallowSATSearch U := by
  rcases h with ⟨T⟩
  exact shallowSATSearch_of_spdpProvedStandardTuringBoundaryTerm U T

/-- If the ordinary lower-bound target holds, the SPDP-standard-term closure
target cannot hold. -/
theorem not_SPDPStandardTuringTermWouldClose_of_deepSATSearch
    (U : MachineModel)
    (hdeep : DeepSATSearch U) :
    ¬ SPDPStandardTuringTermWouldClose U :=
  no_spdpProvedStandardTuringBoundaryTerm_of_deepSATSearch U hdeep

/-! ## Axiom trace -/

#print axioms standardTuringBoundarySolvesSAT_iff_shallowSATSearch
#print axioms no_standardTuringBoundarySolvesSAT_of_deepSATSearch
#print axioms shallowSATSearch_of_spdpProvedStandardTuringBoundaryTerm
#print axioms SATDecisionInP_of_spdpProvedStandardTuringBoundaryTerm
#print axioms no_spdpProvedStandardTuringBoundaryTerm_of_deepSATSearch
#print axioms shallowSATSearch_of_SPDPStandardTuringTermWouldClose
#print axioms not_SPDPStandardTuringTermWouldClose_of_deepSATSearch

end SATDepthMachine
