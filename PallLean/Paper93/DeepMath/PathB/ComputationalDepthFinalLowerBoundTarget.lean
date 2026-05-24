import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSelfHostedUniversal

/-
# Final computational-depth lower-bound target

All compiler, canonical-surface, and self-hosted universal wiring has now been
isolated.  This file expands the one remaining theorem into its exact
machine-level form.

It does not prove the lower bound.  Instead it proves that the lower bound is
precisely:

  every polynomial-budget canonical SAT search machine fails on some satisfiable
  CNF formula.

That is the metacomplexity/P-vs-NP content.  Any future positive proof has to
construct a proof of this expanded predicate.
-/

namespace SATDepthMachine

/-! ## Expanded failure predicate -/

/-- A particular polynomial-budget canonical search machine fails on some
satisfiable formula: there is a satisfiable `φ` for which the machine does not
return any satisfying assignment. -/
def SearchMachineFailsOnSomeSAT
    (C : CanonicalMachineSurface)
    (M : SearchMachine C.toMachineModel) : Prop :=
  ∃ φ : CNF,
    Satisfiable φ ∧
      ¬ ∃ a : RawAssignment,
        C.toMachineModel.searchRun M.code φ = some a ∧ Satisfies φ a

/-- Negating search correctness is exactly failing on some satisfiable formula.
-/
theorem not_searchCorrect_iff_failsOnSomeSAT
    (C : CanonicalMachineSurface)
    (M : SearchMachine C.toMachineModel) :
    ¬ SearchCorrect C.toMachineModel M ↔
      SearchMachineFailsOnSomeSAT C M := by
  classical
  constructor
  · intro hnot
    by_contra hnofail
    apply hnot
    intro φ hsat
    by_contra hnowitness
    exact hnofail ⟨φ, hsat, hnowitness⟩
  · intro hfail hcorrect
    rcases hfail with ⟨φ, hsat, hnowitness⟩
    exact hnowitness (hcorrect φ hsat)

/-! ## Exact final target -/

/-- Canonical deep SAT search is exactly the statement that every
polynomial-budget canonical search machine fails on some satisfiable CNF. -/
theorem canonicalDeepSATSearch_iff_forall_searchMachineFails
    (C : CanonicalMachineSurface) :
    CanonicalDeepSATSearch C ↔
      ∀ M : SearchMachine C.toMachineModel,
        SearchMachineFailsOnSomeSAT C M := by
  constructor
  · intro hdeep M
    exact (not_searchCorrect_iff_failsOnSomeSAT C M).mp
      (by
        intro hcorrect
        exact hdeep ⟨M, hcorrect⟩)
  · intro hfail hshallow
    rcases hshallow with ⟨M, hcorrect⟩
    exact ((not_searchCorrect_iff_failsOnSomeSAT C M).mpr (hfail M))
      hcorrect

/-- Equivalent non-packaged form: no canonical search machine is correct on all
satisfiable formulas. -/
theorem canonicalDeepSATSearch_iff_forall_not_searchCorrect
    (C : CanonicalMachineSurface) :
    CanonicalDeepSATSearch C ↔
      ∀ M : SearchMachine C.toMachineModel,
        ¬ SearchCorrect C.toMachineModel M := by
  constructor
  · intro hdeep M hcorrect
    exact hdeep ⟨M, hcorrect⟩
  · intro hnot hshallow
    rcases hshallow with ⟨M, hcorrect⟩
    exact hnot M hcorrect

/-- Positive closure stated directly from the expanded final target. -/
theorem noCanonicalSATDecisionInP_of_forall_searchMachineFails
    (C : CanonicalMachineSurface)
    (hfail :
      ∀ M : SearchMachine C.toMachineModel,
        SearchMachineFailsOnSomeSAT C M) :
    ¬ CanonicalSATDecisionInP C :=
  canonicalNoDecider_of_deepSATSearch C
    ((canonicalDeepSATSearch_iff_forall_searchMachineFails C).mpr hfail)

/-- Self-hosted universal closure from the expanded final target. -/
theorem noSelfHostedIntendedSATDecisionInP_of_forall_searchMachineFails
    (C : CanonicalMachineSurface)
    (hfail :
      ∀ M : SearchMachine C.toMachineModel,
        SearchMachineFailsOnSomeSAT C M) :
    ¬ UniversalIntendedSATDecisionInP
      (selfHostedUniversalCanonicalSurface C) :=
  selfHostedClosure_of_remainingLowerBound C
    ((canonicalDeepSATSearch_iff_forall_searchMachineFails C).mpr hfail)

/-! ## Kernel-only axiom trace -/

#print axioms not_searchCorrect_iff_failsOnSomeSAT
#print axioms canonicalDeepSATSearch_iff_forall_searchMachineFails
#print axioms canonicalDeepSATSearch_iff_forall_not_searchCorrect
#print axioms noCanonicalSATDecisionInP_of_forall_searchMachineFails
#print axioms noSelfHostedIntendedSATDecisionInP_of_forall_searchMachineFails

end SATDepthMachine
