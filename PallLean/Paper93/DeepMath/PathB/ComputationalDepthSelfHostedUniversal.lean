import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUniversalCanonicalSurface

/-
# Self-hosted universal canonical layer

`ComputationalDepthUniversalCanonicalSurface.lean` defined the completeness
interface from an intended oracle-free machine class into a canonical surface.

This file constructs the canonical self-hosted instance: every
`CanonicalMachineSurface` induces an intended machine class whose programs are
the canonical codes themselves.  Completeness is identity compilation.

This discharges the "universal/completeness wiring" in the honest self-hosted
sense.  It still does not prove `CanonicalDeepSATSearch`; that lower bound is
the P-vs-NP/metacomplexity theorem itself.
-/

namespace SATDepthMachine

/-! ## Canonical surfaces as intended machine classes -/

/-- The intended machine class obtained by reading a canonical surface as its
own program model.  Search and decision programs are natural-number canonical
codes. -/
def canonicalIntendedClass
    (C : CanonicalMachineSurface) : IntendedMachineClass where
  SearchProgram := Nat
  DecisionProgram := Nat
  searchRun := C.searchRun
  searchSteps := C.searchRuntime
  decisionRun := C.decisionRun
  decisionSteps := C.decisionRuntime
  oracleFree := C.oracleFree
  oracleFree_cert := C.oracleFree_cert

/-- Identity completeness of a canonical surface for its self-hosted intended
class. -/
def canonicalSelfCompleteness
    (C : CanonicalMachineSurface) :
    UniversalCanonicalCompleteness (canonicalIntendedClass C) C where
  compileSearchCode := id
  compileDecisionCode := id
  search_run_eq := by
    intro P φ
    rfl
  decision_run_eq := by
    intro P φ
    rfl
  search_steps_le_budget := by
    intro M φ
    exact M.steps_le_budget φ
  decision_steps_le_budget := by
    intro M φ
    exact M.steps_le_budget φ

/-- The universal package induced by a canonical surface itself. -/
def selfHostedUniversalCanonicalSurface
    (C : CanonicalMachineSurface) : UniversalCanonicalSurface where
  intended := canonicalIntendedClass C
  surface := C
  completeness := canonicalSelfCompleteness C

/-! ## Equivalence with the canonical machine predicates -/

/-- Intended SAT decision in the self-hosted class is exactly canonical SAT
decision for the underlying surface. -/
theorem intendedSATDecisionInP_selfHosted_iff_canonical
    (C : CanonicalMachineSurface) :
    IntendedSATDecisionInP (canonicalIntendedClass C) ↔
      CanonicalSATDecisionInP C := by
  constructor
  · intro h
    exact canonicalSATDecisionInP_of_intendedSATDecisionInP
      (canonicalSelfCompleteness C) h
  · intro h
    rcases h with ⟨M, hM⟩
    refine ⟨{
      program := M.code
      budget := M.budget
      polyBudget := M.polyBudget
      steps_le_budget := ?_
    }, ?_⟩
    · intro φ
      exact M.steps_le_budget φ
    · intro φ
      exact hM φ

/-- Intended shallow SAT search in the self-hosted class is exactly canonical
shallow SAT search for the underlying surface. -/
theorem intendedShallowSATSearch_selfHosted_iff_canonical
    (C : CanonicalMachineSurface) :
    IntendedShallowSATSearch (canonicalIntendedClass C) ↔
      ShallowSATSearch C.toMachineModel := by
  constructor
  · intro h
    exact canonicalShallowSATSearch_of_intendedShallowSATSearch
      (canonicalSelfCompleteness C) h
  · intro h
    rcases h with ⟨M, hM⟩
    refine ⟨{
      program := M.code
      budget := M.budget
      polyBudget := M.polyBudget
      steps_le_budget := ?_
    }, ?_⟩
    · intro φ
      exact M.steps_le_budget φ
    · intro φ hsat
      exact hM φ hsat

/-! ## Final self-hosted closure form -/

/-- In the self-hosted universal package, proving canonical deep search rules
out polynomial SAT decision in the self-hosted intended class. -/
theorem selfHostedNoIntendedSATDecisionInP_of_deepSATSearch
    (C : CanonicalMachineSurface)
    (hdeep : CanonicalDeepSATSearch C) :
    ¬ IntendedSATDecisionInP (canonicalIntendedClass C) :=
  universalNoIntendedSATDecisionInP_of_deepSATSearch
    (selfHostedUniversalCanonicalSurface C) hdeep

/-- The self-hosted closure theorem restated directly against canonical SAT
decision.  This is the same closure theorem already proved at the canonical
level; the point of this file is that the universal/completeness layer now
commutes with it by identity compilation. -/
theorem selfHostedNoCanonicalSATDecisionInP_of_deepSATSearch
    (C : CanonicalMachineSurface)
    (hdeep : CanonicalDeepSATSearch C) :
    ¬ CanonicalSATDecisionInP C :=
  canonicalNoDecider_of_deepSATSearch C hdeep

/-- The exact remaining theorem for the self-hosted universal package. -/
def SelfHostedRemainingLowerBound
    (C : CanonicalMachineSurface) : Prop :=
  CanonicalDeepSATSearch C

theorem selfHostedClosure_of_remainingLowerBound
    (C : CanonicalMachineSurface)
    (h : SelfHostedRemainingLowerBound C) :
    ¬ UniversalIntendedSATDecisionInP
      (selfHostedUniversalCanonicalSurface C) :=
  universalNoIntendedSATDecisionInP_of_deepSATSearch
    (selfHostedUniversalCanonicalSurface C) h

/-! ## Kernel-only axiom trace -/

#print axioms canonicalIntendedClass
#print axioms canonicalSelfCompleteness
#print axioms selfHostedUniversalCanonicalSurface
#print axioms intendedSATDecisionInP_selfHosted_iff_canonical
#print axioms intendedShallowSATSearch_selfHosted_iff_canonical
#print axioms selfHostedClosure_of_remainingLowerBound

end SATDepthMachine
