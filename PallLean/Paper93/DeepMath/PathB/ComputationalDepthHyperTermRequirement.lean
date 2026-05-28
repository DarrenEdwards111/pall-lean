import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDiagonalHierarchyBridge

/-
# Hyper-term requirement as the classical lower-bound target

The N-frame book can legitimately model a stronger observer by adding a
hypercomputational SAT boundary term: the extended observer sees SAT through an
extra term that the ordinary Turing surface does not have.

The classical question is different.  To use that term to close the ordinary
P-vs-NP route one must prove that no classical polynomial surface can simulate
the hyper term.  This file names that statement and proves its accounting
content:

* "classical SAT requires the hyper-term" is exactly deep SAT search;
* with the prefix-unit decision/search compiler, it is exactly no SAT decision
  in P for the ordinary machine model;
* a genuine hierarchy/diagonal transport implies the hyper-term requirement.

So this is a clean N-frame theorem, but not a hidden proof of P vs NP.  The
load-bearing input remains the same lower-bound/diagonal target.
-/

namespace SATDepthMachine

/-! ## The requested requirement -/

/-- Classical SAT/NP requires the hyper-term when the hyper-boundary term is not
classically simulable by an oracle-free polynomial search surface. -/
def ClassicalNPRequiresHyperTerm
    (H : HypercomputationalSATBoundaryTerm)
    (U : MachineModel) : Prop :=
  ¬ HyperBoundaryClassicallySimulable H U

/-- The hyper-term requirement is exactly deep SAT search. -/
theorem classicalNPRequiresHyperTerm_iff_deepSATSearch
    (H : HypercomputationalSATBoundaryTerm)
    (U : MachineModel) :
    ClassicalNPRequiresHyperTerm H U ↔ DeepSATSearch U := by
  constructor
  · intro hreq
    exact (deepSATSearch_iff_no_hyperBoundaryClassicalSimulation H U).mpr hreq
  · intro hdeep
    exact (deepSATSearch_iff_no_hyperBoundaryClassicalSimulation H U).mp hdeep

/-- Under the standard prefix-unit compiler/accounting layer, requiring the
hyper-term is exactly the ordinary no-SAT-in-P target. -/
theorem classicalNPRequiresHyperTerm_iff_no_SATDecisionInP
    (H : HypercomputationalSATBoundaryTerm)
    {U : MachineModel}
    (C : PrefixUnitMachineCompiler U) :
    ClassicalNPRequiresHyperTerm H U ↔ ¬ SATDecisionInP U := by
  simpa [ClassicalNPRequiresHyperTerm] using
    (no_hyperBoundaryClassicalSimulation_iff_no_SATDecisionInP H C)

/-- Forward direction: if classical SAT really requires the hyper-term, then
there is no ordinary polynomial-time SAT decider. -/
theorem no_SATDecisionInP_of_classicalNPRequiresHyperTerm
    (H : HypercomputationalSATBoundaryTerm)
    {U : MachineModel}
    (C : PrefixUnitMachineCompiler U)
    (hreq : ClassicalNPRequiresHyperTerm H U) :
    ¬ SATDecisionInP U :=
  (classicalNPRequiresHyperTerm_iff_no_SATDecisionInP H C).mp hreq

/-- Reverse direction: the ordinary no-decider endpoint makes the hyper-term
classically necessary. -/
theorem classicalNPRequiresHyperTerm_of_no_SATDecisionInP
    (H : HypercomputationalSATBoundaryTerm)
    {U : MachineModel}
    (C : PrefixUnitMachineCompiler U)
    (hnodec : ¬ SATDecisionInP U) :
    ClassicalNPRequiresHyperTerm H U :=
  (classicalNPRequiresHyperTerm_iff_no_SATDecisionInP H C).mpr hnodec

/-- A hierarchy/diagonal transport supplies the hyper-term requirement.  This
records the right kind of possible breakthrough: a genuine diagonal escape
implies that the classical observer cannot simulate the hyper-boundary term. -/
theorem classicalNPRequiresHyperTerm_of_hierarchyTransport
    (H : HypercomputationalSATBoundaryTerm)
    (U : MachineModel)
    (T : ResourceBoundedGodelHierarchyTransport U) :
    ClassicalNPRequiresHyperTerm H U :=
  no_hyperBoundaryClassicalSimulation_of_hierarchyTransport H U T

/-- Conversely, the hyper-term requirement noncomputably packages into the same
hierarchy-transport target.  This is an equivalence/guardrail, not a construction
method: it uses the existing `DeepSATSearch` equivalence. -/
noncomputable def hierarchyTransport_of_classicalNPRequiresHyperTerm
    (H : HypercomputationalSATBoundaryTerm)
    (U : MachineModel)
    (hreq : ClassicalNPRequiresHyperTerm H U) :
    ResourceBoundedGodelHierarchyTransport U :=
  hierarchyTransport_of_deepSATSearch U
    ((classicalNPRequiresHyperTerm_iff_deepSATSearch H U).mp hreq)

/-- Existence of a hierarchy transport is equivalent to the hyper-term
requirement. -/
theorem hierarchyTransport_iff_classicalNPRequiresHyperTerm
    (H : HypercomputationalSATBoundaryTerm)
    (U : MachineModel) :
    Nonempty (ResourceBoundedGodelHierarchyTransport U) ↔
      ClassicalNPRequiresHyperTerm H U := by
  constructor
  · intro hT
    rcases hT with ⟨T⟩
    exact classicalNPRequiresHyperTerm_of_hierarchyTransport H U T
  · intro hreq
    exact ⟨hierarchyTransport_of_classicalNPRequiresHyperTerm H U hreq⟩

/-- Final packaged status: the book's hyper-term is a legitimate stronger
observer term, but proving that the classical observer requires it is exactly
the ordinary no-decider target, and the same as the hierarchy/diagonal target. -/
theorem hyperTermRequirement_is_classical_lower_bound_target
    (H : HypercomputationalSATBoundaryTerm)
    {U : MachineModel}
    (C : PrefixUnitMachineCompiler U) :
    (ClassicalNPRequiresHyperTerm H U ↔ DeepSATSearch U) ∧
      (ClassicalNPRequiresHyperTerm H U ↔ ¬ SATDecisionInP U) ∧
        (Nonempty (ResourceBoundedGodelHierarchyTransport U) ↔
          ClassicalNPRequiresHyperTerm H U) :=
  ⟨classicalNPRequiresHyperTerm_iff_deepSATSearch H U,
    classicalNPRequiresHyperTerm_iff_no_SATDecisionInP H C,
      hierarchyTransport_iff_classicalNPRequiresHyperTerm H U⟩

/-! ## Axiom trace -/

#print axioms classicalNPRequiresHyperTerm_iff_deepSATSearch
#print axioms classicalNPRequiresHyperTerm_iff_no_SATDecisionInP
#print axioms no_SATDecisionInP_of_classicalNPRequiresHyperTerm
#print axioms classicalNPRequiresHyperTerm_of_no_SATDecisionInP
#print axioms classicalNPRequiresHyperTerm_of_hierarchyTransport
#print axioms hierarchyTransport_of_classicalNPRequiresHyperTerm
#print axioms hierarchyTransport_iff_classicalNPRequiresHyperTerm
#print axioms hyperTermRequirement_is_classical_lower_bound_target

end SATDepthMachine
