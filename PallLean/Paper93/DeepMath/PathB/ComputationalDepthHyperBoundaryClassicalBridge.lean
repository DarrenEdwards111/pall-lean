import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHypercomputationalBoundaryTerm
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMachineCompiler

/-
# Classical bridge for the hypercomputational boundary term

`ComputationalDepthHypercomputationalBoundaryTerm.lean` proved the clean
observer-hierarchy statement:

  a hypercomputational boundary term `L_H(H(φ_obs))` makes SAT shallow for the
  extended observer model.

This file proves the corresponding no-shortcut theorem for the classical
surface.  Compiling that hyper-boundary term back into an ordinary
oracle-free polynomial machine is not an extra easier lemma; it is exactly
ordinary shallow SAT search.  With the standard prefix-unit
decision-to-search compiler available, it is exactly SAT decision in P.

Thus the book's hypercomputational term can explain how a stronger observer
"sees" NP, but using it to close the classical problem requires the full
classical lower-bound/separation target.
-/

namespace SATDepthMachine

/-! ## Hyper-boundary classical simulability -/

/-- The hyper-boundary SAT oracle is classically simulable over `U` if it can
be compiled into an oracle-free polynomial search machine over `U`. -/
def HyperBoundaryClassicallySimulable
    (H : HypercomputationalSATBoundaryTerm)
    (U : MachineModel) : Prop :=
  Nonempty (HyperBoundaryToClassicalCompiler H U)

/-- Shallow classical SAT search gives a compiler for any hyper-boundary term:
the compiled ordinary searcher simply ignores the hyper oracle and solves SAT
itself. -/
theorem hyperBoundaryCompiler_of_shallowSATSearch
    (H : HypercomputationalSATBoundaryTerm)
    (U : MachineModel)
    (hshallow : ShallowSATSearch U) :
    HyperBoundaryClassicallySimulable H U := by
  rcases hshallow with ⟨M, hM⟩
  exact ⟨{
    compiled := M
    preserves_correctness := by
      intro _hhyper
      exact hM
  }⟩

/-- A classical compiler for the hyper-boundary term is exactly shallow
classical SAT search. -/
theorem hyperBoundaryClassicallySimulable_iff_shallowSATSearch
    (H : HypercomputationalSATBoundaryTerm)
    (U : MachineModel) :
    HyperBoundaryClassicallySimulable H U ↔ ShallowSATSearch U := by
  constructor
  · intro hsim
    rcases hsim with ⟨K⟩
    exact shallowSATSearch_of_hyperBoundaryCompiler H U K
  · intro hshallow
    exact hyperBoundaryCompiler_of_shallowSATSearch H U hshallow

/-- Therefore, ruling out every classical simulation of the hyper-boundary
term is exactly deep classical SAT search. -/
theorem deepSATSearch_iff_no_hyperBoundaryClassicalSimulation
    (H : HypercomputationalSATBoundaryTerm)
    (U : MachineModel) :
    DeepSATSearch U ↔ ¬ HyperBoundaryClassicallySimulable H U := by
  constructor
  · intro hdeep hsim
    exact hdeep
      ((hyperBoundaryClassicallySimulable_iff_shallowSATSearch H U).mp hsim)
  · intro hno hshallow
    exact hno
      ((hyperBoundaryClassicallySimulable_iff_shallowSATSearch H U).mpr
        hshallow)

/-! ## Decision form under the concrete prefix-unit compiler -/

/-- Once the standard SAT decision-to-search compiler is available, classical
simulation of a hyper-boundary term is exactly polynomial-time SAT decision on
the ordinary model. -/
theorem hyperBoundaryClassicallySimulable_iff_SATDecisionInP
    (H : HypercomputationalSATBoundaryTerm)
    {U : MachineModel}
    (C : PrefixUnitMachineCompiler U) :
    HyperBoundaryClassicallySimulable H U ↔ SATDecisionInP U := by
  constructor
  · intro hsim
    exact decider_of_shallowSATSearch U
      ((hyperBoundaryClassicallySimulable_iff_shallowSATSearch H U).mp hsim)
  · intro hdec
    have hshallow : ShallowSATSearch U :=
      shallowSATSearch_of_decider_with_selfReduction
        C.toSelfReduction hdec
    exact (hyperBoundaryClassicallySimulable_iff_shallowSATSearch H U).mpr
      hshallow

/-- Equivalently, no classical compiler for the hyper-boundary term is exactly
no polynomial-time SAT decider, once the prefix-unit compiler/accounting layer
is present. -/
theorem no_hyperBoundaryClassicalSimulation_iff_no_SATDecisionInP
    (H : HypercomputationalSATBoundaryTerm)
    {U : MachineModel}
    (C : PrefixUnitMachineCompiler U) :
    (¬ HyperBoundaryClassicallySimulable H U) ↔ ¬ SATDecisionInP U := by
  constructor
  · intro hno hdec
    exact hno
      ((hyperBoundaryClassicallySimulable_iff_SATDecisionInP H C).mpr hdec)
  · intro hnodec hsim
    exact hnodec
      ((hyperBoundaryClassicallySimulable_iff_SATDecisionInP H C).mp hsim)

/-- Final packaged statement: the hypercomputational term separates observer
classes, but the classical bridge is the ordinary SAT lower-bound target. -/
theorem hyperBoundaryClassicalBridge_is_no_decider_target
    (H : HypercomputationalSATBoundaryTerm)
    {U : MachineModel}
    (C : PrefixUnitMachineCompiler U) :
    (DeepSATSearch U ↔ ¬ HyperBoundaryClassicallySimulable H U) ∧
      ((¬ HyperBoundaryClassicallySimulable H U) ↔ ¬ SATDecisionInP U) :=
  ⟨deepSATSearch_iff_no_hyperBoundaryClassicalSimulation H U,
    no_hyperBoundaryClassicalSimulation_iff_no_SATDecisionInP H C⟩

/-! ## Axiom trace -/

#print axioms hyperBoundaryCompiler_of_shallowSATSearch
#print axioms hyperBoundaryClassicallySimulable_iff_shallowSATSearch
#print axioms deepSATSearch_iff_no_hyperBoundaryClassicalSimulation
#print axioms hyperBoundaryClassicallySimulable_iff_SATDecisionInP
#print axioms no_hyperBoundaryClassicalSimulation_iff_no_SATDecisionInP
#print axioms hyperBoundaryClassicalBridge_is_no_decider_target

end SATDepthMachine
