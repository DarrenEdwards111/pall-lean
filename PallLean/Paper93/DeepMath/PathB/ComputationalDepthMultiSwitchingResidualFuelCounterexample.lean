import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMultiSwitchingCommonShallow

/-!
# Counterexample to residual depth implying a long common trace

The canonical family tree and the residual canonical trees are both built with the original `fuel`.
Consequently a family path may stop because its local recursive fuel reaches zero, while rebuilding
the gate at the reached restriction with the original fuel produces a nontrivial residual tree.

For the one-term DNF `x₀ ∧ x₁`, fuel one, and the all-true assignment, the common family tree asks
only `x₀` and then stops.  At the reached restriction, rebuilding with fuel one asks `x₁`.  Thus a
positive residual depth after a budget-two prefix does **not** imply a length-two common trace.
-/

namespace PallLean.Paper93.DeepMath.PathB.MultiSwitching.ResidualFuelCounterexample

open PallLean.Paper93.DeepMath.PathB.Depth3
open PallLean.Paper93.DeepMath.PathB.SwitchingCounting
open PallLean.Paper93.DeepMath.PathB.MultiSwitching

def gate : Clause 2 :=
  ⟨[Rung4Literal.pos (0 : Fin 2), Rung4Literal.pos (1 : Fin 2)]⟩

def gates : Fin 1 → List (Clause 2) := fun _ => [gate]
def root : Restriction 2 := ![none, none]
def assignment : Fin 2 → Bool := ![true, true]
def tree := canonicalFamilyTree gates 1 root

def prefixResidual : Restriction 2 :=
  CommonTree.run (CommonTree.prefixEndpoints root tree 2) assignment

theorem assignment_extends_root : Rung4Restriction.Extends root assignment := by
  intro v b hv
  fin_cases v <;> simp [root] at hv

theorem common_trace_stops_before_budget :
    (CommonTree.trace (CommonTree.readOnce root tree) assignment).length < 2 := by decide

theorem rebuilt_residual_is_deep :
    0 < (canonicalDT (gates (0 : Fin 1)) 1 prefixResidual).depth := by decide

/-- Kernel-checked falsification of the proposed residual-deep-to-long-trace implication. -/
theorem deep_residual_does_not_force_budget_trace :
    Rung4Restriction.Extends root assignment ∧
      (CommonTree.trace (CommonTree.readOnce root tree) assignment).length < 2 ∧
      0 < (canonicalDT (gates (0 : Fin 1)) 1
        (CommonTree.run (CommonTree.prefixEndpoints root tree 2) assignment)).depth :=
  ⟨assignment_extends_root, common_trace_stops_before_budget, rebuilt_residual_is_deep⟩

end PallLean.Paper93.DeepMath.PathB.MultiSwitching.ResidualFuelCounterexample

#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.ResidualFuelCounterexample.deep_residual_does_not_force_budget_trace
