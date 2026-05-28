import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSubfunctionObserverInvariant

/-!
# Subfunction capacity wall

**STATUS: NEGATIVE/WALL RESULT, NOT A LOWER-BOUND BREAKTHROUGH.**

The subfunction observer invariant is super-polynomial-capable, but it does not
by itself give super-polynomial lower bounds for strong unrestricted models.  To
use it, one must prove a model-specific theorem saying that small models expose
only few residual/subfunctions.

This file formalizes the obstruction.  A fully unrestricted truth-table model can
store an arbitrary split Boolean function as one semantic object.  Therefore it
can compute the equality-split function while exposing `2^n` residuals at unit
syntactic budget.  Any blanket polynomial-capacity theorem for unrestricted
semantic models is false.

For TC⁰/NC¹/width-5 BP, the analogous capacity theorem is exactly the hard
lower-bound content; it cannot be obtained from the observer invariant alone.
-/

namespace PallLean.Paper93.DeepMath.PathB

/-! ## Unrestricted semantic truth-table model -/

/-- A completely unrestricted split Boolean-function model.  This is deliberately
semantic: the model stores the whole two-sided truth table. -/
structure UnrestrictedTruthTableModel (Left Right : Type) where
  table : (Left -> Bool) -> (Right -> Bool) -> Bool

namespace UnrestrictedTruthTableModel

/-- Semantic computation for split functions. -/
def Computes {Left Right : Type}
    (M : UnrestrictedTruthTableModel Left Right)
    (Target : (Left -> Bool) -> (Right -> Bool) -> Bool) : Prop :=
  forall a b, M.table a b = Target a b

/-- The exposed residual capacity of the stored table. -/
noncomputable def residualCapacity {Left Right : Type} [Fintype Left] [DecidableEq Left]
    (M : UnrestrictedTruthTableModel Left Right) : Nat :=
  subfunctionCount Left Right M.table

/-- A deliberately tiny syntactic budget: one semantic truth-table object. -/
def syntacticBudget {_Left _Right : Type}
    (_M : UnrestrictedTruthTableModel _Left _Right) : Nat :=
  1

/-- Exact truth-table model for equality split. -/
def equalityModel (n : Nat) : UnrestrictedTruthTableModel (Fin n) (Fin n) where
  table := equalitySplitFunction (Fin n)

/-- The equality model computes equality split. -/
theorem equalityModel_computes (n : Nat) :
    (equalityModel n).Computes (equalitySplitFunction (Fin n)) := by
  intro a b
  rfl

/-- The equality model exposes exponentially many residuals. -/
theorem equalityModel_residualCapacity (n : Nat) :
    (equalityModel n).residualCapacity = 2 ^ n := by
  classical
  exact subfunctionCount_equalitySplit_fin n

/-- The equality model has unit syntactic budget. -/
theorem equalityModel_syntacticBudget (n : Nat) :
    (equalityModel n).syntacticBudget = 1 := rfl

/-- For every positive split size, the residual capacity of the unit-budget
unrestricted equality model already exceeds its syntactic budget. -/
theorem equalityModel_budget_lt_residualCapacity
    {n : Nat} (hn : 0 < n) :
    (equalityModel n).syntacticBudget < (equalityModel n).residualCapacity := by
  rw [equalityModel_syntacticBudget, equalityModel_residualCapacity]
  exact Nat.one_lt_two_pow (Nat.ne_of_gt hn)

/-- Hence no theorem of the form "every unrestricted semantic model has residual
capacity bounded by its unit syntactic budget" can hold. -/
theorem no_unit_capacity_bound_for_unrestricted_models
    {n : Nat} (hn : 0 < n) :
    Not (forall M : UnrestrictedTruthTableModel (Fin n) (Fin n),
      M.residualCapacity <= M.syntacticBudget) := by
  intro h
  have hbad := h (equalityModel n)
  exact Nat.not_lt_of_ge hbad (equalityModel_budget_lt_residualCapacity hn)

/-- More generally, any claimed residual-capacity upper bound `bound n` for all
unit-budget unrestricted models must already dominate `2^n`, because the equality
model is a counterexample below that threshold. -/
theorem unrestricted_capacity_bound_must_dominate_exponential
    (bound : Nat -> Nat)
    (hbound : forall n : Nat, forall M : UnrestrictedTruthTableModel (Fin n) (Fin n),
      M.syntacticBudget <= 1 -> M.residualCapacity <= bound n) :
    forall n : Nat, 2 ^ n <= bound n := by
  intro n
  have h := hbound n (equalityModel n) (by simp [syntacticBudget])
  simpa [equalityModel_residualCapacity] using h

end UnrestrictedTruthTableModel

/-! ## Wall package -/

/-- The subfunction-capacity wall: unrestricted semantic models can have
exponential residual capacity at unit syntactic budget.  Therefore a
super-polynomial observer lower bound needs a genuine model-specific capacity
upper bound for the restricted syntax under study. -/
structure SubfunctionCapacityWall : Prop where
  equality_capacity : forall n : Nat,
    (UnrestrictedTruthTableModel.equalityModel n).residualCapacity = 2 ^ n
  unit_budget_gap : forall {n : Nat}, 0 < n ->
    (UnrestrictedTruthTableModel.equalityModel n).syntacticBudget <
      (UnrestrictedTruthTableModel.equalityModel n).residualCapacity
  bound_must_dominate_exponential : forall bound : Nat -> Nat,
    (forall n : Nat, forall M : UnrestrictedTruthTableModel (Fin n) (Fin n),
      M.syntacticBudget <= 1 -> M.residualCapacity <= bound n) ->
    forall n : Nat, 2 ^ n <= bound n

/-- Completed wall theorem. -/
theorem subfunctionCapacityWall : SubfunctionCapacityWall where
  equality_capacity := UnrestrictedTruthTableModel.equalityModel_residualCapacity
  unit_budget_gap := by
    intro n hn
    exact UnrestrictedTruthTableModel.equalityModel_budget_lt_residualCapacity hn
  bound_must_dominate_exponential :=
    UnrestrictedTruthTableModel.unrestricted_capacity_bound_must_dominate_exponential

/-! ## Kernel-only trace -/

#print axioms UnrestrictedTruthTableModel.equalityModel_computes
#print axioms UnrestrictedTruthTableModel.equalityModel_residualCapacity
#print axioms UnrestrictedTruthTableModel.equalityModel_budget_lt_residualCapacity
#print axioms UnrestrictedTruthTableModel.no_unit_capacity_bound_for_unrestricted_models
#print axioms UnrestrictedTruthTableModel.unrestricted_capacity_bound_must_dominate_exponential
#print axioms subfunctionCapacityWall

end PallLean.Paper93.DeepMath.PathB
