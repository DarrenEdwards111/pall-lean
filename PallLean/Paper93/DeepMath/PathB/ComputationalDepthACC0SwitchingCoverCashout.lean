import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SeparatorTopCollapse
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ControlShrinkage

/-!
# Full switching-cover cash-out, charged against active variables

A single shallow restriction is not enough to decide SAT of the original circuit: it may omit the
only satisfying assignments.  The correct deterministic output of a switching argument is a cover
of the original SAT problem by residual decision trees.  This file packages exactly that semantic
obligation and charges both costs:

* at most `2^q` restriction leaves;
* decision-tree depth at most `d` on every leaf.

Total observer work is `leafCount * 2^d ≤ 2^(q+d)`.  For a separator-pivot circuit with `r+k`
active variables, a genuine `s`-bit saving therefore requires `q+d ≤ (r+k)-s`.

This is the complete Williams-facing interface for the current fragment.  Existing results that
produce only `∃ ρ, shallow(ρ)` do not construct this cover and cannot discharge its `correct` field.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SwitchingCoverCashout

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.ACC0OracleControl
open PallLean.Paper93.DeepMath.PathB.ACC0SeparatorPivotBranching
open PallLean.Paper93.DeepMath.PathB.ACC0SeparatorTopCollapse
open PallLean.Paper93.DeepMath.PathB.ACC0ControlShrinkage

variable {r k : ℕ}

/-- A semantic switching cover for one separator-pivot circuit. -/
structure SwitchingCover (C : SeparatorPivotCircuit r k) where
  /-- number of residual restriction leaves -/
  leafCount : ℕ
  /-- exponent budget for the number of leaves -/
  branchBits : ℕ
  /-- uniform decision-tree depth budget -/
  residualDepth : ℕ
  /-- residual decision tree at each leaf -/
  tree : Fin leafCount → BoolDecisionTree k
  /-- the leaves cover original satisfiability in both directions -/
  correct : (∃ σ p, C.eval σ p = true) ↔
    ∃ l : Fin leafCount, ∃ y, (tree l).eval y = true
  leafBound : leafCount ≤ 2 ^ branchBits
  depthBound : ∀ l, (tree l).depth ≤ residualDepth

/-- Uniform upper bound obtained by scanning every leaf observer. -/
def coverWork {C : SeparatorPivotCircuit r k} (S : SwitchingCover C) : ℕ :=
  S.leafCount * 2 ^ S.residualDepth

/-- Branch bits and residual depth add in the exponent. -/
theorem coverWork_le_combined {C : SeparatorPivotCircuit r k} (S : SwitchingCover C) :
    coverWork S ≤ 2 ^ (S.branchBits + S.residualDepth) := by
  unfold coverWork
  calc
    S.leafCount * 2 ^ S.residualDepth
        ≤ 2 ^ S.branchBits * 2 ^ S.residualDepth :=
          Nat.mul_le_mul_right _ S.leafBound
    _ = 2 ^ (S.branchBits + S.residualDepth) := by rw [Nat.pow_add]

/-- **Full active-normalized switching cash-out.**  All restriction leaves and all residual tree
states fit in `2^((r+k)-saving)` when their combined exponent does. -/
theorem coverWork_le_active_gap {C : SeparatorPivotCircuit r k} (S : SwitchingCover C)
    (saving : ℕ) (hs : saving ≤ r + k)
    (hbudget : S.branchBits + S.residualDepth ≤ (r + k) - saving) :
    coverWork S ≤ 2 ^ ((r + k) - saving) ∧ saving ≤ r + k := by
  refine ⟨(coverWork_le_combined S).trans ?_, hs⟩
  exact Nat.pow_le_pow_right (by norm_num) hbudget

/-- A positive combined gap gives strict improvement over brute force on the active variables. -/
theorem coverWork_lt_active_bruteforce {C : SeparatorPivotCircuit r k} (S : SwitchingCover C)
    (saving : ℕ) (hpos : 0 < saving) (hs : saving ≤ r + k)
    (hbudget : S.branchBits + S.residualDepth ≤ (r + k) - saving) :
    coverWork S < 2 ^ (r + k) := by
  apply lt_of_le_of_lt (coverWork_le_active_gap S saving hs hbudget).1
  exact Nat.pow_lt_pow_right (by norm_num) (by omega)

/-- A supplied shallow top tree is the degenerate one-leaf switching cover. -/
def oneLeafCover (C : SeparatorPivotCircuit r k) (T : BoolDecisionTree k)
    (hT : ∀ y, controlEval C.top y = T.eval y) : SwitchingCover C where
  leafCount := 1
  branchBits := 0
  residualDepth := T.depth
  tree := fun _ => T
  correct := by
    rw [sat_iff_decision_tree C T hT]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨0, y, hy⟩
    · rintro ⟨_, y, hy⟩
      exact ⟨y, hy⟩
  leafBound := by norm_num
  depthBound := fun _ => le_rfl

/-- The one-leaf cover recovers exactly the earlier top-collapse work. -/
theorem coverWork_oneLeaf (C : SeparatorPivotCircuit r k) (T : BoolDecisionTree k)
    (hT : ∀ y, controlEval C.top y = T.eval y) :
    coverWork (oneLeafCover C T hT) = topCollapseWork T := by
  simp [coverWork, oneLeafCover, topCollapseWork]

/-! ## Why one existential shallow restriction is insufficient -/

/-- Every control has a completely fixed restriction whose residual decision tree has depth zero.
Thus bare existence of a shallow restriction is universal and carries no original-SAT coverage. -/
theorem every_control_has_depth_zero_restriction (C : OracleControl k) :
    ∃ ρ : Fin k → Option Bool, ∃ T : BoolDecisionTree k,
      (∀ y, restrictedControlEval C ρ y = T.eval y) ∧ T.depth = 0 := by
  let ρ : Fin k → Option Bool := fun _ => some false
  obtain ⟨T, hT, hd⟩ := control_restriction_shallow C ρ
  have hfree : (leafFree ρ).card = 0 := by
    simp [leafFree, ρ]
  refine ⟨ρ, T, hT, ?_⟩
  omega

/-- Concrete coverage failure: the one-variable identity control is satisfiable, while its all-false
depth-zero restriction is unsatisfiable. -/
theorem shallow_single_leaf_can_lose_sat :
    ∃ (C : OracleControl 1) (ρ : Fin 1 → Option Bool),
      (∃ y, controlEval C y = true) ∧
      (∀ y, restrictedControlEval C ρ y = false) := by
  refine ⟨OracleControl.leaf 0, fun _ => some false, ?_, ?_⟩
  · exact ⟨fun _ => true, by simp [controlEval]⟩
  · intro y
    simp [restrictedControlEval, controlEval]

end PallLean.Paper93.DeepMath.PathB.ACC0SwitchingCoverCashout

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingCoverCashout.coverWork_le_combined
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingCoverCashout.coverWork_le_active_gap
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingCoverCashout.coverWork_lt_active_bruteforce
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingCoverCashout.oneLeafCover
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingCoverCashout.every_control_has_depth_zero_restriction
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingCoverCashout.shallow_single_leaf_can_lose_sat
