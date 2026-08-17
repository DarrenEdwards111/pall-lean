import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SeparatorPivotUniversalityNoGo
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0DecisionTreeObserver

/-!
# The surviving positive fragment: collapse the top control, normalized to active variables

The separator-pivot universality theorem closed ordinary separator branching: the layer has `r+k`
active variables and preserves an arbitrary top control.  A real speedup must therefore simplify
that control.  This file proves the exact positive interface when the top is computed by a decision
tree of depth `d`.

First, separator branching disappears completely: satisfiability can be tested on one canonical
separator assignment because the pivots realize every control input on that branch.  Second, the
decision-tree leaf observer costs at most `2^d`.  If `d ≤ (r+k)-s`, this gives `2^((r+k)-s)` work,
with the exponent measured against the true active-variable count.

No padding is used.  The remaining hard theorem is precisely a switching theorem that makes the
restricted top control shallow while preserving this saving after all restriction probabilities or
deterministic leaves are accounted for.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SeparatorTopCollapse

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.ACC0OracleControl
open PallLean.Paper93.DeepMath.PathB.ACC0SeparatorPivotBranching
open PallLean.Paper93.DeepMath.PathB.ACC0DecisionTreeObserver

variable {r k : ℕ}

/-- One fixed separator branch is enough: private pivots realize every top-control input there. -/
theorem one_separator_branch_iff (C : SeparatorPivotCircuit r k) (σ₀ : Fin r → Bool) :
    (∃ σ p, C.eval σ p = true) ↔ ∃ p, C.eval σ₀ p = true := by
  constructor
  · intro h
    have htop : ∃ y, controlEval C.top y = true := (sat_iff_top C).mp h
    obtain ⟨y, hy⟩ := htop
    refine ⟨pivotsFor C.layer σ₀ y, ?_⟩
    unfold SeparatorPivotCircuit.eval
    rw [gateVector_pivotsFor]
    exact hy
  · rintro ⟨p, hp⟩
    exact ⟨σ₀, p, hp⟩

/-- If the top control is computed by `T`, circuit SAT is exactly decision-tree SAT. -/
theorem sat_iff_decision_tree (C : SeparatorPivotCircuit r k) (T : BoolDecisionTree k)
    (hT : ∀ y, controlEval C.top y = T.eval y) :
    (∃ σ p, C.eval σ p = true) ↔ ∃ y, T.eval y = true := by
  rw [sat_iff_top]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, hT y ▸ hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, (hT y).symm ▸ hy⟩

/-- Observer work after top-control collapse. -/
def topCollapseWork (T : BoolDecisionTree k) : ℕ := 2 ^ T.depth

/-- **Active-normalized linear saving.**  A depth gap of `saving` below the actual `r+k` active
variables gives the genuine bound `2^((r+k)-saving)`. -/
theorem topCollapseWork_le_active_gap (T : BoolDecisionTree k) (saving : ℕ)
    (hs : saving ≤ r + k) (hdepth : T.depth ≤ (r + k) - saving) :
    topCollapseWork T ≤ 2 ^ ((r + k) - saving) ∧ saving ≤ r + k := by
  refine ⟨Nat.pow_le_pow_right (by norm_num) hdepth, hs⟩

/-- A positive depth gap gives a strict improvement over brute force on all active variables. -/
theorem topCollapseWork_lt_active_bruteforce (T : BoolDecisionTree k) (saving : ℕ)
    (hpos : 0 < saving) (hs : saving ≤ r + k)
    (hdepth : T.depth ≤ (r + k) - saving) :
    topCollapseWork T < 2 ^ (r + k) := by
  apply lt_of_le_of_lt (topCollapseWork_le_active_gap (r := r) T saving hs hdepth).1
  exact Nat.pow_lt_pow_right (by norm_num) (by omega)

/-- Full positive cash-out: semantic reduction to the shallow top plus a strict active-variable
speedup, with no enumeration of separator assignments. -/
theorem separator_top_collapse_speedup (C : SeparatorPivotCircuit r k) (T : BoolDecisionTree k)
    (hT : ∀ y, controlEval C.top y = T.eval y) (saving : ℕ)
    (hpos : 0 < saving) (hs : saving ≤ r + k)
    (hdepth : T.depth ≤ (r + k) - saving) :
    ((∃ σ p, C.eval σ p = true) ↔ ∃ y, T.eval y = true) ∧
      topCollapseWork T < 2 ^ (r + k) :=
  ⟨sat_iff_decision_tree C T hT,
    topCollapseWork_lt_active_bruteforce (r := r) T saving hpos hs hdepth⟩

end PallLean.Paper93.DeepMath.PathB.ACC0SeparatorTopCollapse

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SeparatorTopCollapse.one_separator_branch_iff
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SeparatorTopCollapse.sat_iff_decision_tree
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SeparatorTopCollapse.topCollapseWork_le_active_gap
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SeparatorTopCollapse.separator_top_collapse_speedup
