import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DTreeToCNF

/-!
# AC⁰ reduction, foundation 11: decision-tree negation (branch only)

The last piece before the dual collapse round.  Negating a decision tree (swapping its leaves) computes
the negated function and preserves the depth.  Combined with De Morgan (brick 75), this lets a CNF gate
be switched via the DNF machinery: switch the literal-negated DNF to a shallow tree (the whole switching
arc), negate the tree's leaves, and the result computes the CNF with the same depth — ready to rewrite as
a width-`≤ depth` DNF (`dtreeToDNF`, brick 66).

* `DTree.negTree` — swap the leaves of a decision tree.
* `negTree_eval` — it computes the negated function.
* `negTree_depth` — it preserves the depth.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

namespace DTree

variable {n : ℕ}

/-- Negate a decision tree by swapping its leaves. -/
def negTree : DTree n → DTree n
  | leaf b => leaf (!b)
  | node v lo hi => node v (negTree lo) (negTree hi)

/-- **Negation computes the negated function.** -/
theorem negTree_eval (t : DTree n) (x : Fin n → Bool) : (negTree t).eval x = !(t.eval x) := by
  induction t with
  | leaf b => rfl
  | node v lo hi ihlo ihhi =>
    rw [negTree, eval, eval]
    cases hv : x v <;> simp [ihlo, ihhi]

/-- **Negation preserves the depth.** -/
theorem negTree_depth (t : DTree n) : (negTree t).depth = t.depth := by
  induction t with
  | leaf b => rfl
  | node v lo hi ihlo ihhi => rw [negTree, depth, depth, ihlo, ihhi]

end DTree

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.DTree.negTree_eval
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.DTree.negTree_depth
