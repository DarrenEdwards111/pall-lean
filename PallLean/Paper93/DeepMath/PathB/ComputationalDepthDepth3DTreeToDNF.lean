import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DnfTree

/-!
# AC⁰ reduction, foundation 1: the single-layer decision-tree → DNF conversion (branch only)

The first brick of the multi-round AC⁰ collapse.  A switching step turns a width-`w` DNF into a shallow
decision tree (depth `< s`, whp — the whole switching arc).  To reduce circuit depth one then rewrites
that decision tree *back* into a DNF, now of width `≤ depth`: one term per accepting leaf, conjoining the
path literals.  Iterating shrinks the circuit depth by one per round.

* `dtreeToDNF` — the accepting-path DNF of a decision tree.
* `dtreeToDNF_eval` — it computes the same function (`DTree.dnfValue (dtreeToDNF t) = t.eval`).
* `dtreeToDNF_width` — every term has `≤ depth t` literals.

So a depth-`d` decision tree is a width-`≤ d` DNF computing the same function — the depth-reduction step.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- The accepting-path DNF of a decision tree: one term per `true`-leaf, conjoining the path literals
(`pos v` on the `true` branch, `neg v` on the `false` branch). -/
def dtreeToDNF : DTree n → List (Clause n)
  | DTree.leaf true => [⟨[]⟩]
  | DTree.leaf false => []
  | DTree.node v lo hi =>
    (dtreeToDNF hi).map (fun T => ⟨Rung4Literal.pos v :: T.lits⟩)
      ++ (dtreeToDNF lo).map (fun T => ⟨Rung4Literal.neg v :: T.lits⟩)

/-- Prepending a literal to every term factors the literal's value out of the disjunction. -/
theorem any_map_cons_lit (l : List (Clause n)) (ℓ : Rung4Literal n) (x : Fin n → Bool) :
    (l.map (fun T => (⟨ℓ :: T.lits⟩ : Clause n))).any (fun T => T.lits.all (fun m => Rung4Literal.eval m x))
      = (Rung4Literal.eval ℓ x
          && l.any (fun T => T.lits.all (fun m => Rung4Literal.eval m x))) := by
  induction l with
  | nil => simp only [List.map_nil, List.any_nil, Bool.and_false]
  | cons T rest ih =>
    rw [List.map_cons, List.any_cons, List.any_cons, List.all_cons, ih,
      Bool.and_or_distrib_left]

/-- **Eval correctness.**  The accepting-path DNF computes the tree's function. -/
theorem dtreeToDNF_eval (t : DTree n) (x : Fin n → Bool) :
    DTree.dnfValue (dtreeToDNF t) x = t.eval x := by
  induction t with
  | leaf b => cases b <;> simp [dtreeToDNF, DTree.dnfValue, DTree.eval]
  | node v lo hi ihlo ihhi =>
    rw [dtreeToDNF, DTree.dnfValue, List.any_append, any_map_cons_lit, any_map_cons_lit,
      ← DTree.dnfValue, ← DTree.dnfValue, ihhi, ihlo, DTree.eval]
    simp only [Rung4Literal.eval]
    cases hv : x v <;> simp

/-- **Width bound.**  Every term of the accepting-path DNF has at most `depth t` literals. -/
theorem dtreeToDNF_width (t : DTree n) : ∀ T ∈ dtreeToDNF t, T.lits.length ≤ t.depth := by
  induction t with
  | leaf b => cases b <;> simp [dtreeToDNF]
  | node v lo hi ihlo ihhi =>
    intro T hT
    rw [dtreeToDNF, List.mem_append] at hT
    have hml := le_max_left lo.depth hi.depth
    have hmr := le_max_right lo.depth hi.depth
    cases hT with
    | inl h =>
      rw [List.mem_map] at h
      obtain ⟨S, hS, rfl⟩ := h
      simp only [List.length_cons, DTree.depth]
      have := ihhi S hS
      omega
    | inr h =>
      rw [List.mem_map] at h
      obtain ⟨S, hS, rfl⟩ := h
      simp only [List.length_cons, DTree.depth]
      have := ihlo S hS
      omega

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.dtreeToDNF_eval
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.dtreeToDNF_width
