import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DTreeToDNF

/-!
# AC⁰ reduction, foundation 2: the dual decision-tree → CNF conversion (branch only)

The dual of brick 66.  A shallow decision tree is also a *CNF* (AND of ORs) of width `≤ depth`: one clause
per *rejecting* leaf, the OR of the negated path literals (false exactly when the path to that `false`-leaf
is taken).  This is the dual depth-reduction step: in the multi-round AC⁰ collapse one alternates
DNF→DT→CNF and CNF→DT→DNF so that two adjacent OR/AND layers merge.

* `cnfValue` — the CNF semantics (every clause has a true literal).
* `dtreeToCNF` — the rejecting-path CNF of a decision tree.
* `dtreeToCNF_eval` — it computes the same function (`cnfValue (dtreeToCNF t) = t.eval`).
* `dtreeToCNF_width` — every clause has `≤ depth t` literals.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- The CNF value of a list of clauses: every clause has a satisfied literal. -/
def cnfValue (cs : List (Clause n)) (x : Fin n → Bool) : Bool :=
  cs.all (fun C => C.lits.any (fun ℓ => Rung4Literal.eval ℓ x))

/-- The rejecting-path CNF of a decision tree: one clause per `false`-leaf, the OR of the negated path
literals (`neg v` on the `true` branch, `pos v` on the `false` branch). -/
def dtreeToCNF : DTree n → List (Clause n)
  | DTree.leaf true => []
  | DTree.leaf false => [⟨[]⟩]
  | DTree.node v lo hi =>
    (dtreeToCNF hi).map (fun C => ⟨Rung4Literal.neg v :: C.lits⟩)
      ++ (dtreeToCNF lo).map (fun C => ⟨Rung4Literal.pos v :: C.lits⟩)

/-- Prepending a literal to every clause factors the literal's value out of the conjunction (dual of
`any_map_cons_lit`). -/
theorem all_map_cons_lit (l : List (Clause n)) (ℓ : Rung4Literal n) (x : Fin n → Bool) :
    (l.map (fun C => (⟨ℓ :: C.lits⟩ : Clause n))).all (fun C => C.lits.any (fun m => Rung4Literal.eval m x))
      = (Rung4Literal.eval ℓ x
          || l.all (fun C => C.lits.any (fun m => Rung4Literal.eval m x))) := by
  induction l with
  | nil => simp only [List.map_nil, List.all_nil, Bool.or_true]
  | cons C rest ih =>
    rw [List.map_cons, List.all_cons, List.any_cons, ih, List.all_cons, Bool.or_and_distrib_left]

/-- **Eval correctness.**  The rejecting-path CNF computes the tree's function. -/
theorem dtreeToCNF_eval (t : DTree n) (x : Fin n → Bool) :
    cnfValue (dtreeToCNF t) x = t.eval x := by
  induction t with
  | leaf b => cases b <;> simp [dtreeToCNF, cnfValue, DTree.eval]
  | node v lo hi ihlo ihhi =>
    rw [dtreeToCNF, cnfValue, List.all_append, all_map_cons_lit, all_map_cons_lit,
      ← cnfValue, ← cnfValue, ihhi, ihlo, DTree.eval]
    simp only [Rung4Literal.eval]
    cases hv : x v <;> simp

/-- **Width bound.**  Every clause of the rejecting-path CNF has at most `depth t` literals. -/
theorem dtreeToCNF_width (t : DTree n) : ∀ C ∈ dtreeToCNF t, C.lits.length ≤ t.depth := by
  induction t with
  | leaf b => cases b <;> simp [dtreeToCNF]
  | node v lo hi ihlo ihhi =>
    intro C hC
    rw [dtreeToCNF, List.mem_append] at hC
    have hml := le_max_left lo.depth hi.depth
    have hmr := le_max_right lo.depth hi.depth
    cases hC with
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

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.dtreeToCNF_eval
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.dtreeToCNF_width
