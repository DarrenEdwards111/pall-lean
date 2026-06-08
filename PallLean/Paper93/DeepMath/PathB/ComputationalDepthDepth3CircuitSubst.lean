import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3LayerMerge

/-!
# AC⁰ reduction, foundation 5: the circuit substitution congruence (branch only)

The tree-surgery correctness for one collapse round: replacing each bottom gate by an *eval-equivalent*
circuit (its switching-converted `dtreeToCNF`/`dtreeToDNF`) preserves the parent gate's function.  This is
the congruence the per-gate switching plugs into — combined with the layer merge (brick 69) it realises
the depth reduction.

* `and_map_eval` / `or_map_eval` — mapping an eval-preserving replacement over a gate's children preserves
  the gate's function.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open ACircuit

variable {n : ℕ}

/-- `List.all` over pointwise-equal predicates agree (local copy). -/
private theorem all_pointwise {α : Type*} (l : List α) (p q : α → Bool)
    (h : ∀ a ∈ l, p a = q a) : l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.all_cons, List.all_cons, h a (List.mem_cons_self ..),
      ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

/-- `List.any` over pointwise-equal predicates agree (local copy). -/
private theorem any_pointwise {α : Type*} (l : List α) (p q : α → Bool)
    (h : ∀ a ∈ l, p a = q a) : l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.any_cons, List.any_cons, h a (List.mem_cons_self ..),
      ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

/-- **`AND` substitution congruence.**  Replacing each child of an `AND` by an eval-equivalent circuit
preserves the function. -/
theorem and_map_eval (f : ACircuit n → ACircuit n) (gs : List (ACircuit n)) (x : Fin n → Bool)
    (hf : ∀ g ∈ gs, (f g).eval x = g.eval x) :
    (ACircuit.and (gs.map f)).eval x = (ACircuit.and gs).eval x := by
  rw [eval_and, eval_and, List.all_map]
  exact all_pointwise gs (fun g => (f g).eval x) (fun g => g.eval x) hf

/-- **`OR` substitution congruence.**  Replacing each child of an `OR` by an eval-equivalent circuit
preserves the function. -/
theorem or_map_eval (f : ACircuit n → ACircuit n) (gs : List (ACircuit n)) (x : Fin n → Bool)
    (hf : ∀ g ∈ gs, (f g).eval x = g.eval x) :
    (ACircuit.or (gs.map f)).eval x = (ACircuit.or gs).eval x := by
  rw [eval_or, eval_or, List.any_map]
  exact any_pointwise gs (fun g => (f g).eval x) (fun g => g.eval x) hf

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.and_map_eval
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.or_map_eval
