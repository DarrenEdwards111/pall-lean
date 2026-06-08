import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ACircuit

/-!
# AC⁰ reduction, foundation 4: the layer merge (branch only)

The structural core of one collapse round.  After a switching step the bottom gate (a width-`w` DNF/CNF)
becomes a shallow decision tree, which `dtreeToDNF`/`dtreeToCNF` (bricks 66–67) rewrite into the *same*
gate type as the layer just above it.  Two adjacent `AND` (resp. `OR`) layers then **merge** — preserving
the function and dropping the gate depth by one.

* `and_merge_eval` / `or_merge_eval` — flattening a nested `AND`/`OR` preserves the function.
* `depthList_append` — `depthList` of a concatenation is the max.
* `and_merge_depth` / `or_merge_depth` — the merge does not increase depth (and strictly decreases it when
  the merged-in gate is the deepest child) — the depth reduction of one round.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open ACircuit

variable {n : ℕ}

/-- **`AND`-merge preserves the function.**  `AND (AND a :: rest) = AND (a ++ rest)`. -/
theorem and_merge_eval (a rest : List (ACircuit n)) (x : Fin n → Bool) :
    (ACircuit.and (ACircuit.and a :: rest)).eval x = (ACircuit.and (a ++ rest)).eval x := by
  simp only [eval_and, List.all_cons, List.all_append]

/-- **`OR`-merge preserves the function.**  `OR (OR a :: rest) = OR (a ++ rest)`. -/
theorem or_merge_eval (a rest : List (ACircuit n)) (x : Fin n → Bool) :
    (ACircuit.or (ACircuit.or a :: rest)).eval x = (ACircuit.or (a ++ rest)).eval x := by
  simp only [eval_or, List.any_cons, List.any_append]

/-- `depthList` of a concatenation is the maximum. -/
theorem depthList_append (a b : List (ACircuit n)) :
    depthList (a ++ b) = max (depthList a) (depthList b) := by
  induction a with
  | nil => simp [depthList]
  | cons c a ih => rw [List.cons_append, depthList, ih, depthList, Nat.max_assoc]

/-- **`AND`-merge does not increase depth** (and drops it by one when the merged-in gate is the deepest). -/
theorem and_merge_depth (a rest : List (ACircuit n)) :
    depth (ACircuit.and (a ++ rest)) ≤ depth (ACircuit.and (ACircuit.and a :: rest)) := by
  rw [depth, depth, depthList_append, depthList, depth]
  omega

/-- **`OR`-merge does not increase depth** (and drops it by one when the merged-in gate is the deepest). -/
theorem or_merge_depth (a rest : List (ACircuit n)) :
    depth (ACircuit.or (a ++ rest)) ≤ depth (ACircuit.or (ACircuit.or a :: rest)) := by
  rw [depth, depth, depthList_append, depthList, depth]
  omega

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.and_merge_eval
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.and_merge_depth
