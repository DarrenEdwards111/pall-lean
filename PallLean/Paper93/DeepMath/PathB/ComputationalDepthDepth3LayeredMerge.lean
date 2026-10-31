import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3Layered

/-!
# AC⁰ reduction, foundation 28: the layered associative merge (branch only)

The structural step the multi-round loop needs between rounds.  A collapse turns each bottom gate into a
`CNF` (an `AND`-of-`OR`s) or `DNF` (an `OR`-of-`AND`s); when those sit under a matching gate, associativity
collapses the two levels into one — the depth-`-1` that `one_round_or` (brick 27) could not chain on its
own.  Concretely: an `AND` of `CNF` gates is a single `CNF` (concatenate the clause lists), and an `OR` of
`DNF` gates is a single `DNF`.

* `cnfValue_flatten` / `dnfValue_flatten` — `cnfValue`/`dnfValue` of a flattened clause list is the
  conjunction / disjunction of the pieces.
* `merge_gAnd_cnf` / `merge_gOr_dnf` — `eval (gAnd (cs.map cnf)) = eval (cnf cs.flatten)` and dually.
* `merge_gAnd_cnf_EquivOn` / `merge_gOr_dnf_EquivOn` — the same as an (unconditional) `EquivOn`, so a merge
  is a `Reduces` step (brick 20) on *any* subcube.

This lifts the `ACircuit`-level merge (brick 4: `and_merge_eval`/`or_merge_eval`) to the `Layered` tower,
giving the clean depth-`d → d-1` reduction the recursion chains.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

namespace Layered

variable {n : ℕ}

/-- `cnfValue` of a flattened clause list is the conjunction of the pieces (`AND` is associative). -/
theorem cnfValue_flatten (cs : List (List (Clause n))) (x : Fin n → Bool) :
    cnfValue cs.flatten x = cs.all (fun c => cnfValue c x) := by
  unfold cnfValue
  induction cs with
  | nil => rfl
  | cons c rest ih => rw [List.flatten_cons, List.all_append, List.all_cons, ih]

/-- `dnfValue` of a flattened clause list is the disjunction of the pieces (`OR` is associative). -/
theorem dnfValue_flatten (ds : List (List (Clause n))) (x : Fin n → Bool) :
    DTree.dnfValue ds.flatten x = ds.any (fun d => DTree.dnfValue d x) := by
  unfold DTree.dnfValue
  induction ds with
  | nil => rfl
  | cons d rest ih => rw [List.flatten_cons, List.any_append, List.any_cons, ih]

/-- **`AND`-of-`CNF`s merge.**  An `AND` of `CNF` gates is the single `CNF` whose clause list is the
concatenation. -/
theorem merge_gAnd_cnf (cs : List (List (Clause n))) (x : Fin n → Bool) :
    eval (gAnd (cs.map cnf)) x = eval (cnf cs.flatten) x := by
  rw [eval_cnf, cnfValue_flatten, eval_gAnd, List.all_map]
  simp only [Function.comp_def, eval_cnf]

/-- **`OR`-of-`DNF`s merge.**  An `OR` of `DNF` gates is the single `DNF` whose term list is the
concatenation. -/
theorem merge_gOr_dnf (ds : List (List (Clause n))) (x : Fin n → Bool) :
    eval (gOr (ds.map dnf)) x = eval (dnf ds.flatten) x := by
  rw [eval_dnf, dnfValue_flatten, eval_gOr, List.any_map]
  simp only [Function.comp_def, eval_dnf]

/-- The `AND`-of-`CNF`s merge as an (unconditional) subcube equivalence. -/
theorem merge_gAnd_cnf_EquivOn (ρ : Fin n → Option Bool) (cs : List (List (Clause n))) :
    EquivOn ρ (gAnd (cs.map cnf)) (cnf cs.flatten) :=
  fun x _ => merge_gAnd_cnf cs x

/-- The `OR`-of-`DNF`s merge as an (unconditional) subcube equivalence. -/
theorem merge_gOr_dnf_EquivOn (ρ : Fin n → Option Bool) (ds : List (List (Clause n))) :
    EquivOn ρ (gOr (ds.map dnf)) (dnf ds.flatten) :=
  fun x _ => merge_gOr_dnf ds x

end Layered

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.Layered.merge_gAnd_cnf
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.Layered.merge_gOr_dnf
