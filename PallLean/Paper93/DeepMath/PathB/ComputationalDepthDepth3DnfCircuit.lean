import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ACircuit

/-!
# AC⁰ reduction, foundation 7: DNF/CNF ↔ circuit translations (branch only)

The bridge between the switching world (a DNF/CNF as a `List (Clause n)`, the object the switching lemma
acts on) and the `ACircuit` world (the object the multi-round collapse recurses on).

* `dnfToCircuit` — a DNF as a depth-2 `OR`-of-`AND`s of literals; `dnfToCircuit_eval` matches `dnfValue`.
* `cnfToCircuit` — a CNF as a depth-2 `AND`-of-`OR`s of literals; `cnfToCircuit_eval` matches `cnfValue`.

So the canonical-tree → CNF rewrite (`dtreeToCNF`, brick 67) lands as a genuine depth-2 `AND`-of-`OR`s
subcircuit, ready for the layer merge (brick 69).

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open ACircuit SwitchingCounting

variable {n : ℕ}

/-- A DNF (list of terms) as a depth-2 `OR`-of-`AND`s of literals. -/
def dnfToCircuit (g : List (Clause n)) : ACircuit n :=
  ACircuit.or (g.map (fun T => ACircuit.and (T.lits.map ACircuit.lit)))

/-- A CNF (list of clauses) as a depth-2 `AND`-of-`OR`s of literals. -/
def cnfToCircuit (g : List (Clause n)) : ACircuit n :=
  ACircuit.and (g.map (fun C => ACircuit.or (C.lits.map ACircuit.lit)))

/-- **`dnfToCircuit` computes the DNF.** -/
theorem dnfToCircuit_eval (g : List (Clause n)) (x : Fin n → Bool) :
    (dnfToCircuit g).eval x = DTree.dnfValue g x := by
  rw [dnfToCircuit, eval_or, DTree.dnfValue, List.any_map]
  congr 1
  funext T
  rw [Function.comp_apply, eval_and, List.all_map]
  rfl

/-- **`cnfToCircuit` computes the CNF.** -/
theorem cnfToCircuit_eval (g : List (Clause n)) (x : Fin n → Bool) :
    (cnfToCircuit g).eval x = cnfValue g x := by
  rw [cnfToCircuit, eval_and, cnfValue, List.all_map]
  congr 1
  funext C
  rw [Function.comp_apply, eval_or, List.any_map]
  rfl

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.dnfToCircuit_eval
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.cnfToCircuit_eval
