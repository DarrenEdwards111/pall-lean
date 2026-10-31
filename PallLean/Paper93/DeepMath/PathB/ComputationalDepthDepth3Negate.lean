import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DnfCircuit

/-!
# AC⁰ reduction, foundation 10: literal/De Morgan negation (branch only)

The bridge to the *dual* collapse round (OR-of-CNFs → DNF): a CNF is the negation of a DNF.  The switching
machinery is built for DNFs (`canonicalDTree`/`dnfValue`); via De Morgan a CNF `g` equals `¬` of the DNF
obtained by negating every literal, so a CNF round reduces to a DNF round on the negated gate.

* `negLit` — literal negation (`pos ↔ neg`); `negLit_eval` flips the value.
* `cnfValue_eq_not_dnfValue` — `cnfValue g = ¬ dnfValue (g with every literal negated)`.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- Literal negation. -/
def negLit : Rung4Literal n → Rung4Literal n
  | Rung4Literal.pos v => Rung4Literal.neg v
  | Rung4Literal.neg v => Rung4Literal.pos v

/-- Negating a literal flips its value. -/
@[simp] theorem negLit_eval (ℓ : Rung4Literal n) (x : Fin n → Bool) :
    (negLit ℓ).eval x = !(ℓ.eval x) := by
  cases ℓ <;> simp [negLit, Rung4Literal.eval]

private theorem all_congr {α : Type*} (l : List α) (p q : α → Bool) (h : ∀ a ∈ l, p a = q a) :
    l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.all_cons, List.all_cons, h a (List.mem_cons_self ..),
      ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

private theorem any_congr {α : Type*} (l : List α) (p q : α → Bool) (h : ∀ a ∈ l, p a = q a) :
    l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.any_cons, List.any_cons, h a (List.mem_cons_self ..),
      ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

/-- **De Morgan.**  A CNF is the negation of the DNF obtained by negating every literal. -/
theorem cnfValue_eq_not_dnfValue (g : List (Clause n)) (x : Fin n → Bool) :
    cnfValue g x = !(DTree.dnfValue (g.map (fun C => (⟨C.lits.map negLit⟩ : Clause n))) x) := by
  rw [cnfValue, DTree.dnfValue, List.any_map, List.not_any_eq_all_not]
  apply all_congr
  intro C _
  rw [Function.comp_apply, List.not_all_eq_any_not, List.any_map]
  apply any_congr
  intro ℓ _
  rw [Function.comp_apply, negLit_eval, Bool.not_not]

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.cnfValue_eq_not_dnfValue
