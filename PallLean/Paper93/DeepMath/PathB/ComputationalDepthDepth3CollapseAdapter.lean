import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseInterface
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingCanonicalPath

/-!
# The OR/AND object adapter (switching DNF ↔ ΣΠΣ middle-layer CNF)

**STATUS: REAL.  THE DE MORGAN ADAPTER — A HONEST PREREQUISITE FOR THE COLLAPSE ASSEMBLY.**

The switching machinery (`SwitchingCounting`) operates on **DNF terms** — a `Clause`'s literals
read as an AND (`termSat`/`evalLits`), an `anyTermSat`/`any` over terms.  The ΣΠΣ depth-3
substrate (`Depth3.Circuit`) has the *dual* polarity at the middle layer: a `Term` is an **AND
of OR-clauses** (a CNF).  To apply switching to collapse the bottom of a ΣΠΣ circuit, one
negates: by De Morgan a middle `Term` (CNF) is the negation of a **DNF** whose terms are the
negated clauses — exactly the object the switching count handles.

This file builds that adapter cleanly:

* `litNeg` — literal negation, with `litNeg_eval : (litNeg ℓ).eval x = !(ℓ.eval x)` and
  `litVar_litNeg` (variable preserved, so the switching width/star structure is unchanged);
* `evalLits_map_litNeg` / `clauseEval_neg` — negating an OR-clause yields an AND-monomial:
  `evalLits (C.lits.map litNeg) x = !(C.eval x)`;
* `termEval_neg` — **the adapter**: a ΣΠΣ middle `Term` (CNF) negates to a DNF,
  `!(T.eval x) = (T.clauses.map (fun C => C.lits.map litNeg)).any (fun t => evalLits t x)`.

It does **not** discharge the collapse assembly (good restriction ⟹ short `LDeriv` refutation)
— that is the open gate.  It supplies the polarity bridge that assembly will need.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting Rung4DNFTerm

variable {n : ℕ}

/-- Literal negation: `pos ↔ neg` on the same variable. -/
def litNeg : Rung4Literal n → Rung4Literal n
  | .pos i => .neg i
  | .neg i => .pos i

@[simp] theorem litNeg_eval (ℓ : Rung4Literal n) (x : Fin n → Bool) :
    (litNeg ℓ).eval x = !(ℓ.eval x) := by
  cases ℓ <;> simp [litNeg, Rung4Literal.eval]

@[simp] theorem litVar_litNeg (ℓ : Rung4Literal n) : litVar (litNeg ℓ) = litVar ℓ := by
  cases ℓ <;> rfl

/-- **De Morgan at the clause level.**  Negating an OR-clause's literals and reading them as an
AND-monomial computes the negation of the clause: `evalLits (map litNeg C.lits) = !(OR C.lits)`. -/
theorem evalLits_map_litNeg (lits : List (Rung4Literal n)) (x : Fin n → Bool) :
    evalLits (lits.map litNeg) x = !(lits.any (fun ℓ => ℓ.eval x)) := by
  induction lits with
  | nil => simp [evalLits]
  | cons ℓ rest ih =>
    simp only [List.map_cons, evalLits, litNeg_eval, ih, List.any_cons, Bool.not_or]

/-- The clause-level adapter in `Clause.eval` terms: `!(C.eval x) = evalLits (map litNeg C.lits) x`. -/
theorem clauseEval_neg (C : Clause n) (x : Fin n → Bool) :
    evalLits (C.lits.map litNeg) x = !(C.eval x) := by
  rw [Clause.eval, evalLits_map_litNeg]

/-- De Morgan over a list: `!(all p) = any (negation)`, transported through a map. -/
theorem not_all_eq_any_map {α β : Type*} (l : List α) (p : α → Bool) (f : α → β) (g : β → Bool)
    (h : ∀ a, (!p a) = g (f a)) : (!l.all p) = (l.map f).any g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.all_cons, Bool.not_and, h a, ih, List.map_cons, List.any_cons]

/-- **The OR/AND adapter.**  A ΣΠΣ middle `Term` (AND of OR-clauses, a CNF) negates to a DNF
whose terms are the negated clauses (each an AND-monomial) — the exact object the switching
count consumes.  Variables are preserved (`litVar_litNeg`), so the bottom width is unchanged. -/
theorem termEval_neg (T : Term n) (x : Fin n → Bool) :
    (!T.eval x) = (T.clauses.map (fun C => C.lits.map litNeg)).any (fun t => evalLits t x) := by
  rw [Term.eval]
  exact not_all_eq_any_map T.clauses (fun C => C.eval x) (fun C => C.lits.map litNeg)
    (fun t => evalLits t x) (fun C => (clauseEval_neg C x).symm)

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.termEval_neg
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.clauseEval_neg
