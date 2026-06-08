import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DTreeToCNF

/-!
# AC⁰ reduction, foundation 3: the AC⁰ circuit substrate (branch only)

The object the multi-round collapse recurses on: a depth-`d` unbounded-fan-in alternating circuit — an
`OR`/`AND` tree over literals.

* `ACircuit` — literal / OR-of-subcircuits / AND-of-subcircuits.
* `ACircuit.eval` — Boolean semantics (`OR` = some child true, `AND` = all children true).
* `ACircuit.depth` — the gate (alternation) depth (`0` at a literal).
* `ACircuit.bottomWidth` — the fan-in just above the literals (the width the switching lemma acts on).

The collapse plan (next bricks): a bottom `OR`-of-`AND`s (width-`w` DNF) switches to a shallow decision
tree, which `dtreeToCNF` (brick 67) rewrites as a width-`≤ s` CNF; that `AND`-of-`OR`s merges with the
`AND` layer above, dropping `depth` by one — down to the depth-2 parity bound (brick 35).

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- A depth-`d` unbounded-fan-in alternating circuit: literal, `OR` of subcircuits, or `AND` of
subcircuits. -/
inductive ACircuit (n : ℕ) where
  | lit : Rung4Literal n → ACircuit n
  | or : List (ACircuit n) → ACircuit n
  | and : List (ACircuit n) → ACircuit n

namespace ACircuit

mutual
/-- Boolean evaluation: `OR` = some child true, `AND` = all children true (mutual with `evalAny`/`evalAll`
to recurse through the children). -/
def eval : ACircuit n → (Fin n → Bool) → Bool
  | lit ℓ, x => ℓ.eval x
  | or cs, x => evalAny cs x
  | and cs, x => evalAll cs x
/-- Disjunction over a child list. -/
def evalAny : List (ACircuit n) → (Fin n → Bool) → Bool
  | [], _ => false
  | c :: cs, x => eval c x || evalAny cs x
/-- Conjunction over a child list. -/
def evalAll : List (ACircuit n) → (Fin n → Bool) → Bool
  | [], _ => true
  | c :: cs, x => eval c x && evalAll cs x
end

mutual
/-- The gate (alternation) depth: `0` at a literal, `1 +` the deepest child otherwise. -/
def depth : ACircuit n → ℕ
  | lit _ => 0
  | or cs => depthList cs + 1
  | and cs => depthList cs + 1
/-- The deepest circuit in a child list. -/
def depthList : List (ACircuit n) → ℕ
  | [] => 0
  | c :: cs => max (depth c) (depthList cs)
end

mutual
/-- The bottom fan-in: the largest number of literals fed into a gate just above the leaves. -/
def bottomWidth : ACircuit n → ℕ
  | lit _ => 1
  | or cs => bottomWidthList cs
  | and cs => bottomWidthList cs
/-- The largest bottom fan-in across a child list. -/
def bottomWidthList : List (ACircuit n) → ℕ
  | [] => 0
  | c :: cs => max (bottomWidth c) (bottomWidthList cs)
end

/-- `evalAny` is the disjunction over the children. -/
theorem evalAny_eq (cs : List (ACircuit n)) (x : Fin n → Bool) :
    evalAny cs x = cs.any (fun c => eval c x) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [evalAny, List.any_cons, ih]

/-- `evalAll` is the conjunction over the children. -/
theorem evalAll_eq (cs : List (ACircuit n)) (x : Fin n → Bool) :
    evalAll cs x = cs.all (fun c => eval c x) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [evalAll, List.all_cons, ih]

@[simp] theorem eval_lit (ℓ : Rung4Literal n) (x : Fin n → Bool) : (lit ℓ).eval x = ℓ.eval x := rfl
@[simp] theorem eval_or (cs : List (ACircuit n)) (x : Fin n → Bool) :
    (or cs).eval x = cs.any (fun c => c.eval x) := by rw [eval, evalAny_eq]
@[simp] theorem eval_and (cs : List (ACircuit n)) (x : Fin n → Bool) :
    (and cs).eval x = cs.all (fun c => c.eval x) := by rw [eval, evalAll_eq]

end ACircuit

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.ACircuit.eval
