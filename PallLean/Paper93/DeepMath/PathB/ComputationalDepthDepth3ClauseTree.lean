import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CircuitRestrict

/-!
# Block-DT model, foundation 22: the term/clause → DTree bridge atom (branch only)

The model bridge between the `blockStream` switching world (clauses over `Rung4Literal`) and the
abstract `DTree` parity world.  Its atom: a single bottom **term** (conjunction of literals) compiles to
a binary decision tree of depth `≤` its width, computing the term's satisfaction.

* `termTree` — compile a list of `Rung4Literal`s (a term) to a `DTree`.
* `termTree_eval` — it computes the conjunction (`= lits.all (·.eval x)`).
* `termTree_depth` — depth `≤` width.
* `clauseTree` / `clauseTree_eval` / `clauseTree_depth` — the same wrapped for `Clause`.

## Honest scope

This is the **literal/term-level** bridge: it converts a bottom AC⁰ gate's term to a width-bounded
`DTree`, connecting the two literal representations (`Rung4Literal` ↔ `Fin n × Bool` semantics) with a
proven depth bound.  The full `blockStream` → shallow-`DTree` construction (assembling these across the
canonical block descent, with depth `≤ #blocks · width`) is the remaining piece — it is the
canonical-decision-tree depth bound, the genuinely large switching-lemma construction.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

namespace DTree

variable {n : ℕ}

/-- Compile a term (list of literals) to a decision tree: query each literal's variable; a wrong value
rejects (`leaf false`), all-correct accepts (`leaf true`). -/
def termTree : List (Rung4Literal n) → DTree n
  | [] => leaf true
  | Rung4Literal.pos i :: rest => node i (leaf false) (termTree rest)
  | Rung4Literal.neg i :: rest => node i (termTree rest) (leaf false)

/-- **`termTree` computes the conjunction.** -/
theorem termTree_eval (lits : List (Rung4Literal n)) (x : Fin n → Bool) :
    (termTree lits).eval x = lits.all (fun ℓ => Rung4Literal.eval ℓ x) := by
  induction lits with
  | nil => rfl
  | cons ℓ rest ih =>
    cases ℓ with
    | pos i =>
      simp only [termTree, eval, List.all_cons, Rung4Literal.eval, ih]
      cases x i <;> simp
    | neg i =>
      simp only [termTree, eval, List.all_cons, Rung4Literal.eval, ih]
      cases x i <;> simp

/-- **`termTree` has depth `≤` width.** -/
theorem termTree_depth (lits : List (Rung4Literal n)) :
    (termTree lits).depth ≤ lits.length := by
  induction lits with
  | nil => simp [termTree, depth]
  | cons ℓ rest ih =>
    cases ℓ with
    | pos i =>
      simp only [termTree, depth, List.length_cons, Nat.zero_max]
      omega
    | neg i =>
      simp only [termTree, depth, List.length_cons, Nat.max_zero]
      omega

/-- The decision tree of a `Clause` (a bottom term). -/
def clauseTree (C : Clause n) : DTree n := termTree C.lits

/-- **`clauseTree` computes the term.** -/
theorem clauseTree_eval (C : Clause n) (x : Fin n → Bool) :
    (clauseTree C).eval x = C.lits.all (fun ℓ => Rung4Literal.eval ℓ x) :=
  termTree_eval C.lits x

/-- **`clauseTree` has depth `≤` the clause width.** -/
theorem clauseTree_depth (C : Clause n) : (clauseTree C).depth ≤ C.lits.length :=
  termTree_depth C.lits

end DTree

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.DTree.termTree_eval
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.DTree.termTree_depth
