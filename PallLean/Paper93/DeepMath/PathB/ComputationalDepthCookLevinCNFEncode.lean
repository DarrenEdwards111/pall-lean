import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinReduction

/-!
# Cook–Levin M2 — the CNF bit-encoding primitives for `ValidTrace`

The tableau encodes a computation trace as CNF over bit-variables: the `t=0` (and hard-wired input) bits are **fixed**
to known values, and the head/state at each time are **one-hot** vectors.  Per `SCOPE_COOKLEVIN.md` the *whole*
`ValidTrace`-to-CNF compiler (variable scheme + transition-window + poly emitter) is research-scale and is **not**
claimed here.  This file builds the two genuine, complete, non-circular encoding **primitives** those clauses are made
of, with full correctness against `evalFormula`:

* **Literal fixing** (`fixBits`) — unit clauses pinning chosen variables to chosen values; the init/input clauses.
* **One-hot** (`oneHot` = at-least-one ∨ at-most-one) — encodes "exactly one of these variables is true"; the head
  and state encodings.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinCNFEncode

open PallLean.Paper93.DeepMath.PathB.CookLevinReduction

/-! ## Literal fixing — the init / hard-wired clauses -/

/-- Fix each listed variable to its listed value, as a conjunction of unit clauses. -/
def fixBits (fixes : List (ℕ × Bool)) : Formula := fixes.map (fun p => [p])

/-- **Fixing is correct.**  A CNF of unit clauses is satisfied by `a` iff `a` assigns every listed variable its
listed value — exactly the constraint the tableau's init (and hard-wired input) bits impose. -/
theorem fixBits_iff (a : ℕ → Bool) (fixes : List (ℕ × Bool)) :
    evalFormula a (fixBits fixes) = true ↔ ∀ p ∈ fixes, a p.1 = p.2 := by
  induction fixes with
  | nil => simp [fixBits, evalFormula]
  | cons p fixes ih =>
    simp only [fixBits, List.map_cons, evalFormula, List.all_cons, Bool.and_eq_true, evalClause,
      List.any_cons, List.any_nil, Bool.or_false, evalLit, beq_iff_eq, List.mem_cons, forall_eq_or_imp]
    rw [show (fixes.map fun p => [p]) = fixBits fixes from rfl, ← evalFormula, ih]

/-! ## One-hot — the head / state clauses -/

/-- At-least-one: the disjunction `⋁ vars`. -/
def atLeastOne (vars : List ℕ) : Clause := vars.map (fun v => (v, true))

/-- At-most-one: for each earlier/later pair, the clause `¬vᵢ ∨ ¬vⱼ`. -/
def atMostOne : List ℕ → Formula
  | [] => []
  | v :: vs => vs.map (fun w => [(v, false), (w, false)]) ++ atMostOne vs

/-- One-hot: exactly one of `vars` is true. -/
def oneHot (vars : List ℕ) : Formula := atLeastOne vars :: atMostOne vars

/-- **At-least-one is correct.** -/
theorem atLeastOne_iff (a : ℕ → Bool) (vars : List ℕ) :
    evalClause a (atLeastOne vars) = true ↔ ∃ v ∈ vars, a v = true := by
  simp [atLeastOne, evalClause, List.any_map, evalLit]

/-- `evalFormula` on a cons: head clause AND rest. -/
theorem evalFormula_cons (a : ℕ → Bool) (c : Clause) (φ : Formula) :
    evalFormula a (c :: φ) = (evalClause a c && evalFormula a φ) := by
  simp only [evalFormula, List.all_cons]

/-- `evalFormula` distributes over clause-list append. -/
theorem evalFormula_append (a : ℕ → Bool) (φ ψ : Formula) :
    evalFormula a (φ ++ ψ) = (evalFormula a φ && evalFormula a ψ) := by
  simp only [evalFormula, List.all_append]

/-- The pairwise-with-`v` clause block holds iff `v` and each `w` are not both true. -/
theorem evalFormula_map_pair (a : ℕ → Bool) (v : ℕ) (vs : List ℕ) :
    evalFormula a (vs.map (fun w => [(v, false), (w, false)])) = true
      ↔ ∀ w ∈ vs, a v = false ∨ a w = false := by
  induction vs with
  | nil => simp [evalFormula]
  | cons w ws ih =>
    rw [List.map_cons, evalFormula_cons, Bool.and_eq_true, ih]
    simp [evalClause, evalLit, List.forall_mem_cons]

/-- **At-most-one is correct.**  The pairwise `¬vᵢ ∨ ¬vⱼ` clauses hold iff no two listed variables are both true. -/
theorem atMostOne_iff (a : ℕ → Bool) (vars : List ℕ) :
    evalFormula a (atMostOne vars) = true ↔ vars.Pairwise (fun v w => a v = false ∨ a w = false) := by
  induction vars with
  | nil => simp [atMostOne, evalFormula]
  | cons v vs ih =>
    rw [atMostOne, evalFormula_append, Bool.and_eq_true, evalFormula_map_pair, ih, List.pairwise_cons]

/-- **One-hot is correct.**  `a` satisfies `oneHot vars` iff at least one listed variable is true *and* no two are
both true — i.e. exactly one is true.  This is precisely the head/state vector constraint of the tableau. -/
theorem oneHot_iff (a : ℕ → Bool) (vars : List ℕ) :
    evalFormula a (oneHot vars) = true ↔
      (∃ v ∈ vars, a v = true) ∧ vars.Pairwise (fun v w => a v = false ∨ a w = false) := by
  rw [oneHot, evalFormula_cons, Bool.and_eq_true, atLeastOne_iff, atMostOne_iff]

end PallLean.Paper93.DeepMath.PathB.CookLevinCNFEncode
