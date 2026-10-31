import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSymAnd
import Mathlib

/-!
# The ACC⁰ circuit model (PROVED) — tying the AND / OR / MOD gates together

`ACC⁰` is the class of Boolean functions computed by **constant-depth, polynomial-size** circuits over
unbounded-fan-in `AND`, `OR`, `NOT`, and `MOD_m` gates.  This file gives a clean inductive model of such
circuits and its semantics (`eval`), depth, and size, unifying the gate types studied in the polynomial-method
files (`AND` as a product, `MOD_p` as an `𝔽_p`-polynomial).

  `Circuit n` — an ACC⁰ circuit over `n` Boolean inputs (`var`/`const`/`not`/`and`/`or`/`mod`).
  `eval`, `depth`, `size` — its semantics and the two complexity measures.
  Basic semantic lemmas (`eval_*`) and the `ACC⁰`-class shape.

This is the *model*; the deep theorems about it — the Razborov–Smolensky lower bound (`MOD_q ∉ AC⁰[p]`) and the
Beigel–Tarui `SYM∘AND` normal form — remain genuine targets / cited axioms.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0

/-- An ACC⁰ circuit over `n` Boolean inputs: inputs, constants, `NOT`, and unbounded-fan-in `AND`, `OR`, and
`MOD_m` gates (a `MOD_m` gate fires iff the number of true children is `≡ 0 (mod m)`). -/
inductive Circuit (n : ℕ) where
  | var : Fin n → Circuit n
  | const : Bool → Circuit n
  | not : Circuit n → Circuit n
  | and : List (Circuit n) → Circuit n
  | or : List (Circuit n) → Circuit n
  | mod : ℕ → List (Circuit n) → Circuit n

namespace Circuit

variable {n : ℕ}

mutual
/-- The Boolean value computed by a circuit on an input.  Defined by mutual structural recursion with a list
helper (`evalList` maps the children), so the recursion over the unbounded-fan-in child lists is structural. -/
def eval (x : Fin n → Bool) : Circuit n → Bool
  | var i => x i
  | const b => b
  | not c => !(eval x c)
  | and cs => (evalList x cs).all id
  | or cs => (evalList x cs).any id
  | mod m cs => decide ((evalList x cs).countP id % m = 0)
def evalList (x : Fin n → Bool) : List (Circuit n) → List Bool
  | [] => []
  | c :: cs => eval x c :: evalList x cs
end

/-- The child-evaluation helper is exactly `map eval`. -/
theorem evalList_eq_map (x : Fin n → Bool) (cs : List (Circuit n)) :
    evalList x cs = cs.map (eval x) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [evalList, ih]

@[simp] theorem eval_var (x : Fin n → Bool) (i : Fin n) : eval x (var i) = x i := by rw [eval]
@[simp] theorem eval_const (x : Fin n → Bool) (b : Bool) : eval x (const b) = b := by rw [eval]
@[simp] theorem eval_not (x : Fin n → Bool) (c : Circuit n) : eval x (not c) = !(eval x c) := by rw [eval]

@[simp] theorem eval_and (x : Fin n → Bool) (cs : List (Circuit n)) :
    eval x (and cs) = cs.all (eval x) := by
  rw [eval, evalList_eq_map, List.all_map]; rfl
@[simp] theorem eval_or (x : Fin n → Bool) (cs : List (Circuit n)) :
    eval x (or cs) = cs.any (eval x) := by
  rw [eval, evalList_eq_map, List.any_map]; rfl
@[simp] theorem eval_mod (x : Fin n → Bool) (m : ℕ) (cs : List (Circuit n)) :
    eval x (mod m cs) = decide (cs.countP (eval x) % m = 0) := by
  rw [eval, evalList_eq_map, List.countP_map]; rfl

mutual
/-- The depth of a circuit (longest gate path to an input). -/
def depth : Circuit n → ℕ
  | var _ => 0
  | const _ => 0
  | not c => depth c + 1
  | and cs => depthList cs + 1
  | or cs => depthList cs + 1
  | mod _ cs => depthList cs + 1
def depthList : List (Circuit n) → ℕ
  | [] => 0
  | c :: cs => max (depth c) (depthList cs)
end

mutual
/-- The size of a circuit (number of gates / nodes). -/
def size : Circuit n → ℕ
  | var _ => 1
  | const _ => 1
  | not c => size c + 1
  | and cs => sizeList cs + 1
  | or cs => sizeList cs + 1
  | mod _ cs => sizeList cs + 1
def sizeList : List (Circuit n) → ℕ
  | [] => 0
  | c :: cs => size c + sizeList cs
end

/-- An `AND` of no children is `true` (the empty conjunction). -/
@[simp] theorem eval_and_nil (x : Fin n → Bool) : eval x (and []) = true := by simp
/-- An `OR` of no children is `false` (the empty disjunction). -/
@[simp] theorem eval_or_nil (x : Fin n → Bool) : eval x (or []) = false := by simp

/-- An `AND` is true iff every child is true. -/
theorem eval_and_iff (x : Fin n → Bool) (cs : List (Circuit n)) :
    eval x (and cs) = true ↔ ∀ c ∈ cs, eval x c = true := by
  simp [List.all_eq_true]

/-- An `OR` is true iff some child is true. -/
theorem eval_or_iff (x : Fin n → Bool) (cs : List (Circuit n)) :
    eval x (or cs) = true ↔ ∃ c ∈ cs, eval x c = true := by
  simp [List.any_eq_true]

/-- A `MOD_m` gate fires iff the number of its true children is divisible by `m`. -/
theorem eval_mod_iff (x : Fin n → Bool) (m : ℕ) (cs : List (Circuit n)) :
    eval x (mod m cs) = true ↔ cs.countP (eval x) % m = 0 := by
  simp

end Circuit

/-- The shape of the `ACC⁰` class: a Boolean function `f` is computed by a circuit of the given depth and size
bounds.  (The class `ACC⁰` proper bounds depth by a constant and size by a polynomial in `n`, across a family;
this is the per-circuit realisation predicate.) -/
def ComputesWithin (n : ℕ) (f : (Fin n → Bool) → Bool) (d s : ℕ) : Prop :=
  ∃ C : Circuit n, C.depth ≤ d ∧ C.size ≤ s ∧ ∀ x, C.eval x = f x

/-- Every circuit computes *some* function within its own depth and size. -/
theorem Circuit.computes (C : Circuit n) : ComputesWithin n C.eval C.depth C.size :=
  ⟨C, le_refl _, le_refl _, fun _ => rfl⟩

end PallLean.Paper93.DeepMath.PathB.ACC0

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0.Circuit.eval_and_iff
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0.Circuit.eval_mod_iff
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0.Circuit.computes
