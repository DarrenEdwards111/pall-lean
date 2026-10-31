import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DepthReduction

/-!
# Block-DT model, foundation 15: iterated depth reduction over a real circuit datatype (branch only)

We package the depth-reduction step (bricks 14–15) on an explicit alternating AC⁰-style circuit
datatype `Circ` (unbounded fan-in `and`/`or` over literals).  Two ingredients drive the iteration:

* the **swap** turns a shallow bottom gate (a `DTree`) into a depth-2 bounded-width CNF circuit
  (`DTree.toCirc`, `toCirc_eval`, `toCirc_clause_width`); and
* the **associativity collapse** `bigAnd_flatten_eval` / `bigOr_flatten_eval` merges a whole layer of
  same-type gates into one (`AND`-of-`AND`s / `OR`-of-`OR`s flattens), removing an alternation level.

Running them in alternation is one full switching round; iterating drives `depth d → d-1` over a real
circuit.  This is the AC⁰ depth-reduction engine in datatype form.

* `Circ`, `Circ.eval`, `Circ.height` — alternating circuit, Boolean semantics, alternation-level count.
* `eval_and_iff` / `eval_or_iff` — the gate semantics as `∀`/`∃` over children.
* `bigAnd_flatten_eval` / `bigOr_flatten_eval` — the iterated (whole-layer) same-type collapse.
* `DTree.toCirc` / `toCirc_eval` / `toCirc_clause_width` — shallow DT ↦ depth-2 width-bounded CNF circuit.

Clean, no `sorry`, no `native_decide`.  AC⁰/depth-3; not P≠NP-strength (AC⁰ ceiling).
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

/-- An alternating AC⁰-style circuit over `n` Boolean variables: literals, unbounded fan-in `and`,
unbounded fan-in `or`. -/
inductive Circ (n : ℕ) where
  | lit : Fin n → Bool → Circ n
  | and : List (Circ n) → Circ n
  | or : List (Circ n) → Circ n

namespace Circ

variable {n : ℕ}

mutual
/-- Evaluate a circuit at an assignment (mutual structural recursion via the list helpers). -/
def eval (x : Fin n → Bool) : Circ n → Bool
  | lit v b => decide (x v = b)
  | and cs => evalAll x cs
  | or cs => evalAny x cs
/-- `AND` over a child list. -/
def evalAll (x : Fin n → Bool) : List (Circ n) → Bool
  | [] => true
  | c :: cs => eval x c && evalAll x cs
/-- `OR` over a child list. -/
def evalAny (x : Fin n → Bool) : List (Circ n) → Bool
  | [] => false
  | c :: cs => eval x c || evalAny x cs
end

mutual
/-- The alternation-level count: literals are `0`, each gate adds one above its deepest child. -/
def height : Circ n → ℕ
  | lit _ _ => 0
  | and cs => heightList cs + 1
  | or cs => heightList cs + 1
/-- Max height over a child list. -/
def heightList : List (Circ n) → ℕ
  | [] => 0
  | c :: cs => max (height c) (heightList cs)
end

/-- `heightList` is bounded by any upper bound of the children's heights. -/
theorem heightList_le : ∀ (l : List (Circ n)) (b : ℕ), (∀ c ∈ l, height c ≤ b) → heightList l ≤ b := by
  intro l b
  induction l with
  | nil => intro _; exact Nat.zero_le b
  | cons c cs ih =>
    intro h
    exact max_le (h c (List.mem_cons_self ..)) (ih (fun x hx => h x (List.mem_cons_of_mem _ hx)))

theorem evalAll_iff (x : Fin n → Bool) (cs : List (Circ n)) :
    evalAll x cs = true ↔ ∀ c ∈ cs, eval x c = true := by
  induction cs with
  | nil => simp [evalAll]
  | cons c cs ih => simp [evalAll, Bool.and_eq_true, ih]

theorem evalAny_iff (x : Fin n → Bool) (cs : List (Circ n)) :
    evalAny x cs = true ↔ ∃ c ∈ cs, eval x c = true := by
  induction cs with
  | nil => simp [evalAny]
  | cons c cs ih => simp [evalAny, Bool.or_eq_true, ih]

/-- **`AND` semantics.**  An `and`-gate accepts iff every child does. -/
theorem eval_and_iff (x : Fin n → Bool) (cs : List (Circ n)) :
    eval x (and cs) = true ↔ ∀ c ∈ cs, eval x c = true := by
  rw [show eval x (and cs) = evalAll x cs from rfl]; exact evalAll_iff x cs

/-- **`OR` semantics.**  An `or`-gate accepts iff some child does. -/
theorem eval_or_iff (x : Fin n → Bool) (cs : List (Circ n)) :
    eval x (or cs) = true ↔ ∃ c ∈ cs, eval x c = true := by
  rw [show eval x (or cs) = evalAny x cs from rfl]; exact evalAny_iff x cs

/-! ### Iterated same-type collapse (the associativity engine) -/

/-- **`AND`-of-`AND`s flattens (whole layer).**  A top `AND` over a layer of `AND`-gates equals one
`AND` over the concatenated children — an alternation level removed. -/
theorem bigAnd_flatten_eval (css : List (List (Circ n))) (x : Fin n → Bool) :
    eval x (and (css.map and)) = true ↔ eval x (and css.flatten) = true := by
  rw [eval_and_iff, eval_and_iff]
  constructor
  · intro h c hc
    rw [List.mem_flatten] at hc
    obtain ⟨ds, hds, hcd⟩ := hc
    have hand := h (and ds) (List.mem_map.mpr ⟨ds, hds, rfl⟩)
    rw [eval_and_iff] at hand
    exact hand c hcd
  · intro h c hc
    rw [List.mem_map] at hc
    obtain ⟨ds, hds, rfl⟩ := hc
    rw [eval_and_iff]
    intro c' hc'
    exact h c' (List.mem_flatten.mpr ⟨ds, hds, hc'⟩)

/-- **`OR`-of-`OR`s flattens (whole layer).**  Dual of `bigAnd_flatten_eval`. -/
theorem bigOr_flatten_eval (css : List (List (Circ n))) (x : Fin n → Bool) :
    eval x (or (css.map or)) = true ↔ eval x (or css.flatten) = true := by
  rw [eval_or_iff, eval_or_iff]
  constructor
  · rintro ⟨c, hc, hev⟩
    rw [List.mem_map] at hc
    obtain ⟨ds, hds, rfl⟩ := hc
    rw [eval_or_iff] at hev
    obtain ⟨c', hc', hev'⟩ := hev
    exact ⟨c', List.mem_flatten.mpr ⟨ds, hds, hc'⟩, hev'⟩
  · rintro ⟨c, hc, hev⟩
    rw [List.mem_flatten] at hc
    obtain ⟨ds, hds, hcd⟩ := hc
    refine ⟨or ds, List.mem_map.mpr ⟨ds, hds, rfl⟩, ?_⟩
    rw [eval_or_iff]
    exact ⟨c, hcd, hev⟩

end Circ

/-! ### The swap as a datatype bridge: a shallow DT becomes a depth-2 width-bounded CNF circuit -/

namespace DTree

variable {n : ℕ}

/-- Convert a decision tree to its rejecting-path **CNF circuit**: an `AND` of clauses, each an `OR` of
literals.  Depth 2; bottom fan-in (clause width) `≤ depth`. -/
def toCirc (t : DTree n) : Circ n :=
  Circ.and (t.toCNF.map (fun c => Circ.or (c.map (fun p => Circ.lit p.1 p.2))))

/-- **The swap, on circuits.**  `toCirc` preserves the computed function. -/
theorem toCirc_eval (t : DTree n) (x : Fin n → Bool) :
    Circ.eval x t.toCirc = true ↔ t.eval x = true := by
  rw [toCirc, Circ.eval_and_iff, eval_eq_cnf t x]
  constructor
  · intro h c hc
    have hor := h (Circ.or (c.map (fun p => Circ.lit p.1 p.2))) (List.mem_map.mpr ⟨c, hc, rfl⟩)
    rw [Circ.eval_or_iff] at hor
    obtain ⟨b, hb, hev⟩ := hor
    rw [List.mem_map] at hb
    obtain ⟨p, hp, rfl⟩ := hb
    exact ⟨p, hp, of_decide_eq_true hev⟩
  · intro h c' hc'
    rw [List.mem_map] at hc'
    obtain ⟨c, hc, rfl⟩ := hc'
    rw [Circ.eval_or_iff]
    obtain ⟨p, hp, hpx⟩ := h c hc
    exact ⟨Circ.lit p.1 p.2, List.mem_map.mpr ⟨p, hp, rfl⟩, decide_eq_true hpx⟩

/-- **Bottom-fan-in bound for the CNF circuit.**  Each `OR`-clause of `toCirc` has fan-in `≤ depth`. -/
theorem toCirc_clause_width (t : DTree n) :
    ∀ c ∈ t.toCNF, (c.map (fun p => Circ.lit p.1 p.2)).length ≤ t.depth := by
  intro c hc
  rw [List.length_map]
  exact toCNF_width t c hc

end DTree

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.Circ.bigAnd_flatten_eval
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.Circ.bigOr_flatten_eval
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.DTree.toCirc_eval
