import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameMagnitude

/-!
# N-Frame: the boundary transducer — the real cubic-graph boundary invariant (not a degree shadow)

The earlier candidates (raw N-Frame degree, SPDP rank, sensitivity, MCSP) were the *formalisable* simplifications, but they
collapsed book1's boundary idea into truth-table/degree proxies.  This file builds the **real** minimal object book1 asks
for: a finite observer as a **bounded-degree ("cubic") boundary graph** — a transducer with fan-in `≤ 2` nodes — whose
**thermodynamic budget** is its *graph volume* (node count `×` unit local cost).  A function is observer-realisable when a
bounded-degree transducer computes it; the invariant is the minimum budget.

  `Trans` — a bounded-degree boundary graph (var / const / unary / binary nodes, each degree `≤ 3`).
  `eval` / `volume` — the transducer semantics and its graph volume (thermodynamic budget).
  `budget f` — the least volume over transducers computing `f`.

**The easy tests (all PROVED) — and why this is not a degree shadow:**
  `budget_const_le` / `budget_var_le` — constants and variables cost `1` (a single boundary node).
  `budget_bin_le` — **composition preserves budget additively**: `budget (op ∘ (f,g)) ≤ budget f + budget g + 1`.  The
        boundary class is closed under bounded-degree composition — the structural handle degree/sensitivity lacked, and
        the reason `P`-style composed computations stay within a polynomial budget.
  `budget_fullAnd_le` — the full-AND has budget `≤ 2n+1` (**linear**).  Yet its unique multilinear representation has raw
        degree `n` (the *maximum*, `nframeComplexity_sqfEval_univ_eq`).  So **high raw degree no longer implies high boundary
        cost** — the inversion that killed raw degree is *corrected* by the graph-volume budget, honestly and by
        construction, not by a truth-table trick.

## Honest scope — the right object; capture is free, the gap is the real mountain

Graph volume is (a minimal form of) *circuit size / graph complexity*, not polynomial degree — so this route has a very
different, and more honest, status than the proxies:

* **Capture is free, not assumed.**  `P/poly` *is* "polynomial boundary budget" by definition.  Unlike the raw-degree
  bridge (assumed/false) or MCSP (circular), here the capture direction needs no hypothesis — it is definitional.
* **The gap is the real mountain.**  The remaining step is a *super-polynomial budget (graph-volume / circuit) lower
  bound* for an `NP`/`VNP` target under all bounded-degree boundary embeddings.  That is a genuine circuit lower bound —
  the actual hard problem, now faced with the correct object rather than a shadow of it, with *no* assumed bridge and *no*
  circular proxy.

So this is the right *class* of invariant, its sanity tests pass, and it reduces `P vs NP` to exactly a boundary-volume
lower bound.  It does **not** prove that lower bound (geometry refinements — treewidth / spectral dimension / curvature /
CEW–SPDP tearing pressure — are the next layer of the boundary structure, and the super-polynomial gap is unproved).
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

variable {n : ℕ}

/-- A **bounded-degree ("cubic") boundary graph** / transducer: input, constant, unary and binary nodes (fan-in `≤ 2`,
so each node has degree `≤ 3`). -/
inductive Trans (n : ℕ) where
  | var : Fin n → Trans n
  | cst : Bool → Trans n
  | un : (Bool → Bool) → Trans n → Trans n
  | bin : (Bool → Bool → Bool) → Trans n → Trans n → Trans n

/-- The transducer's computed function. -/
def eval : Trans n → (Fin n → Bool) → Bool
  | .var i, x => x i
  | .cst b, _ => b
  | .un op t, x => op (eval t x)
  | .bin op t₁ t₂, x => op (eval t₁ x) (eval t₂ x)

/-- The **graph volume** = node count = thermodynamic budget (unit local cost). -/
def volume : Trans n → ℕ
  | .var _ => 1
  | .cst _ => 1
  | .un _ t => volume t + 1
  | .bin _ t₁ t₂ => volume t₁ + volume t₂ + 1

/-- The **minimum boundary budget** of `f`: the least graph volume over transducers computing `f`. -/
noncomputable def budget (f : (Fin n → Bool) → Bool) : ℕ :=
  sInf {v | ∃ t : Trans n, eval t = f ∧ volume t = v}

/-! ### Easy tests -/

/-- **Constants cost one node (proved).** -/
theorem budget_const_le (b : Bool) : budget (fun _ : Fin n → Bool => b) ≤ 1 :=
  Nat.sInf_le ⟨Trans.cst b, rfl, rfl⟩

/-- **Variables cost one node (proved).** -/
theorem budget_var_le (i : Fin n) : budget (fun x : Fin n → Bool => x i) ≤ 1 :=
  Nat.sInf_le ⟨Trans.var i, rfl, rfl⟩

/-- **Composition preserves budget additively (proved).**  Combining two realisable sub-computations by a bounded-degree
gate costs at most the sum of their budgets plus one node.  The boundary class is closed under bounded-degree
composition. -/
theorem budget_bin_le (op : Bool → Bool → Bool) (f g : (Fin n → Bool) → Bool)
    (hf : ∃ t : Trans n, eval t = f) (hg : ∃ t : Trans n, eval t = g) :
    budget (fun x => op (f x) (g x)) ≤ budget f + budget g + 1 := by
  have hnf : {v | ∃ t : Trans n, eval t = f ∧ volume t = v}.Nonempty := by
    obtain ⟨t, ht⟩ := hf; exact ⟨volume t, t, ht, rfl⟩
  have hng : {v | ∃ t : Trans n, eval t = g ∧ volume t = v}.Nonempty := by
    obtain ⟨t, ht⟩ := hg; exact ⟨volume t, t, ht, rfl⟩
  obtain ⟨tf, hef, hvf⟩ := Nat.sInf_mem hnf
  obtain ⟨tg, heg, hvg⟩ := Nat.sInf_mem hng
  refine Nat.sInf_le ⟨Trans.bin op tf tg, ?_, ?_⟩
  · funext x; simp only [eval]; rw [hef, heg]
  · simp only [volume, budget]; rw [hvf, hvg]

/-- The full-AND transducer over a list of variables: a right-folded chain of binary AND nodes. -/
def andVars : List (Fin n) → Trans n
  | [] => Trans.cst true
  | i :: is => Trans.bin (· && ·) (Trans.var i) (andVars is)

theorem eval_andVars (is : List (Fin n)) (x : Fin n → Bool) :
    eval (andVars is) x = is.foldr (fun i acc => x i && acc) true := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [andVars, eval, ih]

theorem volume_andVars (is : List (Fin n)) : volume (andVars is) = 2 * is.length + 1 := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [andVars, volume, ih, List.length_cons]; ring

/-- The full-AND function `∏ᵢ xᵢ` as a Boolean transduction. -/
def fullAndFn (n : ℕ) : (Fin n → Bool) → Bool :=
  fun x => (List.finRange n).foldr (fun i acc => x i && acc) true

/-- **The full-AND has linear budget (proved).**  Its boundary budget is `≤ 2n+1` — yet its multilinear degree is the
maximal `n` (`nframeComplexity_sqfEval_univ_eq`).  High raw degree does **not** force high boundary cost: the graph-volume
budget corrects the raw-degree inversion. -/
theorem budget_fullAnd_le : budget (fullAndFn n) ≤ 2 * n + 1 := by
  refine Nat.sInf_le ⟨andVars (List.finRange n), ?_, ?_⟩
  · funext x; rw [eval_andVars]; rfl
  · rw [volume_andVars, List.length_finRange]

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.budget_bin_le
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.budget_fullAnd_le
