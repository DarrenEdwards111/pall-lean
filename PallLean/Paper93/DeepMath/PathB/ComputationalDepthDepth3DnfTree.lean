import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ClauseTree

/-!
# Block-DT model, foundation 23: DNF → DTree, increment 1 — the correct construction (branch only)

The descent assembly, step 1: every DNF (clause list) compiles to a *single* decision tree computing it,
with depth `≤` the total number of literals.  This is the structural skeleton of the canonical decision
tree; the small-depth refinement (where a good restriction prunes the descent to `≤ #blocks · width`) is
the next increment.

* `termTreeCont` — `termTree` with a **continuation**: query a term; all-true accepts, any-false falls
  through to the continuation tree `k` (this is what threads one term into the next).
* `termTreeCont_eval` — `= term-conjunction ∨ k`.
* `termTreeCont_depth` — `≤ width + depth k`.
* `dnfTree` / `dnfValue` — compile the whole DNF (fold the terms via continuations) and its semantics.
* `dnfTree_eval` — `(dnfTree cs).eval x = dnfValue cs x` (the DNF on full assignments).
* `dnfTree_depth` — `≤ Σ_T |T.lits|`, and `dnfTree_depth_le_mul` — `≤ #clauses · w` for width-`≤ w` DNF.

## Honest scope

Increment 1 gives the *correct* DNF→DTree with the *trivial* (total-literal) depth bound.  The
switching-lemma small-depth bound (`≤ #blocks · width`, with `#blocks` small after a good restriction)
is increment 2: it needs the restriction to prune falsified clauses so the realised descent is short.
Built incrementally and honestly; no `sorry`.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

namespace DTree

variable {n : ℕ}

/-- `termTree` with a continuation: query the term; all-true accepts (`leaf true`), any-false falls
through to `k`. -/
def termTreeCont : List (Rung4Literal n) → DTree n → DTree n
  | [], _ => leaf true
  | Rung4Literal.pos i :: rest, k => node i k (termTreeCont rest k)
  | Rung4Literal.neg i :: rest, k => node i (termTreeCont rest k) k

/-- **`termTreeCont` computes term-conjunction `∨` continuation.** -/
theorem termTreeCont_eval (lits : List (Rung4Literal n)) (k : DTree n) (x : Fin n → Bool) :
    (termTreeCont lits k).eval x
      = (lits.all (fun ℓ => Rung4Literal.eval ℓ x) || k.eval x) := by
  induction lits with
  | nil => simp [termTreeCont, eval]
  | cons ℓ rest ih =>
    cases ℓ with
    | pos i =>
      simp only [termTreeCont, eval, List.all_cons, Rung4Literal.eval, ih]
      cases x i <;> simp
    | neg i =>
      simp only [termTreeCont, eval, List.all_cons, Rung4Literal.eval, ih]
      cases x i <;> simp

/-- **`termTreeCont` depth `≤` width `+` continuation depth.** -/
theorem termTreeCont_depth (lits : List (Rung4Literal n)) (k : DTree n) :
    (termTreeCont lits k).depth ≤ lits.length + k.depth := by
  induction lits with
  | nil => simp [termTreeCont, depth]
  | cons ℓ rest ih =>
    cases ℓ with
    | pos i =>
      simp only [termTreeCont, depth, List.length_cons]
      rcases Nat.le_total (depth k) (depth (termTreeCont rest k)) with hle | hle
      · rw [Nat.max_eq_right hle]; omega
      · rw [Nat.max_eq_left hle]; omega
    | neg i =>
      simp only [termTreeCont, depth, List.length_cons]
      rcases Nat.le_total (depth (termTreeCont rest k)) (depth k) with hle | hle
      · rw [Nat.max_eq_right hle]; omega
      · rw [Nat.max_eq_left hle]; omega

/-- The DNF on full assignments: some term has all literals true. -/
def dnfValue (cs : List (Clause n)) (x : Fin n → Bool) : Bool :=
  cs.any (fun T => T.lits.all (fun ℓ => Rung4Literal.eval ℓ x))

/-- Compile a DNF to a single decision tree: fold the terms via continuations. -/
def dnfTree : List (Clause n) → DTree n
  | [] => leaf false
  | T :: rest => termTreeCont T.lits (dnfTree rest)

/-- **`dnfTree` computes the DNF.** -/
theorem dnfTree_eval (cs : List (Clause n)) (x : Fin n → Bool) :
    (dnfTree cs).eval x = dnfValue cs x := by
  induction cs with
  | nil => rfl
  | cons T rest ih =>
    show (termTreeCont T.lits (dnfTree rest)).eval x = _
    rw [termTreeCont_eval, ih]
    simp [dnfValue, List.any_cons]

/-- **`dnfTree` depth `≤` total literal count.** -/
theorem dnfTree_depth (cs : List (Clause n)) :
    (dnfTree cs).depth ≤ (cs.map (fun T => T.lits.length)).sum := by
  induction cs with
  | nil => simp [dnfTree, depth]
  | cons T rest ih =>
    have h := termTreeCont_depth T.lits (dnfTree rest)
    simp only [dnfTree, List.map_cons, List.sum_cons]
    omega

/-- **`dnfTree` depth `≤ #clauses · w`** for a width-`≤ w` DNF. -/
theorem dnfTree_depth_le_mul (cs : List (Clause n)) (w : ℕ)
    (hw : ∀ T ∈ cs, T.lits.length ≤ w) :
    (dnfTree cs).depth ≤ cs.length * w := by
  refine le_trans (dnfTree_depth cs) ?_
  calc (cs.map (fun T => T.lits.length)).sum
      ≤ (cs.map (fun _ => w)).sum := by
        apply List.sum_le_sum
        intro a ha
        exact hw a ha
    _ = cs.length * w := by rw [List.map_const', List.sum_replicate, smul_eq_mul]

/-- **Depth-2 parity lower bound (a genuine, complete consequence).**  A width-`≤ w` DNF computing
parity needs `≥ n/w` terms: `n ≤ #clauses · w`.  This is the base case of the AC⁰ hierarchy, fully
proved: `dnfTree` computes the DNF (`dnfTree_eval`), so it computes parity, so it has depth `≥ n`
(`parity_needs_full_depth`), but its depth is `≤ #clauses · w` (`dnfTree_depth_le_mul`). -/
theorem dnf_parity_size_bound (cs : List (Clause n)) (w : ℕ)
    (hw : ∀ T ∈ cs, T.lits.length ≤ w)
    (hpar : ∀ x, dnfValue cs x = parity x) :
    n ≤ cs.length * w := by
  have hcomp : ∀ x, (dnfTree cs).eval x = parity x :=
    fun x => (dnfTree_eval cs x).trans (hpar x)
  have h1 := parity_needs_full_depth (dnfTree cs) hcomp
  have h2 := dnfTree_depth_le_mul cs w hw
  omega

end DTree

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.DTree.dnfTree_eval
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.DTree.dnfTree_depth_le_mul
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.DTree.dnf_parity_size_bound
