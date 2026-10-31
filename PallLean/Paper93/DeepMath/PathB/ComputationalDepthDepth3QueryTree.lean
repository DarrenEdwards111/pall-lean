import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DnfRestrict

/-!
# Block-DT model, foundation 25: the per-block query subtree (increment 3, step 1) (branch only)

The adaptive canonical decision tree of the switching lemma queries, at each block, *all* the free
variables of the active term, branching into a different continuation per leaf assignment.  This module
builds that per-block query mechanism and proves its two essential properties.

* `queryAll` — a complete binary decision tree querying a list of variables, threading each leaf's
  assignment into the continuation `k`.
* `queryAll_eval` — evaluating it at `x` runs the continuation on the leaf assignment that `x` selects
  (`= (k (foldl-update acc with x over vars)).eval x`).
* `queryAll_depth` — depth `≤ #vars + d` whenever every continuation tree has depth `≤ d`.

## Honest scope

This is the per-block query atom of the adaptive canonical tree (increment 3, step 1).  The remaining
steps are: the descent recursion (fuel-based, mirroring `blockStream`), eval-correctness against the DNF
(via the `killTerm`/`activeTerm` dichotomy), and the assembled depth bound `≤ #blocks · width`.  Built
incrementally and honestly; no `sorry`.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

namespace DTree

variable {n : ℕ}

/-- A complete binary decision tree querying `vars`, threading the leaf assignment (built from `acc`
updated by the queried values) into the continuation `k`. -/
def queryAll : List (Fin n) → (Fin n → Bool) → ((Fin n → Bool) → DTree n) → DTree n
  | [], acc, k => k acc
  | v :: vars, acc, k =>
      node v (queryAll vars (Function.update acc v false) k)
             (queryAll vars (Function.update acc v true) k)

/-- **`queryAll` runs the continuation on the leaf assignment selected by `x`.** -/
theorem queryAll_eval (vars : List (Fin n)) (acc : Fin n → Bool)
    (k : (Fin n → Bool) → DTree n) (x : Fin n → Bool) :
    (queryAll vars acc k).eval x
      = (k (vars.foldl (fun a v => Function.update a v (x v)) acc)).eval x := by
  induction vars generalizing acc with
  | nil => rfl
  | cons v vars ih =>
    simp only [queryAll, eval, List.foldl_cons]
    split
    · next h => rw [h]; exact ih (Function.update acc v true)
    · next h =>
      simp only [Bool.not_eq_true] at h
      rw [h]; exact ih (Function.update acc v false)

/-- **`queryAll` depth `≤ #vars + d`** when every continuation has depth `≤ d`. -/
theorem queryAll_depth (vars : List (Fin n)) (acc : Fin n → Bool)
    (k : (Fin n → Bool) → DTree n) (d : ℕ) (hk : ∀ a, (k a).depth ≤ d) :
    (queryAll vars acc k).depth ≤ vars.length + d := by
  induction vars generalizing acc with
  | nil => simpa [queryAll] using hk acc
  | cons v vars ih =>
    simp only [queryAll, depth, List.length_cons]
    have h1 := ih (Function.update acc v false)
    have h2 := ih (Function.update acc v true)
    rcases Nat.le_total (queryAll vars (Function.update acc v false) k).depth
        (queryAll vars (Function.update acc v true) k).depth with hle | hle
    · rw [Nat.max_eq_right hle]; omega
    · rw [Nat.max_eq_left hle]; omega

end DTree

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.DTree.queryAll_eval
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.DTree.queryAll_depth
