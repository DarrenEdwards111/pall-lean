import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BranchingHolography

/-!
# Block-DT model, foundation 37: branching holography, step 1.5 — pathLen is the tree path length (branch only)

Solidifying the branching-holography object: the per-input descent `pathLen` (brick 36) is *exactly* the
root-to-leaf path length of the input in the abstract decision tree.

* `DTree.dtPathLen` — the root-to-leaf path length of an input in a decision tree (`+1` per query).
* `dtPathLen_le_depth` — `dtPathLen ≤ depth` (every path is at most the height).
* `dtPathLen_queryAll` — `dtPathLen` through a `queryAll` block is `#vars + dtPathLen` of the continuation.
* `pathLen_eq_dtPathLen` — `pathLen cs w F σ x = dtPathLen (canonicalDTree cs w F σ) x`.

So the per-input descent the count will encode is literally the abstract tree-path length.

## Honest note

The *exists*-direction (`depth ≥ s → ∃ x, pathLen ≥ s`, i.e. the deepest input realises the height)
requires the canonical tree to not re-query a variable (well-formedness, from the per-block
disjointness/`stars`-decrease) — for a *general* `DTree` a structural-deepest path can be unrealisable.
That well-formedness is the next sub-project; this brick fixes the object as the genuine tree-path.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

namespace DTree

/-- The root-to-leaf path length of input `x` in a decision tree. -/
def dtPathLen : DTree n → (Fin n → Bool) → ℕ
  | leaf _, _ => 0
  | node v lo hi, x => (if x v then dtPathLen hi x else dtPathLen lo x) + 1

/-- **Path length is at most height.** -/
theorem dtPathLen_le_depth (t : DTree n) (x : Fin n → Bool) : dtPathLen t x ≤ t.depth := by
  induction t with
  | leaf b => simp [dtPathLen, depth]
  | node v lo hi ihlo ihhi =>
    simp only [dtPathLen, depth]
    have hm1 := le_max_left lo.depth hi.depth
    have hm2 := le_max_right lo.depth hi.depth
    split <;> omega

/-- **`dtPathLen` through a `queryAll` block.** -/
theorem dtPathLen_queryAll (vars : List (Fin n)) (k : (Fin n → Bool) → DTree n) (x : Fin n → Bool) :
    ∀ (acc : Fin n → Bool),
      dtPathLen (queryAll vars acc k) x
        = vars.length + dtPathLen (k (vars.foldl (fun a v => Function.update a v (x v)) acc)) x := by
  induction vars with
  | nil => intro acc; simp [queryAll]
  | cons v vars ih =>
    intro acc
    simp only [queryAll, dtPathLen, List.foldl_cons, List.length_cons]
    split
    · next h => rw [ih (Function.update acc v true), h]; omega
    · next h =>
      rw [Bool.not_eq_true] at h
      rw [ih (Function.update acc v false), h]; omega

end DTree

/-- **`pathLen` is the tree path length.**  The per-input DNF descent equals the abstract decision-tree
path length of the input in the canonical tree. -/
theorem pathLen_eq_dtPathLen (cs : List (Clause n)) (w : ℕ) :
    ∀ (F : ℕ) (σ : Fin n → Option Bool) (x : Fin n → Bool),
      pathLen cs w F σ x = DTree.dtPathLen (canonicalDTree cs w F σ) x := by
  intro F
  induction F with
  | zero => intro σ x; simp [pathLen, canonicalDTree, DTree.dtPathLen]
  | succ F ih =>
    intro σ x
    cases hany : anyTermSat cs σ with
    | true => rw [pathLen, canonicalDTree]; simp [hany, DTree.dtPathLen]
    | false =>
      cases hact : activeTerm cs σ with
      | none => rw [pathLen, canonicalDTree]; simp [hany, hact, DTree.dtPathLen]
      | some T =>
        have hpl : pathLen cs w (F + 1) σ x
            = (freeVarsOf σ T).length
              + (if (T.lits.filter (DTree.freeLit σ)).all (fun ℓ => Rung4Literal.eval ℓ x) then 0
                 else pathLen cs w F (extendσ σ T x) x) := by
          rw [pathLen]; simp only [hany, Bool.false_eq_true, if_false, hact]
        have hcd : canonicalDTree cs w (F + 1) σ
            = DTree.queryAll (freeVarsOf σ T) (fun _ => false)
                (fun a => if (T.lits.filter (DTree.freeLit σ)).all (fun ℓ => Rung4Literal.eval ℓ a)
                          then DTree.leaf true else canonicalDTree cs w F (extendσ σ T a)) := by
          rw [canonicalDTree]; simp only [hany, Bool.false_eq_true, if_false, hact]
        rw [hpl, hcd, DTree.dtPathLen_queryAll, cond_leaf_eq, extendσ_leaf_eq]
        congr 1
        split
        · simp [DTree.dtPathLen]
        · exact ih (extendσ σ T x) x

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.pathLen_eq_dtPathLen
