import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3QueryTree

/-!
# Block-DT model, foundation 26: the adaptive canonical decision tree (increment 3, step 2) (branch only)

The switching lemma's adaptive canonical decision tree, mirroring `blockStream`: at restriction `σ`, if
some term is satisfied accept; if no active term reject; otherwise query the active term's free variables
(via `queryAll`) and recurse on each falsifying leaf with that leaf's **own extended restriction** —
this per-leaf threading is the genuinely adaptive part.

* `canonicalDTree cs w F σ` — the adaptive tree (fuel `F`).
* `canonicalDTree_depth_le` — depth `≤ F · w` for a width-`≤ w` DNF.

## Honest scope

This brick defines the adaptive tree and proves the fuel-based depth bound `≤ F · w` (each block costs
`≤ w`, at most `F` blocks).  The remaining steps of increment 3: eval-correctness against the DNF (via
the `killTerm`/`activeTerm` dichotomy), and the tighter `≤ blockStream.length · w` bound (needs the
descent-length monotonicity under restriction extension), then the parity-bridge connection.  Built
incrementally and honestly; no `sorry`.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- The variable a literal queries (local, to avoid namespace coupling). -/
def litVarOf : Rung4Literal n → Fin n
  | Rung4Literal.pos v => v
  | Rung4Literal.neg v => v

/-- The free variables of a term under `σ` (those its literals query that `σ` leaves unset). -/
def freeVarsOf (σ : Fin n → Option Bool) (T : Clause n) : List (Fin n) :=
  T.lits.filterMap (fun ℓ => if σ (litVarOf ℓ) = none then some (litVarOf ℓ) else none)

/-- Extend `σ` by the leaf assignment `a` on the term's free variables. -/
def extendσ (σ : Fin n → Option Bool) (T : Clause n) (a : Fin n → Bool) : Fin n → Option Bool :=
  fun i => if i ∈ freeVarsOf σ T then some (a i) else σ i

/-- **The adaptive canonical decision tree.** -/
def canonicalDTree (cs : List (Clause n)) (w : ℕ) : ℕ → (Fin n → Option Bool) → DTree n
  | 0, _ => DTree.leaf false
  | F + 1, σ =>
    if anyTermSat cs σ then DTree.leaf true
    else match activeTerm cs σ with
      | none => DTree.leaf false
      | some T =>
        DTree.queryAll (freeVarsOf σ T) (fun _ => false)
          (fun a => if T.lits.all (fun ℓ => Rung4Literal.eval ℓ a) then DTree.leaf true
                    else canonicalDTree cs w F (extendσ σ T a))

/-- `freeVarsOf` is no longer than the term. -/
theorem freeVarsOf_length_le (σ : Fin n → Option Bool) (T : Clause n) :
    (freeVarsOf σ T).length ≤ T.lits.length := by
  rw [freeVarsOf]
  exact List.length_filterMap_le _ _

/-- The active term is a member of `cs`. -/
theorem activeTerm_mem {cs : List (Clause n)} {σ : Fin n → Option Bool} {T : Clause n}
    (h : activeTerm cs σ = some T) : T ∈ cs := by
  have hns := activeTerm_anyTermSat_false h
  have hfind : cs.find? (fun T => !termFalsified σ T && decide (0 < (freeLits σ T).length)) = some T :=
    activeTerm_eq_find hns ▸ h
  exact List.mem_of_find?_eq_some hfind

/-- **The adaptive tree has depth `≤ F · w`** for a width-`≤ w` DNF. -/
theorem canonicalDTree_depth_le (cs : List (Clause n)) (w : ℕ)
    (hw : ∀ T ∈ cs, T.lits.length ≤ w) :
    ∀ (F : ℕ) (σ : Fin n → Option Bool), (canonicalDTree cs w F σ).depth ≤ F * w := by
  intro F
  induction F with
  | zero => intro σ; simp [canonicalDTree, DTree.depth]
  | succ F ih =>
    intro σ
    rw [canonicalDTree]
    split
    · simp [DTree.depth]
    · next hns =>
      cases hact : activeTerm cs σ with
      | none => simp [DTree.depth]
      | some T =>
        have hfv : (freeVarsOf σ T).length ≤ w :=
          le_trans (freeVarsOf_length_le σ T) (hw T (activeTerm_mem hact))
        refine le_trans (DTree.queryAll_depth (freeVarsOf σ T) (fun _ => false) _ (F * w) ?_) ?_
        · intro a
          split
          · simp [DTree.depth]
          · exact ih (extendσ σ T a)
        · calc (freeVarsOf σ T).length + F * w ≤ w + F * w := by omega
            _ = (F + 1) * w := by ring

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.canonicalDTree_depth_le
