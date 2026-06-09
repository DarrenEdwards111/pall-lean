import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3LabelBound
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CanonicalComplete

/-!
# Block-DT model, F-independence step 1: the block count is bounded by the path length (branch `razborov-recoverRho-wip`)

The first step of tightening the branching switching lemma's label space from the crude **fuel-dependent**
`(4^w+1)^F` (`descent_switching_count` / `descent_switching_prob`) to a **path-content** bound — the route to
the `F`-independent, `m`-free, `hnf`-free tight count.

The branching (satisfying-extension) decoder `descentSat` already drops `hnf` (it recovers the active term as
the *first satisfied term* of the boundary, which automatically skips pre-falsified clauses — the empty-skip
wall that defeats the falsification-replay decoder).  Its weakness is purely quantitative: the label space is
counted by `≤ F` blocks (one per fuel step), giving `(4^w+1)^F`.  But `LabelBound` proves the labels carry
exactly `pathLen` variables in total (`descentLabels_flatten_length`), and every block is the freed-variable
set `freeVarsOf σ T` of an *active* term, which is **non-empty** (`activeTerm_exists_free`).  A list of
non-empty blocks has length `≤` its flattened length, so:

```
  (descentLabels cs w F σ x).length ≤ pathLen cs w F σ x      -- #blocks ≤ total stars
```

— the number of blocks is bounded by the path length, **independently of the fuel `F`**.  On the bad event
`pathLen ≥ s`, so the genuinely-used blocks number `≤ pathLen`, and combined with the per-step `≤ w` width
(`descentLabels_label_le_w`) the label content is a partition of `≤ pathLen` slots into `≤ w`-blocks — the
shape whose cardinality is `(O(w))^{pathLen}`, the `F`-independent target.

* `length_le_flatten_length` — a list of non-empty blocks is no longer than its flattening.
* `descentLabels_block_nonempty` — every descent block is a non-empty freed-variable set.
* `descentLabels_length_le_pathLen` — **`#blocks ≤ pathLen`**, the `F`-independent block count.

## Honest scope

This is the block-*count* bound (`#blocks ≤ pathLen`), the structural keystone for `F`-independence.  The
remaining work is the cardinality re-encoding — injecting the content-`pathLen` label streams into an
`(O(w))^{pathLen}` space — and threading it through the weight gain (`(2p/(1-p))^{pathLen}`) to obtain the
tight `((2p/(1-p))·O(w))^s` switching bound that closes the parity regime for all depths.  That is **not** done
here; this delivers the count bound the re-encoding rests on.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- A list of **non-empty** blocks has length at most the length of its flattening. -/
theorem length_le_flatten_length {α : Type*} :
    ∀ (L : List (List α)), (∀ b ∈ L, 1 ≤ b.length) → L.length ≤ L.flatten.length
  | [], _ => by simp
  | b :: L', h => by
    rw [List.flatten_cons, List.length_append, List.length_cons]
    have hb : 1 ≤ b.length := h b (List.mem_cons_self ..)
    have hL' : L'.length ≤ L'.flatten.length :=
      length_le_flatten_length L' (fun c hc => h c (List.mem_cons_of_mem _ hc))
    omega

/-- **Every descent block is a non-empty freed-variable set.**  Each block is `freeVarsOf σ T` for an active
term `T`, which has a free variable, so it is non-empty. -/
theorem descentLabels_block_nonempty (cs : List (Clause n)) (w : ℕ) :
    ∀ (F : ℕ) (σ : Fin n → Option Bool) (x : Fin n → Bool),
      ∀ b ∈ descentLabels cs w F σ x, 1 ≤ b.length := by
  intro F
  induction F with
  | zero => intro σ x b hb; rw [descentLabels] at hb; simp at hb
  | succ F ih =>
    intro σ x b hb
    rw [descentLabels] at hb
    cases hany : anyTermSat cs σ with
    | true => rw [hany] at hb; simp at hb
    | false =>
      cases hact : activeTerm cs σ with
      | none => simp only [hany, Bool.false_eq_true, if_false, hact] at hb; simp at hb
      | some T =>
        obtain ⟨v, hv, _⟩ := activeTerm_exists_free hact
        have hne : 1 ≤ (freeVarsOf σ T).length := List.length_pos_of_mem hv
        simp only [hany, Bool.false_eq_true, if_false, hact] at hb
        by_cases hsat : (T.lits.filter (DTree.freeLit σ)).all (fun ℓ => Rung4Literal.eval ℓ x)
        · rw [if_pos hsat] at hb; rw [List.mem_singleton.mp hb]; exact hne
        · rw [if_neg hsat, List.mem_cons] at hb
          cases hb with
          | inl h => rw [h]; exact hne
          | inr h => exact ih (extendσ σ T x) x b h

/-- **The block count is bounded by the path length — `F`-independent.**  The number of descent blocks is at
most `pathLen` (the total number of stars freed), since each block is a non-empty freed-variable set and the
blocks flatten to exactly `pathLen` variables. -/
theorem descentLabels_length_le_pathLen (cs : List (Clause n)) (w F : ℕ) (σ : Fin n → Option Bool)
    (x : Fin n → Bool) :
    (descentLabels cs w F σ x).length ≤ pathLen cs w F σ x := by
  rw [← descentLabels_flatten_length cs w F σ x]
  exact length_le_flatten_length _ (descentLabels_block_nonempty cs w F σ x)

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.descentLabels_length_le_pathLen
