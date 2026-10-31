import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3LabelBlockCount
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3TaggedFlatten

/-!
# Block-DT model, route-2 step 2: the freed-position label cardinality `(2w+1)^pathLen` (branch `razborov-recoverRho-wip`)

The cardinality half of route 2 — **no probability yet**.  The depth-graded descent labels are var-lists
(`descentLabels`, over `Fin n`); to count them `w`-dependently (not `n`-dependently) we map each block's freed
variables to their **in-term positions** `Fin w`.  The resulting freed-position label has flatten-content
exactly `pathLen` (the map preserves block lengths) and non-empty blocks, so brick 147's tagged-flatten count
gives `≤ (2·w+1)^{pathLen}`.

* `posInTerm` — the `Fin w` position of a variable in a term (real position for the term's variables).
* `descentPosLabels` — `descentLabels` with each block's vars mapped to their positions (`List (List (Fin w))`).
* `descentPosLabels_flatten_length` — content equals `pathLen`.
* `descentPosLabels_block_nonempty` — every block is non-empty.
* `descentPosLabels_card_le` — over a fixed-content (`pathLen = k`) bad set, the label image has card
  `≤ (2·w+1)^k`, **`F`-independent**.

The weighted geometric sum (the probability algebra) is the *separate* next brick [155]; this one is purely the
label cardinality.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- The `Fin w` position of variable `v` in term `T` (the index of its first literal; `% w` for totality —
exact for a variable of `T` under width `≤ w`). -/
def posInTerm (w : ℕ) [NeZero w] (T : Clause n) (v : Fin n) : Fin w :=
  ⟨(T.lits.findIdx (fun ℓ => decide (litVarOf ℓ = v))) % w, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne w))⟩

/-- The freed-position label: `descentLabels` with each block's freed variables mapped to their `Fin w`
positions.  (Same control flow as `descentLabels`.) -/
def descentPosLabels (cs : List (Clause n)) (w : ℕ) [NeZero w] :
    ℕ → (Fin n → Option Bool) → (Fin n → Bool) → List (List (Fin w))
  | 0, _, _ => []
  | F + 1, σ, x =>
    if anyTermSat cs σ then []
    else match activeTerm cs σ with
      | none => []
      | some T =>
        if (T.lits.filter (DTree.freeLit σ)).all (fun ℓ => Rung4Literal.eval ℓ x) then
          [(freeVarsOf σ T).map (posInTerm w T)]
        else (freeVarsOf σ T).map (posInTerm w T) :: descentPosLabels cs w F (extendσ σ T x) x

/-- **Content equals the path length.**  Mapping vars to positions preserves block lengths, so the freed-position
label carries exactly `pathLen` positions in total. -/
theorem descentPosLabels_flatten_length (cs : List (Clause n)) (w : ℕ) [NeZero w] :
    ∀ (F : ℕ) (σ : Fin n → Option Bool) (x : Fin n → Bool),
      (descentPosLabels cs w F σ x).flatten.length = pathLen cs w F σ x := by
  intro F
  induction F with
  | zero => intro σ x; simp [descentPosLabels, pathLen]
  | succ F ih =>
    intro σ x
    rw [descentPosLabels, pathLen]
    cases hany : anyTermSat cs σ with
    | true => simp [hany]
    | false =>
      cases hact : activeTerm cs σ with
      | none => simp [hany, hact]
      | some T =>
        simp only [hany, Bool.false_eq_true, if_false, hact]
        by_cases hsat : (T.lits.filter (DTree.freeLit σ)).all (fun ℓ => Rung4Literal.eval ℓ x) = true
        · rw [if_pos hsat, if_pos hsat]
          simp [List.length_map]
        · rw [if_neg hsat, if_neg hsat]
          rw [List.flatten_cons, List.length_append, List.length_map, ih (extendσ σ T x) x]

/-- **Every freed-position block is non-empty.**  Each block is the freed-variable set of an active term,
which is non-empty. -/
theorem descentPosLabels_block_nonempty (cs : List (Clause n)) (w : ℕ) [NeZero w] :
    ∀ (F : ℕ) (σ : Fin n → Option Bool) (x : Fin n → Bool),
      ∀ b ∈ descentPosLabels cs w F σ x, b ≠ [] := by
  intro F
  induction F with
  | zero => intro σ x b hb; rw [descentPosLabels] at hb; simp at hb
  | succ F ih =>
    intro σ x b hb
    rw [descentPosLabels] at hb
    cases hany : anyTermSat cs σ with
    | true => rw [hany] at hb; simp at hb
    | false =>
      cases hact : activeTerm cs σ with
      | none => simp only [hany, Bool.false_eq_true, if_false, hact] at hb; simp at hb
      | some T =>
        obtain ⟨v, hv, _⟩ := activeTerm_exists_free hact
        have hne : (freeVarsOf σ T).map (posInTerm w T) ≠ [] := by
          simp only [ne_eq, List.map_eq_nil_iff]
          exact List.ne_nil_of_mem hv
        simp only [hany, Bool.false_eq_true, if_false, hact] at hb
        by_cases hsat : (T.lits.filter (DTree.freeLit σ)).all (fun ℓ => Rung4Literal.eval ℓ x) = true
        · rw [if_pos hsat] at hb; rw [List.mem_singleton.mp hb]; exact hne
        · rw [if_neg hsat, List.mem_cons] at hb
          cases hb with
          | inl h => rw [h]; exact hne
          | inr h => exact ih (extendσ σ T x) x b h

/-- **The freed-position label count is `(2·w+1)^k`, `F`-independent.**  Over a bad set on which the path
length is fixed to `k`, the freed-position labels (content `k`, non-empty blocks) number at most `(2·w+1)^k`. -/
theorem descentPosLabels_card_le (cs : List (Clause n)) (w : ℕ) [NeZero w] (F : ℕ) (x : Fin n → Bool)
    (k : ℕ) {Bad : Finset (Fin n → Option Bool)}
    (hk : ∀ σ ∈ Bad, pathLen cs w F σ x = k) :
    (Bad.image (fun σ => descentPosLabels cs w F σ x)).card ≤ (2 * w + 1) ^ k := by
  classical
  have hbound := nonempty_block_streams_card_le (α := Fin w) k
    (S := Bad.image (fun σ => descentPosLabels cs w F σ x))
    (fun L hL b hb => by
      obtain ⟨σ, _, rfl⟩ := Finset.mem_image.mp hL
      exact descentPosLabels_block_nonempty cs w F σ x b hb)
    (fun L hL => by
      obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hL
      rw [descentPosLabels_flatten_length, hk σ hσ])
  rwa [Fintype.card_fin] at hbound

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.descentPosLabels_card_le
