import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SetDecode

/-!
# Block-DT model, foundation 47: branching holography, step 4e — Finset card inequality (branch only)

The injection mechanics, realised as a genuine `Finset.card` inequality: the restrictions whose canonical
tree has depth `≥ s` inject (via `σ ↦ (descentFinal, freed-variable set)`, with `σ` recovered by the
set-form decoder) into the pairs `(restriction, variable-set of size ≥ s)`.

* `bad_card_le` — `|{σ : depth ≥ s}| ≤ |{(f, S) : s ≤ S.card}|`.

## IMPORTANT — this bound is LOOSE (not yet the switching bound)

The right-hand side has cardinality `3^n · #{S : |S| ≥ s} ≥ 3^n`, while the left-hand side is trivially
`≤ 3^n`.  So **this inequality does not beat the trivial bound** — it is the injection *mechanics*
(`Finset.card_le_card_of_injOn` into a `Fintype` codomain), not the quantitative switching estimate.

The `(c·w)^s` gain requires a *smaller* codomain: a per-block position *label* (living in a space of size
`(c·w)^s`) from which the freed set is **recovered by replaying the canonical tree on the final
restriction** — rather than storing the full freed set as done here.  That replay/position encoding is the
genuine remaining content; this brick only banks the reusable `injOn`-to-`Finset` scaffolding it will use.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **Finset card inequality (loose).**  The restrictions with a depth-`≥ s` canonical tree inject into
`(restriction, ≥ s`-sized variable-set`)` pairs.  See the file header: this RHS is `≥ 3^n`, so the bound
is not yet better than trivial — it is the injection mechanics, not the switching estimate. -/
theorem bad_card_le (cs : List (Clause n)) (w : ℕ)
    (hnd : ∀ T ∈ cs, (T.lits.map litVarOf).Nodup) (F s : ℕ) :
    (Finset.univ.filter
        (fun σ : Fin n → Option Bool => s ≤ (canonicalDTree cs w F σ).depth)).card
      ≤ (Finset.univ.filter
        (fun p : (Fin n → Option Bool) × Finset (Fin n) => s ≤ p.2.card)).card := by
  classical
  apply Finset.card_le_card_of_injOn
    (fun σ => (descentFinal cs w F σ (Classical.choose (exists_deep_input cs w hnd F σ)),
               (descentLabels cs w F σ
                 (Classical.choose (exists_deep_input cs w hnd F σ))).flatten.toFinset))
  · -- the image lands in the target: the freed set has `≥ s` elements
    intro σ hσ
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hσ ⊢
    have hx := Classical.choose_spec (exists_deep_input cs w hnd F σ)
    rw [List.toFinset_card_of_nodup
        (descentLabels_flatten_nodup cs w hnd F σ _), descentLabels_flatten_length]
    exact le_trans hσ hx
  · -- injectivity: recover `σ` from the final restriction and freed set
    intro σ₁ _ σ₂ _ heq
    set x₁ := Classical.choose (exists_deep_input cs w hnd F σ₁) with hx₁
    set x₂ := Classical.choose (exists_deep_input cs w hnd F σ₂) with hx₂
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hf, hS⟩ := heq
    have hiff : ∀ v, v ∈ (descentLabels cs w F σ₁ x₁).flatten
        ↔ v ∈ (descentLabels cs w F σ₂ x₂).flatten := by
      intro v
      constructor
      · intro h; exact List.mem_toFinset.mp (hS ▸ List.mem_toFinset.mpr h)
      · intro h; exact List.mem_toFinset.mp (hS.symm ▸ List.mem_toFinset.mpr h)
    rw [← descent_decode_set cs w F σ₁ x₁, ← descent_decode_set cs w F σ₂ x₂]
    funext v
    by_cases hv1 : v ∈ (descentLabels cs w F σ₁ x₁).flatten
    · rw [if_pos hv1, if_pos ((hiff v).mp hv1)]
    · rw [if_neg hv1, if_neg (fun h => hv1 ((hiff v).mpr h)), hf]

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.bad_card_le
