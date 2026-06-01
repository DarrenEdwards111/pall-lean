import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingPathLabel
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingCounting

/-!
# Tight-label counting bound `|Bad| ≤ |Short| · (2w)^s`

**STATUS: REAL.  THE CANONICAL ENCODE + ITS INJECTIVITY IS THE ISOLATED GATE.**

The switching count with the *tight* `(2w)^s` label.  Given a label function
`lab : Restriction → PathLabel w s` and the **recovery** property — a bad
restriction is determined by its shortened restriction together with its label —
the encoding `ρ ↦ (fixOn ρ (sel ρ) (a ρ), lab ρ)` injects `Bad` into
`Short × PathLabel w s`, so

  `|Bad| ≤ |Short| · (2w)^s`.

This is exactly the form the binomial layer-ratio consumes (the `(2w)^s` label
factor vs the `t`-star/`(t-s)`-star ratio).  The only remaining content is to
*construct* the canonical-path label `lab` and prove the recovery hypothesis
`hrec` — the active-clause sequential traversal and its injectivity, the genuine
hard core of Håstad's lemma.  Stated here as a hypothesis (a concrete equality
condition, not a vacuous socket).
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

variable {n : ℕ}

/-- **Tight-label switching count.**  If every bad restriction's shortened image
lands in `Short`, and a bad restriction is recovered from its shortened image plus
its `(2w)^s`-bounded path label, then `|Bad| ≤ |Short| · (2w)^s`. -/
theorem card_bad_le_pathlabel {w s : ℕ}
    (sel : Restriction n → Finset (Fin n)) (a : Restriction n → (Fin n → Bool))
    (lab : Restriction n → PathLabel w s)
    {Bad Short : Finset (Restriction n)}
    (hmem : ∀ ρ ∈ Bad, fixOn ρ (sel ρ) (a ρ) ∈ Short)
    (hrec : ∀ ρ ∈ Bad, ∀ σ ∈ Bad,
        fixOn ρ (sel ρ) (a ρ) = fixOn σ (sel σ) (a σ) → lab ρ = lab σ → ρ = σ) :
    Bad.card ≤ Short.card * (2 * w) ^ s := by
  classical
  have hcard : (Finset.univ : Finset (PathLabel w s)).card = (2 * w) ^ s := by
    rw [Finset.card_univ]; exact card_pathLabels w s
  have hsub : ∀ ρ ∈ Bad, (fun ρ => (fixOn ρ (sel ρ) (a ρ), lab ρ)) ρ
      ∈ Short ×ˢ (Finset.univ : Finset (PathLabel w s)) := by
    intro ρ hρ
    exact Finset.mem_product.mpr ⟨hmem ρ hρ, Finset.mem_univ _⟩
  have hinj : Set.InjOn (fun ρ => (fixOn ρ (sel ρ) (a ρ), lab ρ)) ↑Bad := by
    intro ρ hρ σ hσ heq
    exact hrec ρ (Finset.mem_coe.mp hρ) σ (Finset.mem_coe.mp hσ)
      (congrArg Prod.fst heq) (congrArg Prod.snd heq)
  calc Bad.card
      ≤ (Short ×ˢ (Finset.univ : Finset (PathLabel w s))).card :=
        Finset.card_le_card_of_injOn _ hsub hinj
    _ = Short.card * (2 * w) ^ s := by rw [Finset.card_product, hcard]

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.card_bad_le_pathlabel
