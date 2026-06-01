import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingCompletionVars

/-!
# The switching count closes: `|Bad| ≤ |Short| · 2ⁿ`

**STATUS: REAL.  THE COUNT LOOP CLOSES (loose bound) ON THE PROVED DECODE CORE.**

`pathClauseVars C = (C's variables) ∩ (path-variable set)`, so the path-variable *set*
alone determines the whole per-clause label.  Hence a bad restriction is determined by
its satisfying completion together with its path-variable set (`bad_inj'`), and the
encoding `ρ ↦ (complete ρ …, pathvar-set)` injects `Bad` into `Short × 𝒫(Fin n)`:

  `|Bad| ≤ |Short| · 2ⁿ`.

This is the honest *loose* count (the analog of the falsify arc's unconditional count): a
complete count theorem standing entirely on the proved decode core (`freeOn_completionVars_eq`,
`bad_inj`).  The `(2w)^s` tightening replaces `2ⁿ` by the clause-relative `PathLabel`
encoding (the walk) — a separate optimisation; the loop itself is closed.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- The path-variable *set* determines the per-clause label, so a bad restriction is
determined by its completion together with its path-variable set. -/
theorem bad_inj' {cs : List (Clause n)} {s : ℕ} {ρ σ : Restriction n}
    (hcomplete : complete ρ (pathLits cs ρ s) = complete σ (pathLits cs σ s))
    (hset : ((pathLits cs ρ s).map litVar).toFinset = ((pathLits cs σ s).map litVar).toFinset) :
    ρ = σ := by
  apply bad_inj hcomplete
  funext C
  simp only [pathClauseVars]
  rw [hset]

/-- **The switching count closes (loose `2ⁿ` bound).**  If every bad restriction's
completion lands in `Short`, then `|Bad| ≤ |Short| · 2ⁿ`. -/
theorem bad_card_le_completion {cs : List (Clause n)} {s : ℕ}
    {Bad Short : Finset (Restriction n)}
    (hmem : ∀ ρ ∈ Bad, complete ρ (pathLits cs ρ s) ∈ Short) :
    Bad.card ≤ Short.card * 2 ^ (Fintype.card (Fin n)) := by
  classical
  have hsub : ∀ ρ ∈ Bad,
      (fun ρ => (complete ρ (pathLits cs ρ s), ((pathLits cs ρ s).map litVar).toFinset)) ρ
        ∈ Short ×ˢ (Finset.univ.powerset : Finset (Finset (Fin n))) := by
    intro ρ hρ
    exact Finset.mem_product.mpr ⟨hmem ρ hρ, Finset.mem_powerset.mpr (Finset.subset_univ _)⟩
  have hinj : Set.InjOn
      (fun ρ => (complete ρ (pathLits cs ρ s), ((pathLits cs ρ s).map litVar).toFinset)) ↑Bad := by
    intro ρ _ σ _ heq
    exact bad_inj' (congrArg Prod.fst heq) (congrArg Prod.snd heq)
  calc Bad.card
      ≤ (Short ×ˢ (Finset.univ.powerset : Finset (Finset (Fin n)))).card :=
        Finset.card_le_card_of_injOn _ hsub hinj
    _ = Short.card * (Finset.univ : Finset (Fin n)).powerset.card := by rw [Finset.card_product]
    _ = Short.card * 2 ^ (Fintype.card (Fin n)) := by
        rw [Finset.card_powerset, Finset.card_univ]

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.bad_card_le_completion
