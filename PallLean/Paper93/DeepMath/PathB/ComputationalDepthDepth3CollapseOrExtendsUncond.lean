import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SurvivorExtendsUncond
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3TightCollapseOr

/-!
# Tight switching, step 38: unconditional dual-extends collapse round (branch `razborov-recoverRho-wip`)

The subcube-relative dual collapse round — the round-2 step a depth-4 reduction needs.
`collapse_to_dnf_layer_tight_uncond` (step 35) is full-domain; here we run it on the conditional measure
(`exists_survivor_shallow_extends_uncond`, step 36), so the produced `ρ` **extends `τ`** and keeps
`s ≤ stars ρ` survivors, while collapsing `OR`-of-`CNF` to a single bottom `DNF`.

* `collapse_to_dnf_layer_tight_extends_uncond` — `∃ ρ, Extends τ ρ ∧ s ≤ stars ρ ∧ (∀g shallow) ∧
  EquivOn ρ (gOr cnf) (dnf D) ∧ widths`.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered Classical

variable {n : ℕ}

/-- **Unconditional dual-extends collapse round (`OR`-of-`CNF` → `DNF`).**  The produced `ρ` extends `τ`,
retains `s ≤ stars ρ` survivors, and collapses the `OR`-of-`CNF`s to a single bottom `DNF` — no
`hnf`/`hleaf`/`hpos`. -/
theorem collapse_to_dnf_layer_tight_extends_uncond {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    {w F s m : ℕ} [NeZero w] [NeZero m] (hF : n ≤ F) (τ : Fin n → Option Bool)
    (G : Finset (List (Clause n)))
    (hw : ∀ g ∈ G.image negDNF, ∀ T ∈ g, T.lits.length ≤ w)
    (hm : ∀ g ∈ G.image negDNF, g.length ≤ m)
    (hr1 : (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ)) < 1)
    (hsmall :
        (∑ σ ∈ (extBox τ).filter (fun σ => SwitchingCounting.stars σ < s), pweight p σ)
          + ((G.image negDNF).card : ℚ)
              * (((2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ))) ^ s
                  / (1 - (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ))))
        < ((1 - p) / 2) ^ (n - SwitchingCounting.stars τ)) :
    ∃ ρ : Fin n → Option Bool, Extends τ ρ ∧ s ≤ SwitchingCounting.stars ρ ∧
      (∀ g ∈ G, (canonicalDT (negDNF g) F ρ).depth < s)
        ∧ EquivOn ρ (gOr (G.toList.map cnf))
          (dnf (G.toList.flatMap (fun g =>
            dtreeToDNF (DTree.negTree (toDTree (canonicalDT (negDNF g) F ρ))))))
        ∧ (∀ T ∈ G.toList.flatMap (fun g =>
              dtreeToDNF (DTree.negTree (toDTree (canonicalDT (negDNF g) F ρ)))),
            T.lits.length < s) := by
  classical
  obtain ⟨ρ, hext, hge, hle, hρ⟩ :=
    exists_survivor_shallow_extends_uncond hp0 hp3 hF τ (G.image negDNF) hw hm hr1 hsmall
  have hshallow : ∀ g ∈ G, (canonicalDT (negDNF g) F ρ).depth < s :=
    fun g hg => hρ (negDNF g) (Finset.mem_image_of_mem _ hg)
  refine ⟨ρ, hext, hge, hshallow, ?_, ?_⟩
  · intro x hx
    rw [eval_gOr_cnf, eval_dnf]
    exact ((collapse_core_or_tight F s G hle hshallow).1 x hx).symm
  · exact (collapse_core_or_tight F s G hle hshallow).2

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.collapse_to_dnf_layer_tight_extends_uncond
