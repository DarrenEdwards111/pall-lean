import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ShallowAllUncond
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SurvivorExtendsUncond
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3TightLayerCollapse

/-!
# Tight switching, step 37: unconditional `EquivOn` collapse rounds (branch `razborov-recoverRho-wip`)

`collapse_or_layer_tight` (step 16) and `collapse_or_layer_tight_extends` (step 19) with the empty-skip
hypotheses dropped — the underlying collapse-existence is now `exists_shallow_all_tight_uncond` (step 33)
resp. `exists_survivor_shallow_extends_uncond` (step 36).  These are the per-round `EquivOn` steps the
multi-round (depth-`d`) loop iterates, now unconditional (only width/clause-count bounds).

* `collapse_or_layer_tight_uncond` — unconditional `OR`-layer collapse round.
* `collapse_or_layer_tight_extends_uncond` — unconditional subcube-relative round (nests via `τ`).

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

private theorem any_congr_uncond {α : Type*} (l : List α) (p q : α → Bool)
    (h : ∀ a ∈ l, p a = q a) : l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.any_cons, List.any_cons, h a (by simp), ih (fun b hb => h b (by simp [hb]))]

/-- **Unconditional `OR`-layer collapse round.**  As `collapse_or_layer_tight`, but no
`hnf`/`hleaf`/`hpos` — only per-gate width/clause-count. -/
theorem collapse_or_layer_tight_uncond {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    {w F s m : ℕ} [NeZero w] [NeZero m] (hF : n ≤ F)
    (gates : List (Finset (List (Clause n)))) (Gtot : Finset (List (Clause n)))
    (hsub : ∀ G ∈ gates, G ⊆ Gtot)
    (hw : ∀ g ∈ Gtot, ∀ T ∈ g, T.lits.length ≤ w) (hm : ∀ g ∈ Gtot, g.length ≤ m)
    (hr1 : (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ)) < 1)
    (hsmall : (Gtot.card : ℚ)
        * (((2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ))) ^ s
            / (1 - (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ)))) < 1) :
    ∃ ρ : Fin n → Option Bool,
      EquivOn ρ (gOr (gates.map (fun G => gAnd (G.toList.map dnf))))
          (gOr (gates.map (fun G => cnf (G.toList.flatMap
            (fun g => dtreeToCNF (toDTree (canonicalDT g F ρ)))))))
        ∧ (∀ G ∈ gates, ∀ C ∈ G.toList.flatMap
              (fun g => dtreeToCNF (toDTree (canonicalDT g F ρ))), C.lits.length < s) := by
  obtain ⟨ρ, hρ⟩ := exists_shallow_all_tight_uncond hp0 hp3 Gtot hw hm hr1 hsmall
  have hstars : SwitchingCounting.stars ρ ≤ F :=
    le_trans (by rw [stars]; exact le_trans (Finset.card_le_univ _) (by simp)) hF
  have hshallow : ∀ G ∈ gates, ∀ g ∈ G, (canonicalDT g F ρ).depth < s :=
    fun G hG g hg => hρ g (hsub G hG hg)
  refine ⟨ρ, ?_, ?_⟩
  · intro x hx
    rw [eval_gOr, eval_gOr, List.any_map, List.any_map]
    apply any_congr_uncond
    intro G hG
    simp only [Function.comp_apply]
    rw [eval_gAnd_dnf, eval_cnf]
    exact ((collapse_core_tight_list F s G hstars (hshallow G hG)).1 x hx).symm
  · intro G hG C hC
    exact (collapse_core_tight_list F s G hstars (hshallow G hG)).2 C hC

/-- **Unconditional subcube-relative `OR`-layer collapse round.**  As `collapse_or_layer_tight_extends`, but
no `hnf`/`hleaf`/`hpos`; the produced `ρ` extends `τ` with `s ≤ stars ρ` survivors. -/
theorem collapse_or_layer_tight_extends_uncond {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    {w F s m : ℕ} [NeZero w] [NeZero m] (hF : n ≤ F) (τ : Fin n → Option Bool)
    (gates : List (Finset (List (Clause n)))) (Gtot : Finset (List (Clause n)))
    (hsub : ∀ G ∈ gates, G ⊆ Gtot)
    (hw : ∀ g ∈ Gtot, ∀ T ∈ g, T.lits.length ≤ w) (hm : ∀ g ∈ Gtot, g.length ≤ m)
    (hr1 : (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ)) < 1)
    (hsmall :
        (∑ σ ∈ (extBox τ).filter (fun σ => SwitchingCounting.stars σ < s), pweight p σ)
          + (Gtot.card : ℚ)
              * (((2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ))) ^ s
                  / (1 - (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ))))
        < ((1 - p) / 2) ^ (n - SwitchingCounting.stars τ)) :
    ∃ ρ : Fin n → Option Bool, Extends τ ρ ∧ s ≤ SwitchingCounting.stars ρ ∧
      EquivOn ρ (gOr (gates.map (fun G => gAnd (G.toList.map dnf))))
          (gOr (gates.map (fun G => cnf (G.toList.flatMap
            (fun g => dtreeToCNF (toDTree (canonicalDT g F ρ)))))))
        ∧ (∀ G ∈ gates, ∀ C ∈ G.toList.flatMap
              (fun g => dtreeToCNF (toDTree (canonicalDT g F ρ))), C.lits.length < s) := by
  obtain ⟨ρ, hext, hge, hle, hρ⟩ :=
    exists_survivor_shallow_extends_uncond hp0 hp3 hF τ Gtot hw hm hr1 hsmall
  have hshallow : ∀ G ∈ gates, ∀ g ∈ G, (canonicalDT g F ρ).depth < s :=
    fun G hG g hg => hρ g (hsub G hG hg)
  refine ⟨ρ, hext, hge, ?_, ?_⟩
  · intro x hx
    rw [eval_gOr, eval_gOr, List.any_map, List.any_map]
    apply any_congr_uncond
    intro G hG
    simp only [Function.comp_apply]
    rw [eval_gAnd_dnf, eval_cnf]
    exact ((collapse_core_tight_list F s G hle (hshallow G hG)).1 x hx).symm
  · intro G hG C hC
    exact (collapse_core_tight_list F s G hle (hshallow G hG)).2 C hC

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.collapse_or_layer_tight_uncond
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.collapse_or_layer_tight_extends_uncond
