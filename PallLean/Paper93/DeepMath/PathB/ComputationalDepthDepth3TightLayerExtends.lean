import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3TightLayerCollapse
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3TightSurvivorExtends

/-!
# Tight switching, step 19: the subcube-relative `EquivOn` round (branch `razborov-recoverRho-wip`)

The per-round building block of the nested multi-round loop: a tight `EquivOn` collapse round that moreover
**extends a fixed base `τ`** and **keeps `s ≤ stars ρ` survivors**.  This is `collapse_or_layer_tight`
(step 16) run on the conditional measure via `exists_survivor_shallow_extends` (step 18) instead of the
full-domain `exists_shallow_all_tight`.

Iterating this with `τ_{i+1} := ρ_i` keeps every later round inside the earlier subcube, so the survivor
sets nest and the common finest restriction `σ` has `stars σ ≥ s` — exactly the data
`iterated_not_parity_tight` (step 17) and `reduces_iterate` consume.

* `collapse_or_layer_tight_extends` — `∃ ρ, Extends τ ρ ∧ s ≤ stars ρ ∧ EquivOn ρ (OR-of-AND-of-DNF)
  (OR-of-CNF) ∧ widths < s`.

This closes the analytic content of the multi-round loop: every round's restriction is produced *and* its
survivor budget guaranteed, all `F`-independent, conditional only on the per-gate alive/leaf/position
hypotheses (the empty-skip wall, brick 49).  What remains is the purely structural recursion that defines
the tower sequence `C i` and alternates the collapse type down to a depth-2 bottom `DNF`; the depth-2 base
case is already closed non-vacuously (`tight_dnf_not_parity`, step 15).

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

private theorem any_congr_ext {α : Type*} (l : List α) (p q : α → Bool)
    (h : ∀ a ∈ l, p a = q a) : l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.any_cons, List.any_cons, h a (by simp),
      ih (fun b hb => h b (by simp [hb]))]

/-- **The subcube-relative tight `OR`-layer collapse.**  Like `collapse_or_layer_tight`, but the produced
restriction extends `τ` and retains `s ≤ stars ρ` survivors — the data the nested iteration threads. -/
theorem collapse_or_layer_tight_extends {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    {w F s : ℕ} [NeZero w] (hF : n ≤ F) (τ : Fin n → Option Bool)
    (gates : List (Finset (List (Clause n)))) (Gtot : Finset (List (Clause n)))
    (hsub : ∀ G ∈ gates, G ⊆ Gtot)
    (hnf : ∀ g ∈ Gtot, ∀ ρ : Restriction n, ∀ U ∈ g,
      SwitchingCounting.termFalsified ρ U = false)
    (hleaf : ∀ g ∈ Gtot, ∀ ρ : Restriction n,
      SwitchingCounting.anyTermSat g (deepestEnd g F ρ) = false)
    (hpos : ∀ g ∈ Gtot, ∀ ρ : Restriction n, ∀ q ∈ deepestFullSeq g F ρ, q.1 < w)
    (hr1 : (2 * p / (1 - p)) * (2 * (w : ℚ)) < 1)
    (hsmall :
        (∑ σ ∈ (extBox τ).filter (fun σ => SwitchingCounting.stars σ < s), pweight p σ)
          + (Gtot.card : ℚ)
              * (((2 * p / (1 - p)) * (2 * (w : ℚ))) ^ s
                  / (1 - (2 * p / (1 - p)) * (2 * (w : ℚ))))
        < ((1 - p) / 2) ^ (n - SwitchingCounting.stars τ)) :
    ∃ ρ : Fin n → Option Bool, Extends τ ρ ∧ s ≤ SwitchingCounting.stars ρ ∧
      EquivOn ρ (gOr (gates.map (fun G => gAnd (G.toList.map dnf))))
          (gOr (gates.map (fun G => cnf (G.toList.flatMap
            (fun g => dtreeToCNF (toDTree (canonicalDT g F ρ)))))))
        ∧ (∀ G ∈ gates, ∀ C ∈ G.toList.flatMap
              (fun g => dtreeToCNF (toDTree (canonicalDT g F ρ))), C.lits.length < s) := by
  obtain ⟨ρ, hext, hge, hle, hρ⟩ :=
    exists_survivor_shallow_extends hp0 hp3 hF τ Gtot hnf hleaf hpos hr1 hsmall
  have hshallow : ∀ G ∈ gates, ∀ g ∈ G, (canonicalDT g F ρ).depth < s :=
    fun G hG g hg => hρ g (hsub G hG hg)
  refine ⟨ρ, hext, hge, ?_, ?_⟩
  · intro x hx
    rw [eval_gOr, eval_gOr, List.any_map, List.any_map]
    apply any_congr_ext
    intro G hG
    simp only [Function.comp_apply]
    rw [eval_gAnd_dnf, eval_cnf]
    exact ((collapse_core_tight_list F s G hle (hshallow G hG)).1 x hx).symm
  · intro G hG C hC
    exact (collapse_core_tight_list F s G hle (hshallow G hG)).2 C hC

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.collapse_or_layer_tight_extends
