import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3LayerCollapseWF

/-!
# AC⁰ reduction, foundation 26: the restriction-given layer collapse (branch only)

The adapter joining the conditional switching primitive (brick 25) to the reduction spine (brick 20).  The
layer collapses of bricks 17/19 *produce* their own restriction (via `exists_shallow_all`); but the
multi-round loop must use the restriction handed down from the *survivor* primitive
(`exists_shallow_survivor_extends`), which extends the previous round's subcube.  So we re-state the layer
collapse with the restriction **given** — shallowness as a hypothesis — exactly as `collapse_core`
(brick 17) is `single_round_collapse` with `ρ` given.

* `collapse_or_layer_at` — given `ρ` (and that every gate is shallow under it), the `OR`-of-`AND`-of-`DNF`
  layer is `EquivOn ρ` an `OR`-of-`CNF`s, with the output clauses well-formed (`< s`, `Consistent`, `Nodup`).
* `collapse_and_layer_at` — the dual.

Feeding the `ρ` from `exists_shallow_survivor_extends` (brick 25) into these gives one reduction round
(`Reduces.head`, brick 20) that lives on the nested subcube — the unit the `d`-round loop iterates.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

namespace Layered

variable {n : ℕ}

private theorem all_congr {α : Type*} (l : List α) (P Q : α → Bool) (h : ∀ a ∈ l, P a = Q a) :
    l.all P = l.all Q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.all_cons, List.all_cons, h a (List.mem_cons_self ..),
      ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

private theorem any_congr {α : Type*} (l : List α) (P Q : α → Bool) (h : ∀ a ∈ l, P a = Q a) :
    l.any P = l.any Q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.any_cons, List.any_cons, h a (List.mem_cons_self ..),
      ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

/-- **The restriction-given `OR`-layer collapse.**  With `ρ` given and every gate shallow under it, the
`OR`-of-`AND`-of-`DNF` layer is `EquivOn ρ` an `OR`-of-`CNF`s with well-formed output clauses. -/
theorem collapse_or_layer_at (w F s : ℕ) (gates : List (Finset (List (Clause n))))
    (ρ : Fin n → Option Bool) (hstars : stars ρ < F)
    (hnd : ∀ G ∈ gates, ∀ g ∈ G, ∀ T ∈ g, (T.lits.map litVarOf).Nodup)
    (hshallow : ∀ G ∈ gates, ∀ g ∈ G, (canonicalDTree g w F ρ).depth < s) :
    EquivOn ρ (gOr (gates.map (fun G => gAnd (G.toList.map dnf))))
        (gOr (gates.map (fun G => cnf (G.toList.flatMap
          (fun g => dtreeToCNF (canonicalDTree g w F ρ))))))
      ∧ (∀ G ∈ gates, ∀ C ∈ G.toList.flatMap (fun g => dtreeToCNF (canonicalDTree g w F ρ)),
          C.lits.length < s)
      ∧ (∀ G ∈ gates, ∀ C ∈ G.toList.flatMap (fun g => dtreeToCNF (canonicalDTree g w F ρ)),
          Consistent C ∧ (C.lits.map litVarOf).Nodup) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [eval_gOr, eval_gOr, List.any_map, List.any_map]
    apply any_congr
    intro G hG
    simp only [Function.comp_apply]
    rw [eval_gAnd_dnf, eval_cnf]
    exact ((collapse_core w F s G hstars (hshallow G hG)).1 x hx).symm
  · intro G hG C hC
    exact (collapse_core w F s G hstars (hshallow G hG)).2 C hC
  · intro G hG C hC
    rw [List.mem_flatMap] at hC
    obtain ⟨g, hg, hCg⟩ := hC
    have hfresh := canonicalDTree_fresh g w (hnd G hG g (Finset.mem_toList.mp hg)) F ρ
    exact ⟨dtreeToCNF_consistent _ hfresh C hCg, dtreeToCNF_nodup _ hfresh C hCg⟩

/-- **The restriction-given `AND`-layer collapse (dual).** -/
theorem collapse_and_layer_at (w F s : ℕ) (gates : List (Finset (List (Clause n))))
    (ρ : Fin n → Option Bool) (hstars : stars ρ < F)
    (hnd : ∀ G ∈ gates, ∀ g ∈ G, ∀ C ∈ g, (C.lits.map litVarOf).Nodup)
    (hshallow : ∀ G ∈ gates, ∀ g ∈ G, (canonicalDTree (negDNF g) w F ρ).depth < s) :
    EquivOn ρ (gAnd (gates.map (fun G => gOr (G.toList.map cnf))))
        (gAnd (gates.map (fun G => dnf (G.toList.flatMap
          (fun g => dtreeToDNF (DTree.negTree (canonicalDTree (negDNF g) w F ρ)))))))
      ∧ (∀ G ∈ gates, ∀ T ∈ G.toList.flatMap
            (fun g => dtreeToDNF (DTree.negTree (canonicalDTree (negDNF g) w F ρ))),
          T.lits.length < s)
      ∧ (∀ G ∈ gates, ∀ T ∈ G.toList.flatMap
            (fun g => dtreeToDNF (DTree.negTree (canonicalDTree (negDNF g) w F ρ))),
          Consistent T ∧ (T.lits.map litVarOf).Nodup) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [eval_gAnd, eval_gAnd, List.all_map, List.all_map]
    apply all_congr
    intro G hG
    simp only [Function.comp_apply]
    rw [eval_gOr_cnf, eval_dnf]
    exact ((collapse_core_or w F s G hstars (hshallow G hG)).1 x hx).symm
  · intro G hG T hT
    exact (collapse_core_or w F s G hstars (hshallow G hG)).2 T hT
  · intro G hG T hT
    rw [List.mem_flatMap] at hT
    obtain ⟨g, hg, hTg⟩ := hT
    have hndg : ∀ C ∈ g, (C.lits.map litVarOf).Nodup := hnd G hG g (Finset.mem_toList.mp hg)
    have hndneg : ∀ C ∈ negDNF g, (C.lits.map litVarOf).Nodup := by
      intro C hC
      rw [negDNF, List.mem_map] at hC
      obtain ⟨C0, hC0, rfl⟩ := hC
      have hmap : (C0.lits.map negLit).map litVarOf = C0.lits.map litVarOf := by
        rw [List.map_map]; exact List.map_congr_left (fun ℓ _ => litVarOf_negLit ℓ)
      simpa [hmap] using hndg C0 hC0
    have hfresh := DTree.negTree_fresh _ (canonicalDTree_fresh (negDNF g) w hndneg F ρ)
    exact ⟨dtreeToDNF_consistent _ hfresh T hTg, dtreeToDNF_nodup _ hfresh T hTg⟩

end Layered

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.Layered.collapse_or_layer_at
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.Layered.collapse_and_layer_at
