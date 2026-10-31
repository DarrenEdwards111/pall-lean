import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SurvivorShallowFindep
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3LayerCollapseAt
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SingleRoundOr

/-!
# Block-DT model, route-2 step [163]: the m-FREE producing AND-layer collapse (dual)

The `AND`-layer dual of [162].  The existing m-ful `collapse_and_layer` obtains its survivor from
`exists_shallow_all` on the De-Morgan-negated gate set `Gtot.image negDNF`; here we use the m-free,
`F`-independent `exists_survivor_shallow_findep` (brick [157]) on the same negated set.  The negated
gates inherit the switching hypotheses via `consistent_negClause` / `litVarOf_negLit` (negation
preserves consistency, the variable multiset, and width), and the geometric deep-cap is monotone in
the gate count so the budget transfers from `Gtot.card` to `(Gtot.image negDNF).card ≤ Gtot.card`.

* `collapse_and_layer_findep` — under the m-free three-tail budget, some `ρ` makes the
  `AND`-of-`OR`-of-`CNF` layer `EquivOn`-collapse to an `AND`-of-`DNF` with every term of width `< s`.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

namespace Layered

variable {n : ℕ}

/-- **The m-free producing `AND`-layer collapse.**  Dual of `collapse_or_layer_findep`: the survivor
is produced by the m-free budget [157] applied to the negated gate set `Gtot.image negDNF`, which
inherits the switching hypotheses by De Morgan.  No `hF : n < F` needed. -/
theorem collapse_and_layer_findep {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    {w F s : ℕ} [NeZero w] (gates : List (Finset (List (Clause n))))
    (Gtot : Finset (List (Clause n)))
    (hsub : ∀ G ∈ gates, G ⊆ Gtot)
    (hcons : ∀ g ∈ Gtot, ∀ C ∈ g, Consistent C)
    (hnd : ∀ g ∈ Gtot, ∀ C ∈ g, (C.lits.map litVarOf).Nodup)
    (hw : ∀ g ∈ Gtot, ∀ C ∈ g, C.lits.length ≤ w)
    (hr' : (2 * p / (1 - p)) * (4 * w + 1) < 1)
    (hsmall :
        (∑ ρ ∈ Finset.univ.filter (fun ρ : Restriction n => SwitchingCounting.stars ρ < s),
            pweight p ρ)
          + (∑ ρ ∈ Finset.univ.filter (fun ρ : Restriction n => F ≤ SwitchingCounting.stars ρ),
              pweight p ρ)
          + (Gtot.card : ℚ)
              * (((2 * p / (1 - p)) * (4 * w + 1)) ^ s
                  / (1 - (2 * p / (1 - p)) * (4 * w + 1))) < 1) :
    ∃ ρ : Fin n → Option Bool,
      EquivOn ρ (gAnd (gates.map (fun G => gOr (G.toList.map cnf))))
          (gAnd (gates.map (fun G => dnf (G.toList.flatMap
            (fun g => dtreeToDNF (DTree.negTree (canonicalDTree (negDNF g) w F ρ)))))))
        ∧ (∀ G ∈ gates, ∀ T ∈ G.toList.flatMap
              (fun g => dtreeToDNF (DTree.negTree (canonicalDTree (negDNF g) w F ρ))),
            T.lits.length < s) := by
  classical
  -- the negated gate set inherits the switching hypotheses (De Morgan)
  have hcons' : ∀ g ∈ Gtot.image negDNF, ∀ T ∈ g, Consistent T := by
    intro g hg T hT
    rw [Finset.mem_image] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    rw [negDNF, List.mem_map] at hT
    obtain ⟨C, hC, rfl⟩ := hT
    exact consistent_negClause (hcons g0 hg0 C hC)
  have hnd' : ∀ g ∈ Gtot.image negDNF, ∀ T ∈ g, (T.lits.map litVarOf).Nodup := by
    intro g hg T hT
    rw [Finset.mem_image] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    rw [negDNF, List.mem_map] at hT
    obtain ⟨C, hC, rfl⟩ := hT
    have hmap : (C.lits.map negLit).map litVarOf = C.lits.map litVarOf := by
      rw [List.map_map]; exact List.map_congr_left (fun ℓ _ => litVarOf_negLit ℓ)
    simpa [hmap] using hnd g0 hg0 C hC
  have hw' : ∀ g ∈ Gtot.image negDNF, ∀ T ∈ g, T.lits.length ≤ w := by
    intro g hg T hT
    rw [Finset.mem_image] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    rw [negDNF, List.mem_map] at hT
    obtain ⟨C, hC, rfl⟩ := hT
    simpa using hw g0 hg0 C hC
  -- the geometric deep-cap is nonnegative, so the budget is monotone in the gate count
  have hp1 : (0 : ℚ) < 1 - p := by linarith
  have h2p : (0 : ℚ) ≤ 2 * p / (1 - p) := div_nonneg (by linarith) (by linarith)
  have hr0 : (0 : ℚ) ≤ (2 * p / (1 - p)) * (4 * w + 1) := mul_nonneg h2p (by positivity)
  have hcap0 : (0 : ℚ) ≤ ((2 * p / (1 - p)) * (4 * w + 1)) ^ s
      / (1 - (2 * p / (1 - p)) * (4 * w + 1)) :=
    div_nonneg (pow_nonneg hr0 s) (by linarith)
  have hmono : ((Gtot.image negDNF).card : ℚ)
        * (((2 * p / (1 - p)) * (4 * w + 1)) ^ s / (1 - (2 * p / (1 - p)) * (4 * w + 1)))
      ≤ (Gtot.card : ℚ)
        * (((2 * p / (1 - p)) * (4 * w + 1)) ^ s / (1 - (2 * p / (1 - p)) * (4 * w + 1))) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_image_le) hcap0
  have hsmall' :
      (∑ ρ ∈ Finset.univ.filter (fun ρ : Restriction n => SwitchingCounting.stars ρ < s),
          pweight p ρ)
        + (∑ ρ ∈ Finset.univ.filter (fun ρ : Restriction n => F ≤ SwitchingCounting.stars ρ),
            pweight p ρ)
        + ((Gtot.image negDNF).card : ℚ)
            * (((2 * p / (1 - p)) * (4 * w + 1)) ^ s
                / (1 - (2 * p / (1 - p)) * (4 * w + 1))) < 1 := by
    linarith [hsmall, hmono]
  obtain ⟨ρ, _hge, hltF, hshallowNeg⟩ :=
    exists_survivor_shallow_findep hp0 hp3 (Gtot.image negDNF) hcons' hnd' hw' hr' hsmall'
  have hshallow : ∀ G ∈ gates, ∀ g ∈ G, (canonicalDTree (negDNF g) w F ρ).depth < s :=
    fun G hG g hg => hshallowNeg (negDNF g) (Finset.mem_image_of_mem negDNF (hsub G hG hg))
  have hnd2 : ∀ G ∈ gates, ∀ g ∈ G, ∀ C ∈ g, (C.lits.map litVarOf).Nodup :=
    fun G hG g hg C hC => hnd g (hsub G hG hg) C hC
  have hca := collapse_and_layer_at w F s gates ρ hltF hnd2 hshallow
  exact ⟨ρ, hca.1, hca.2.1⟩

end Layered

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.Layered.collapse_and_layer_findep
