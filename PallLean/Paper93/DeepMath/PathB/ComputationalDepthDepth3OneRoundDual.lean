import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SurvivorChernoff
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3GateCollapse
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3LayerCollapseWF

/-!
# AC⁰ reduction, foundation 38: the dual concrete round (branch only)

The depth-`3 → 2` round at `p=1/5, t=1/2`: an `OR` of `CNF` gates collapses to a single `DNF`, on a
restriction extending `τ` with the survivors kept above `k`.  Dual to `one_round_exists_p_fifth_dim`
(brick 36): the switching is run on the *negated* gates (De Morgan), so the concrete one-round step is
applied to `Cs.toFinset.image negDNF`, whose switching hypotheses are inherited from the `CNF`s' via
`consistent_negClause` / `litVarOf_negLit`.  The output `DNF`'s terms are again `Consistent` with distinct
variables (the negated canonical tree is fresh, bricks 15/18), so it feeds the next round / the terminal
step.

* `one_round_dual_p_fifth` — `gOr (Cs.map cnf)` `EquivOn ρ` a single `DNF`, `Extends τ ρ`, `k < stars ρ`,
  well-formed output, from the size + dimension conditions.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered Classical

variable {n : ℕ}

/-- **The dual concrete round.**  At `p=1/5, t=1/2`, an `OR` of `CNF` gates `Cs` collapses to a single
`DNF` on a restriction extending `τ` with `k < stars ρ`, the output terms well-formed. -/
theorem one_round_dual_p_fifth (w F s k : ℕ) (hF : n < F)
    (τ : Fin n → Option Bool) (Cs : List (List (Clause n)))
    (hcons : ∀ c ∈ Cs, ∀ C ∈ c, Consistent C)
    (hnd : ∀ c ∈ Cs, ∀ C ∈ c, (C.lits.map litVarOf).Nodup)
    (hw : ∀ c ∈ Cs, ∀ C ∈ c, C.lits.length ≤ w)
    (hdeep : 2 * ((Cs.toFinset.image negDNF).card
        * Fintype.card (Fin F → Option (Fin w → Option (Option Bool)))) < 2 ^ s)
    (hdim : 7 * (k + 1) ≤ stars τ) :
    ∃ ρ : Fin n → Option Bool,
      Extends τ ρ
        ∧ EquivOn ρ (gOr (Cs.map cnf))
            (dnf (Cs.flatMap (fun c =>
              dtreeToDNF (DTree.negTree (canonicalDTree (negDNF c) w F ρ)))))
        ∧ k < stars ρ
        ∧ (∀ T ∈ Cs.flatMap (fun c =>
              dtreeToDNF (DTree.negTree (canonicalDTree (negDNF c) w F ρ))), T.lits.length < s)
        ∧ (∀ T ∈ Cs.flatMap (fun c =>
              dtreeToDNF (DTree.negTree (canonicalDTree (negDNF c) w F ρ))),
            Consistent T ∧ (T.lits.map litVarOf).Nodup) := by
  classical
  -- the negated gate set inherits the switching hypotheses (De Morgan, brick 75)
  have hcons' : ∀ g ∈ Cs.toFinset.image negDNF, ∀ T ∈ g, Consistent T := by
    intro g hg T hT
    rw [Finset.mem_image] at hg
    obtain ⟨c0, hc0, rfl⟩ := hg
    rw [negDNF, List.mem_map] at hT
    obtain ⟨C, hC, rfl⟩ := hT
    exact consistent_negClause (hcons c0 (List.mem_toFinset.mp hc0) C hC)
  have hnd' : ∀ g ∈ Cs.toFinset.image negDNF, ∀ T ∈ g, (T.lits.map litVarOf).Nodup := by
    intro g hg T hT
    rw [Finset.mem_image] at hg
    obtain ⟨c0, hc0, rfl⟩ := hg
    rw [negDNF, List.mem_map] at hT
    obtain ⟨C, hC, rfl⟩ := hT
    have hmap : (C.lits.map negLit).map litVarOf = C.lits.map litVarOf := by
      rw [List.map_map]; exact List.map_congr_left (fun ℓ _ => litVarOf_negLit ℓ)
    simpa [hmap] using hnd c0 (List.mem_toFinset.mp hc0) C hC
  have hw' : ∀ g ∈ Cs.toFinset.image negDNF, ∀ T ∈ g, T.lits.length ≤ w := by
    intro g hg T hT
    rw [Finset.mem_image] at hg
    obtain ⟨c0, hc0, rfl⟩ := hg
    rw [negDNF, List.mem_map] at hT
    obtain ⟨C, hC, rfl⟩ := hT
    simpa using hw c0 (List.mem_toFinset.mp hc0) C hC
  obtain ⟨ρ, hext, hshallowG, hstars⟩ :=
    one_round_exists_p_fifth_dim w F s k τ (Cs.toFinset.image negDNF) hcons' hnd' hw' hdeep hdim
  have hshallow : ∀ c ∈ Cs, (canonicalDTree (negDNF c) w F ρ).depth < s :=
    fun c hc => hshallowG (negDNF c)
      (Finset.mem_image_of_mem negDNF (List.mem_toFinset.mpr hc))
  have hstarsF : stars ρ < F :=
    lt_of_le_of_lt (by rw [stars]; exact le_trans (Finset.card_le_univ _) (by simp)) hF
  obtain ⟨heq, hwidth⟩ := collapse_gOr_cnf_at w F s Cs ρ hstarsF hshallow
  refine ⟨ρ, hext, heq, hstars, hwidth, ?_⟩
  intro T hT
  rw [List.mem_flatMap] at hT
  obtain ⟨c, hc, hTc⟩ := hT
  have hndneg : ∀ C ∈ negDNF c, (C.lits.map litVarOf).Nodup := by
    intro C hC
    rw [negDNF, List.mem_map] at hC
    obtain ⟨C0, hC0, rfl⟩ := hC
    have hmap : (C0.lits.map negLit).map litVarOf = C0.lits.map litVarOf := by
      rw [List.map_map]; exact List.map_congr_left (fun ℓ _ => litVarOf_negLit ℓ)
    simpa [hmap] using hnd c hc C0 hC0
  have hfresh := DTree.negTree_fresh _ (canonicalDTree_fresh (negDNF c) w hndneg F ρ)
  exact ⟨dtreeToDNF_consistent _ hfresh T hTc, dtreeToDNF_nodup _ hfresh T hTc⟩

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.one_round_dual_p_fifth
