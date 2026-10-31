import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3OneRoundFindep
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseRoundBlockBounded
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseRoundBlockClean
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3HsurvDischarge

/-!
# Block-DT model, route-2 step [170c]: the m-free per-round BLOCK survivor (discharges `hsurv`)

The block twin of `hsurv_REL2_round`: one round's m-free survivor, discharging the `hsurv` hypothesis
of `parity_not_altO_block_width_aware_clean` [170b].  Apply the m-free conditional survivor [164] to
`bottomGatesG C` (which already bundles **both polarities** — every bottom gate and its `negDNF`), so
the resulting `ρ` shallows each in the block tree, i.e. `ShallowsBlock w F ρ s C`.

The injectivity hypotheses of [164] (`Consistent` + variable-`Nodup`) are exactly what `BottomClean C`
[170a/b] supplies — extended to the negated polarity by `consistent_negClause` / `litVarOf_negLit`; the
width `≤ w` comes from `BottomWidth w C` (negation preserves clause length).  The only remaining input
is the per-base budget `hsmall` (the schedule, [170d]).

* `hsurv_block_round` — from `BottomWidth`, `BottomClean`, `s ≤ stars τ`, and the per-base budget, a
  survivor `ρ` extending `τ` with `s ≤ stars ρ < F` and `ShallowsBlock w F ρ s C`.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

/-- **One round's m-free block survivor.**  Discharges `hsurv` of [170b]: from `BottomClean` (the
injectivity data) + `BottomWidth` and the per-base budget on `bottomGatesG C`, the m-free survivor
[164] gives `ρ` shallowing every bottom gate (both polarities) below `s`, i.e. `ShallowsBlock`. -/
theorem hsurv_block_round {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    {w F s : ℕ} [NeZero w] (hs : 1 ≤ s) (hF : n < F)
    (C : Layered n) (τ : Fin n → Option Bool) (hbw : BottomWidth w C) (hcl : BottomClean C)
    (hr' : (2 * p / (1 - p)) * (4 * w + 1) < 1)
    (hsmall :
        (∑ σ ∈ (extBox τ).filter (fun σ => SwitchingCounting.stars σ ≤ s - 1), pweight p σ)
          + ((bottomGatesG C).card : ℚ)
              * ((((2 * p / (1 - p)) * (4 * w + 1)) ^ s
                    / (1 - (2 * p / (1 - p)) * (4 * w + 1)))
                  * ((1 - p) / 2) ^ (n - SwitchingCounting.stars τ))
        < ((1 - p) / 2) ^ (n - SwitchingCounting.stars τ)) :
    ∃ ρ : Fin n → Option Bool, Extends τ ρ ∧ s ≤ SwitchingCounting.stars ρ ∧
      SwitchingCounting.stars ρ < F ∧ ShallowsBlock w F ρ s C := by
  obtain ⟨ρ, hext, hshallow, hk⟩ :=
    exists_shallow_survivor_extends_findep hp0 hp3 F s (s - 1) τ (bottomGatesG C)
      (by intro g hg T hT
          rcases mem_bottomGatesG.mp hg with h | ⟨cs, hcs, rfl⟩
          · exact hcl.1 g h T hT
          · rw [negDNF, List.mem_map] at hT
            obtain ⟨C0, hC0, rfl⟩ := hT
            exact consistent_negClause (hcl.1 cs hcs C0 hC0))
      (by intro g hg T hT
          rcases mem_bottomGatesG.mp hg with h | ⟨cs, hcs, rfl⟩
          · exact hcl.2 g h T hT
          · rw [negDNF, List.mem_map] at hT
            obtain ⟨C0, hC0, rfl⟩ := hT
            have hmap : (C0.lits.map negLit).map litVarOf = C0.lits.map litVarOf := by
              rw [List.map_map]; exact List.map_congr_left (fun ℓ _ => litVarOf_negLit ℓ)
            simpa [hmap] using hcl.2 cs hcs C0 hC0)
      (by intro g hg T hT
          rcases mem_bottomGatesG.mp hg with h | ⟨cs, hcs, rfl⟩
          · exact hbw g h T hT
          · rw [negDNF, List.mem_map] at hT
            obtain ⟨C0, hC0, rfl⟩ := hT
            simpa using hbw cs hcs C0 hC0)
      hr' hsmall
  have hsρ : s ≤ SwitchingCounting.stars ρ := by omega
  have hltF : SwitchingCounting.stars ρ < F :=
    lt_of_le_of_lt (by rw [stars]; exact le_trans (Finset.card_le_univ _) (by simp)) hF
  refine ⟨ρ, hext, hsρ, hltF, ?_⟩
  intro cs hcs
  exact ⟨hshallow cs (mem_bottomGatesG.mpr (Or.inl hcs)),
    hshallow (negDNF cs) (mem_bottomGatesG.mpr (Or.inr ⟨cs, hcs, rfl⟩))⟩

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.hsurv_block_round
