import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3OneRoundFindep
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseRoundBlockBounded
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseRoundBlockClean
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3HsurvDischarge
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3HsmallChernoff
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3HcfSplit
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3H1Assemble

/-!
# Block-DT model, route-2 step [171b′]: the TWO-PARAMETER m-free block survivor (depth ⟂ star)

The decoupled survivor — the fix for the depth/star conflation of [171b].  A *small* depth threshold
`t` (controls the bottom width `≤ t` and the union exponent `(r')^t`) is kept **separate** from a
*large* star threshold `sOut` (controls the Chernoff gap `7·sOut < stars τ · p`).  The m-free survivor
[164] `exists_shallow_survivor_extends_findep (F t (sOut-1))` already takes these as separate
parameters (depth `t`, star `sOut-1`); here we feed it the budget assembled from the two independent
conditions, getting `stars ρ ≥ sOut` (large) while `ShallowsBlock w F ρ t C` (depth `< t`, small).

* `hsurv_block_REL2_round_dt` — from `BottomWidth`, `BottomClean`, the star gap (`sOut`) and the depth
  union bound (`t`), an m-free survivor `ρ` with `sOut ≤ stars ρ < F` shallowing every bottom gate
  below the depth threshold `t` (both polarities).

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

/-- **One round's two-parameter (depth ⟂ star) m-free block survivor.**  The Chernoff gap at the star
threshold `sOut` and the union bound at the depth threshold `t` give a survivor `ρ` with
`stars ρ ≥ sOut` (large) shallowing every bottom gate below `t` (small) in the block tree. -/
theorem hsurv_block_REL2_round_dt {p : ℚ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp3 : 3 * p ≤ 1)
    {w F t sOut : ℕ} [NeZero w] (hsOut : 2 ≤ sOut) (hF : n < F)
    (C : Layered n) (τ : Fin n → Option Bool) (hbw : BottomWidth w C) (hcl : BottomClean C)
    (hr' : (2 * p / (1 - p)) * (4 * w + 1) < 1)
    (hgap : 7 * (sOut : ℚ) < (SwitchingCounting.stars τ : ℚ) * p)
    (hunion : ((bottomGatesG C).card : ℚ)
        * (((2 * p / (1 - p)) * (4 * w + 1)) ^ t
            / (1 - (2 * p / (1 - p)) * (4 * w + 1))) < 1 / 2) :
    ∃ ρ : Fin n → Option Bool, Extends τ ρ ∧ sOut ≤ SwitchingCounting.stars ρ ∧
      SwitchingCounting.stars ρ < F ∧ ShallowsBlock w F ρ t C := by
  have hp_lt : p < 1 := by linarith
  have hsq : (1 : ℚ) < (sOut : ℚ) := by exact_mod_cast (by omega : 1 < sOut)
  set u : ℚ := 1 - 1 / (sOut : ℚ) with hu
  have h1s : 1 / (sOut : ℚ) < 1 := by rw [div_lt_one (by positivity)]; exact hsq
  have hu0 : 0 < u := by rw [hu]; linarith
  have h0s : (0 : ℚ) ≤ 1 / (sOut : ℚ) := by positivity
  have hu1 : u ≤ 1 := by rw [hu]; linarith
  set geom : ℚ := ((2 * p / (1 - p)) * (4 * w + 1)) ^ t
    / (1 - (2 * p / (1 - p)) * (4 * w + 1)) with hgeomd
  set box : ℚ := ((1 - p) / 2) ^ (n - SwitchingCounting.stars τ) with hboxd
  have hbox0 : 0 < box := by rw [hboxd]; exact pow_pos (by linarith) _
  have hh2box : ((bottomGatesG C).card : ℚ) * (geom * box) < box / 2 := by
    rw [show ((bottomGatesG C).card : ℚ) * (geom * box)
          = (((bottomGatesG C).card : ℚ) * geom) * box by ring,
        show box / 2 = (1 / 2) * box by ring]
    exact mul_lt_mul_of_pos_right hunion hbox0
  have hsmall : (∑ σ ∈ (extBox τ).filter (fun σ => SwitchingCounting.stars σ < sOut), pweight p σ)
      + ((bottomGatesG C).card : ℚ) * (geom * box) < box :=
    hsmall_of_chernoff hu0 hu1 hp0 hp1 (by omega) τ (((bottomGatesG C).card : ℚ) * (geom * box))
      (hcf_of_split hp_lt ((bottomGatesG C).card : ℚ) (geom * box)
        (h1_of_gap hp0 hp1 (SwitchingCounting.stars τ) sOut (by omega) hgap) hh2box)
  rw [show (extBox τ).filter (fun σ => SwitchingCounting.stars σ < sOut)
        = (extBox τ).filter (fun σ => SwitchingCounting.stars σ ≤ sOut - 1) from by
      apply Finset.filter_congr; intro σ _; omega] at hsmall
  -- apply [164] with depth threshold `t` and star threshold `sOut - 1`
  obtain ⟨ρ, hext, hshallow, hk⟩ :=
    exists_shallow_survivor_extends_findep hp0 hp3 F t (sOut - 1) τ (bottomGatesG C)
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
  have hsρ : sOut ≤ SwitchingCounting.stars ρ := by omega
  have hltF : SwitchingCounting.stars ρ < F :=
    lt_of_le_of_lt (by rw [stars]; exact le_trans (Finset.card_le_univ _) (by simp)) hF
  refine ⟨ρ, hext, hsρ, hltF, ?_⟩
  intro cs hcs
  exact ⟨hshallow cs (mem_bottomGatesG.mpr (Or.inl hcs)),
    hshallow (negDNF cs) (mem_bottomGatesG.mpr (Or.inr ⟨cs, hcs, rfl⟩))⟩

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.hsurv_block_REL2_round_dt
