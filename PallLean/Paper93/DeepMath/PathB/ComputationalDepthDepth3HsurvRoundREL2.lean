import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SurvivorExtendsREL2
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3HsurvRoundRel

/-!
# Tight switching, step 96: the two-parameter per-round survivor (depth/star decoupled) (branch `razborov-recoverRho-wip`)

The per-round survivor on the two-parameter budget (step 95).  The Chernoff **gap** is at the *star* threshold
`s` (`(stars τ)·p > 7·s` — the surviving count stays large), the **union bound** is at the independent *depth*
threshold `t` (`card · CAP^t/(1-CAP) < 1/2` — `t` small, so the rate is constant).  Together they discharge the
two-parameter relative budget (`exists_survivor_shallow_extends_REL2`), yielding a survivor `ρ` with `stars ρ ≥
s` (large) shallowing every bottom gate below `t` (small) in both polarities — `Shallows F ρ t C`.

* `hsurv_REL2_round` — one round's two-parameter survivor from the gap (at `s`) and the union bound (at `t`).

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

/-- **One round's two-parameter survivor.**  The gap at the star threshold `s` and the union bound at the depth
threshold `t` give a survivor `ρ` with `stars ρ ≥ s` shallowing every bottom gate below `t`. -/
theorem hsurv_REL2_round {p : ℚ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp3 : 3 * p ≤ 1)
    {w F s t m : ℕ} [NeZero w] [NeZero m] (hs : 2 ≤ s) (hF : n ≤ F)
    (C : Layered n) (τ : Fin n → Option Bool) (hbw : BottomWidth w C)
    (hmc : ∀ cs ∈ bottomGates C, cs.length ≤ m)
    (hr1 : (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ)) < 1)
    (hgap : 7 * (s : ℚ) < (SwitchingCounting.stars τ : ℚ) * p)
    (hh2 : ((bottomGatesG C).card : ℚ)
        * (((2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ))) ^ t
            / (1 - (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ)))) < 1 / 2) :
    ∃ ρ : Fin n → Option Bool, Extends τ ρ ∧ s ≤ SwitchingCounting.stars ρ ∧
      SwitchingCounting.stars ρ ≤ F ∧ Shallows F ρ t C := by
  have hp_lt : p < 1 := by linarith
  have hsq : (1 : ℚ) < (s : ℚ) := by exact_mod_cast (by omega : 1 < s)
  set u : ℚ := 1 - 1 / (s : ℚ) with hu
  have h1s : 1 / (s : ℚ) < 1 := by rw [div_lt_one (by positivity)]; exact hsq
  have hu0 : 0 < u := by rw [hu]; linarith
  have h0s : (0 : ℚ) ≤ 1 / (s : ℚ) := by positivity
  have hu1 : u ≤ 1 := by rw [hu]; linarith
  set capt : ℚ := ((2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ))) ^ t
    / (1 - (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ))) with hcaptd
  set box : ℚ := ((1 - p) / 2) ^ (n - SwitchingCounting.stars τ) with hboxd
  have hbox0 : 0 < box := by rw [hboxd]; exact pow_pos (by linarith) _
  have hh2box : ((bottomGatesG C).card : ℚ) * (capt * box) < box / 2 := by
    rw [show ((bottomGatesG C).card : ℚ) * (capt * box)
          = (((bottomGatesG C).card : ℚ) * capt) * box by ring,
        show box / 2 = (1 / 2) * box by ring]
    exact mul_lt_mul_of_pos_right hh2 hbox0
  have hsmall : (∑ σ ∈ (extBox τ).filter (fun σ => SwitchingCounting.stars σ < s), pweight p σ)
      + ((bottomGatesG C).card : ℚ) * (capt * box) < box :=
    hsmall_of_chernoff hu0 hu1 hp0 hp1 (by omega) τ (((bottomGatesG C).card : ℚ) * (capt * box))
      (hcf_of_split hp_lt ((bottomGatesG C).card : ℚ) (capt * box)
        (h1_of_gap hp0 hp1 (SwitchingCounting.stars τ) s (by omega) hgap) hh2box)
  obtain ⟨ρ, hext, hge, hle, hsh⟩ :=
    exists_survivor_shallow_extends_REL2 hp0 hp3 hF τ (bottomGatesG C)
      (by intro g hg T hT
          rcases mem_bottomGatesG.mp hg with h | ⟨cs, hcs, rfl⟩
          · exact hbw g h T hT
          · rw [negDNF, List.mem_map] at hT
            obtain ⟨S, hS, rfl⟩ := hT
            simpa using hbw cs hcs S hS)
      (by intro g hg
          rcases mem_bottomGatesG.mp hg with h | ⟨cs, hcs, rfl⟩
          · exact hmc g h
          · rw [negDNF, List.length_map]; exact hmc cs hcs)
      hr1 hsmall
  refine ⟨ρ, hext, hge, hle, ?_⟩
  intro cs hcs
  exact ⟨hsh cs (mem_bottomGatesG.mpr (Or.inl hcs)),
    hsh (negDNF cs) (mem_bottomGatesG.mpr (Or.inr ⟨cs, hcs, rfl⟩))⟩

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.hsurv_REL2_round
