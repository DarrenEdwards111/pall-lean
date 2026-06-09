import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3HsurvBlockRound
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3HsmallChernoff
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3HcfSplit
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3H1Assemble

/-!
# Block-DT model, route-2 step [171b]: the two-threshold m-free block survivor (gap + union)

The block twin of `hsurv_REL2_round`: the per-round survivor with the budget reduced to two clean
conditions — the Chernoff **gap** at the (output) star threshold `sOut` (`7·sOut < stars τ · p`, so the
surviving count stays large) and the **union bound** at the depth threshold `sOut`
(`card · (r')^sOut/(1-r') < 1/2`, the m-free deep cap).  The decreasing schedule keeps
`stars τ ≫ sOut`, so the gap holds; together they discharge the per-base budget of [170c].

* `hsurv_block_REL2_round` — from `BottomWidth`, `BottomClean`, the gap and the union bound, the m-free
  survivor `ρ` with `sOut ≤ stars ρ < F` shallowing every bottom gate below `sOut` (`ShallowsBlock`).

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

/-- **One round's two-threshold m-free block survivor.**  The Chernoff gap at `sOut` and the union
bound at depth `sOut` give a survivor `ρ` with `stars ρ ≥ sOut` shallowing every bottom gate below
`sOut` in the block tree (both polarities). -/
theorem hsurv_block_REL2_round {p : ℚ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp3 : 3 * p ≤ 1)
    {w F sOut : ℕ} [NeZero w] (hsOut : 2 ≤ sOut) (hF : n < F)
    (C : Layered n) (τ : Fin n → Option Bool) (hbw : BottomWidth w C) (hcl : BottomClean C)
    (hr' : (2 * p / (1 - p)) * (4 * w + 1) < 1)
    (hgap : 7 * (sOut : ℚ) < (SwitchingCounting.stars τ : ℚ) * p)
    (hunion : ((bottomGatesG C).card : ℚ)
        * (((2 * p / (1 - p)) * (4 * w + 1)) ^ sOut
            / (1 - (2 * p / (1 - p)) * (4 * w + 1))) < 1 / 2) :
    ∃ ρ : Fin n → Option Bool, Extends τ ρ ∧ sOut ≤ SwitchingCounting.stars ρ ∧
      SwitchingCounting.stars ρ < F ∧ ShallowsBlock w F ρ sOut C := by
  have hp_lt : p < 1 := by linarith
  have hsq : (1 : ℚ) < (sOut : ℚ) := by exact_mod_cast (by omega : 1 < sOut)
  set u : ℚ := 1 - 1 / (sOut : ℚ) with hu
  have h1s : 1 / (sOut : ℚ) < 1 := by rw [div_lt_one (by positivity)]; exact hsq
  have hu0 : 0 < u := by rw [hu]; linarith
  have h0s : (0 : ℚ) ≤ 1 / (sOut : ℚ) := by positivity
  have hu1 : u ≤ 1 := by rw [hu]; linarith
  set geom : ℚ := ((2 * p / (1 - p)) * (4 * w + 1)) ^ sOut
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
  exact hsurv_block_round hp0 hp3 (by omega) hF C τ hbw hcl hr' hsmall

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.hsurv_block_REL2_round
