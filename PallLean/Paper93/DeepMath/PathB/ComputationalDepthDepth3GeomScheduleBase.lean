import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3GeomSchedule

/-!
# Tight switching, step 73: the base-`D` geometric schedule (the `p`-factor fix) (branch `razborov-recoverRho-wip`)

The halving schedule (step 68) used the wrong contraction factor: the Chernoff gap (step 71) needs the next
threshold below the mean, `s_{i+1} < (stars τ)·p/7 ≈ s_i·p/7`, so the survivor count must shrink by a factor
`~p = 1/(8wm)` per round, not `1/2`.  Generalising the schedule to an arbitrary integer base `D`,
`geomSchedB D N i = max 1 (N / D^i)`, lets the contraction match: with `D > 7/p = 56wm` the gap holds (modulo
flooring).  The structural facts (antitone, `≥ 1`, starts at `N`) carry over verbatim from the base-`2` case.

* `geomSchedB` — the base-`D` schedule (`geomSched = geomSchedB 2`).
* `geomSchedB_anti` / `geomSchedB_pos` / `geomSchedB_zero` — its structural facts.
* `parity_not_altO_geomB` — the general-`d` parity bound at the base-`D` schedule.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

/-- The base-`D` survivor-threshold schedule: `N`, `N/D`, `N/D²`, …, floored at `1`. -/
def geomSchedB (D N i : ℕ) : ℕ := max 1 (N / D ^ i)

theorem geomSchedB_anti (D N : ℕ) (hD : 1 ≤ D) {a b : ℕ} (hab : a ≤ b) :
    geomSchedB D N b ≤ geomSchedB D N a := by
  apply max_le_max (le_refl 1)
  exact Nat.div_le_div_left (Nat.pow_le_pow_right hD hab) (by positivity)

theorem geomSchedB_pos (D N i : ℕ) : 1 ≤ geomSchedB D N i := le_max_left _ _

theorem geomSchedB_zero (D N : ℕ) (hN : 1 ≤ N) : geomSchedB D N 0 = N := by
  rw [geomSchedB, pow_zero, Nat.div_one, max_eq_right hN]

/-- **The general-`d` parity lower bound at the base-`D` geometric schedule.**  Identical to `parity_not_altO
_geom` (step 68) but with the contraction base `D ≥ 1`, so the Chernoff gap can be met with `D > 56wm`. -/
theorem parity_not_altO_geomB {p t : ℚ}
    (ht0 : 0 < t) (ht1 : t ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp3 : 3 * p ≤ 1)
    {F m D N : ℕ} (d : ℕ) [NeZero m] (hD : 1 ≤ D) (hN : 1 ≤ N) (hF : n ≤ F)
    (C₀ : Layered n) (τ₀ : Fin n → Option Bool) (hC₀ : AltO (d + 2) C₀)
    (hbw₀ : BottomWidth (geomSchedB D N 1) C₀) (hτ₀ : N ≤ SwitchingCounting.stars τ₀)
    (hr1 : (2 * p / (1 - p)) * (2 * ((geomSchedB D N 1 : ℕ) : ℚ) * (m : ℚ)) < 1)
    (hcount : ∀ C : Layered n, BottomWidth (geomSchedB D N 1) C →
        ∀ cs ∈ bottomGates C, cs.length ≤ m)
    (hcf : ∀ (i : ℕ) (C : Layered n) (τ : Fin n → Option Bool), BottomWidth (geomSchedB D N 1) C →
        geomSchedB D N i ≤ SwitchingCounting.stars τ →
        ((1 - p) / 2) ^ (n - SwitchingCounting.stars τ)
            * (t * p + (1 - p)) ^ (SwitchingCounting.stars τ) / t ^ (geomSchedB D N (i + 1) - 1)
          + ((bottomGatesG C).card : ℚ)
              * (((2 * p / (1 - p)) * (2 * ((geomSchedB D N 1 : ℕ) : ℚ) * (m : ℚ))) ^ (geomSchedB D N (i + 1))
                  / (1 - (2 * p / (1 - p)) * (2 * ((geomSchedB D N 1 : ℕ) : ℚ) * (m : ℚ))))
        < ((1 - p) / 2) ^ (n - SwitchingCounting.stars τ)) :
    ∃ x : Fin n → Bool, eval C₀ x ≠ DTree.parity x := by
  haveI : NeZero (geomSchedB D N 1) := ⟨(lt_of_lt_of_le one_pos (geomSchedB_pos D N 1)).ne'⟩
  refine parity_not_altO_closed_form_seq ht0 ht1 hp0 hp1 hp3 (geomSchedB D N) d
    (fun i => geomSchedB_anti D N hD (Nat.le_succ i)) (fun i => geomSchedB_pos D N (i + 1))
    (fun i => geomSchedB_anti D N hD (by omega : 1 ≤ i + 1)) hF C₀ τ₀ hC₀ hbw₀ ?_ hr1 hcount hcf
  rw [geomSchedB_zero D N hN]; exact hτ₀

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.parity_not_altO_geomB
