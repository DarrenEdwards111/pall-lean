import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3HsurvDischarge
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3HsmallChernoff

/-!
# Tight switching, step 62: one round's survivor from one closed-form inequality (branch `razborov-recoverRho-wip`)

The per-round survivor packaged as a single composition: `hsurv_of_budget` (step 60) consumes the survivor
budget `hsmall`, and `hsmall_of_chernoff` (step 61) supplies it from a closed-form Chernoff inequality.  So a
survivor `ρ` shallowing every bottom gate of `C` (`Shallows F ρ s C`) exists as soon as the single explicit
inequality `hcf` holds — no sums, no budgets, just the rate `hr1` and the closed-form tail/cap split.

* `hsurv_round` — `Shallows F ρ s C` from the rate and one closed-form inequality.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

/-- **One round's survivor from one closed-form inequality.**  Given the rate (`hp0`/`hp1`/`hp3`/`hr1`), a
clause-count bound `m` on the bottoms, and the single closed-form Chernoff inequality `hcf` (the conditional
low-star tail plus the deep-gate cap term, below the box mass), there is a survivor `ρ` extending `τ` that
keeps `s ≤ stars ρ ≤ F` and shallows every bottom gate of `C` below `s`. -/
theorem hsurv_round {p t : ℚ} (ht0 : 0 < t) (ht1 : t ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp3 : 3 * p ≤ 1)
    {w F s m : ℕ} [NeZero w] [NeZero m] (hs : 1 ≤ s) (hF : n ≤ F)
    (C : Layered n) (τ : Fin n → Option Bool) (hbw : BottomWidth w C)
    (hτ : s ≤ SwitchingCounting.stars τ) (hm : ∀ cs ∈ bottomGates C, cs.length ≤ m)
    (hr1 : (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ)) < 1)
    (hcf :
        ((1 - p) / 2) ^ (n - SwitchingCounting.stars τ)
            * (t * p + (1 - p)) ^ (SwitchingCounting.stars τ) / t ^ (s - 1)
          + ((bottomGatesG C).card : ℚ)
              * (((2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ))) ^ s
                  / (1 - (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ))))
        < ((1 - p) / 2) ^ (n - SwitchingCounting.stars τ)) :
    ∃ ρ : Fin n → Option Bool, Extends τ ρ ∧ s ≤ SwitchingCounting.stars ρ ∧
      SwitchingCounting.stars ρ ≤ F ∧ Shallows F ρ s C :=
  hsurv_of_budget hp0 hp3 hF C τ hbw hτ hm hr1
    (hsmall_of_chernoff ht0 ht1 hp0 hp1 hs τ
      (((bottomGatesG C).card : ℚ)
        * (((2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ))) ^ s
            / (1 - (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ))))) hcf)

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.hsurv_round
