import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ParityWidthAware
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3HsurvRound

/-!
# Tight switching, step 63: the general-`d` parity bound as one closed-form inequality (branch `razborov-recoverRho-wip`)

The culmination of the switching arc.  Wiring the per-round survivor `hsurv_round` (step 62) into the
width-aware capstone (step 59) discharges `hsurv` entirely: the general-`d` `parity ∉ AC⁰` rests on nothing
but the rate (`hr1`), a clause-count bound `m` on the bottoms, and the **single closed-form Chernoff
inequality** holding at every reachable tower.  No sums, no survivor existence, no `hround`/`hterm`, no
sockets — the whole multi-round switching collapse is reduced to one explicit rational inequality per round.

* `parity_not_altO_closed_form` — `AltO (d+2) C₀ ∧ BottomWidth w C₀ ⟹ ∃ x, eval C₀ x ≠ parity x`, given only
  the rate, the count bound, and the per-round closed-form inequality.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

/-- **The general-`d` parity lower bound as one closed-form inequality.**  A depth-`(d+2)` alternating tower
of bottom width `≤ w` does not compute parity, given the rate `hr1`, a clause-count bound `m` on every
reachable tower's bottoms, and the closed-form Chernoff inequality `hcf` at every reachable tower.  All survivor
existence, the terminal switch, and the per-round budgets are discharged. -/
theorem parity_not_altO_closed_form {p t : ℚ}
    (ht0 : 0 < t) (ht1 : t ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp3 : 3 * p ≤ 1)
    {w F s m d : ℕ} [NeZero w] [NeZero m] (hs : 1 ≤ s) (hsw : s ≤ w) (hF : n ≤ F)
    (C₀ : Layered n) (τ₀ : Fin n → Option Bool)
    (hC₀ : AltO (d + 2) C₀) (hbw₀ : BottomWidth w C₀) (hτ₀ : s ≤ SwitchingCounting.stars τ₀)
    (hr1 : (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ)) < 1)
    (hcount : ∀ C : Layered n, BottomWidth w C → ∀ cs ∈ bottomGates C, cs.length ≤ m)
    (hcf : ∀ (C : Layered n) (τ : Fin n → Option Bool), BottomWidth w C →
        s ≤ SwitchingCounting.stars τ →
        ((1 - p) / 2) ^ (n - SwitchingCounting.stars τ)
            * (t * p + (1 - p)) ^ (SwitchingCounting.stars τ) / t ^ (s - 1)
          + ((bottomGatesG C).card : ℚ)
              * (((2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ))) ^ s
                  / (1 - (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ))))
        < ((1 - p) / 2) ^ (n - SwitchingCounting.stars τ)) :
    ∃ x : Fin n → Bool, eval C₀ x ≠ DTree.parity x :=
  parity_not_altO_width_aware s w F d hsw C₀ τ₀ hC₀ hbw₀ hτ₀
    (fun C τ hbw hτ =>
      hsurv_round ht0 ht1 hp0 hp1 hp3 hs hF C τ hbw hτ (hcount C hbw) hr1 (hcf C τ hbw hτ))

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.parity_not_altO_closed_form
