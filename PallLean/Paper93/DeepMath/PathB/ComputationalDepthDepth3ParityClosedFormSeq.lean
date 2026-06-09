import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ParityWidthAwareSeq
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3HsurvRound

/-!
# Tight switching, step 66: the per-round-threshold parity bound as one closed-form inequality (branch `razborov-recoverRho-wip`)

The Håstad-regime culmination.  Wiring the per-round survivor `hsurv_round` (step 62, at output threshold
`s (i+1)`) into the two-threshold capstone (step 65) discharges the per-round survivor `hsurv` entirely: the
general-`d` `parity ∉ AC⁰` with a *decreasing* threshold sequence rests on nothing but the rate (`hr1`), a
clause-count bound `m`, and the **single closed-form Chernoff inequality** at every reachable tower — now with
the budget over the *current* `stars τ = s i` and the shallowness at the *next* `s (i+1)`, the split that lets
the Chernoff term `(t·p+(1-p))^(stars τ)/t^(s (i+1) - 1)` be small when `s i ≫ s (i+1)`.

* `parity_not_altO_closed_form_seq` — the per-round-threshold parity bound from one closed-form inequality.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

/-- **The per-round-threshold general-`d` parity bound as one closed-form inequality.**  A depth-`(d+2)`
alternating tower of bottom width `≤ w` does not compute parity, given the rate, a clause-count bound `m`, a
decreasing threshold sequence `s` below `w`, and the closed-form Chernoff inequality `hcf` at every reachable
tower (budget over the input count `s i`, shallowness at the output `s (i+1)`). -/
theorem parity_not_altO_closed_form_seq {p t : ℚ}
    (ht0 : 0 < t) (ht1 : t ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp3 : 3 * p ≤ 1)
    {w F m : ℕ} (s : ℕ → ℕ) (d : ℕ) [NeZero w] [NeZero m]
    (hmono : ∀ i, s (i + 1) ≤ s i) (hs1 : ∀ i, 1 ≤ s (i + 1)) (hsw : ∀ i, s (i + 1) ≤ w)
    (hF : n ≤ F) (C₀ : Layered n) (τ₀ : Fin n → Option Bool)
    (hC₀ : AltO (d + 2) C₀) (hbw₀ : BottomWidth w C₀) (hτ₀ : s 0 ≤ SwitchingCounting.stars τ₀)
    (hr1 : (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ)) < 1)
    (hcount : ∀ C : Layered n, BottomWidth w C → ∀ cs ∈ bottomGates C, cs.length ≤ m)
    (hcf : ∀ (i : ℕ) (C : Layered n) (τ : Fin n → Option Bool), BottomWidth w C →
        s i ≤ SwitchingCounting.stars τ →
        ((1 - p) / 2) ^ (n - SwitchingCounting.stars τ)
            * (t * p + (1 - p)) ^ (SwitchingCounting.stars τ) / t ^ (s (i + 1) - 1)
          + ((bottomGatesG C).card : ℚ)
              * (((2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ))) ^ (s (i + 1))
                  / (1 - (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ))))
        < ((1 - p) / 2) ^ (n - SwitchingCounting.stars τ)) :
    ∃ x : Fin n → Bool, eval C₀ x ≠ DTree.parity x :=
  parity_not_altO_width_aware_seq s w F d hmono hsw C₀ τ₀ hC₀ hbw₀ hτ₀
    (fun i C τ hbw hsurvτ =>
      hsurv_round ht0 ht1 hp0 hp1 hp3 (hs1 i) hF C τ hbw
        (le_trans (hmono i) hsurvτ) (hcount C hbw) hr1 (hcf i C τ hbw hsurvτ))

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.parity_not_altO_closed_form_seq
