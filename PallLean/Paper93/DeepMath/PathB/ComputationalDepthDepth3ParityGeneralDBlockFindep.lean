import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ParityWidthAwareBlockClean
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3HsurvBlockRound

/-!
# Block-DT model, route-2 step [170d]: the m-free general-`d` parity bound — `hsurv` discharged

The assembly of [170b] and [170c]: the per-round block survivor `hsurv` of the clean width-aware tower
[170b] is discharged by the m-free per-round survivor [170c].  What remains is the **single schedule
hypothesis** `hsched` — the per-base budget that, for every reachable clean width-`≤ w` tower `C` and
base `τ` with `s ≤ stars τ`, keeps the m-free deep-cap below the surviving mass.

* `parity_not_altO_block_findep` — a depth-`(d+2)` alternating, width-`≤ w`, `BottomClean` tower does
  not compute parity, given only the uniform schedule budget `hsched`.  Everything else (the entire
  m-free depth-`d` machinery) is now built; `hsched` is the sole remaining analytic input ([171]).

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

/-- **The m-free general-`d` parity lower bound, `hsurv` discharged.**  Only the uniform per-base
schedule budget `hsched` remains.  The deep-cap is the m-free geometric `(r')^s/(1-r')`,
`r' = (2p/(1-p))(4w+1)` — no clause-count `m`, no `canonicalDT ↔ canonicalDTree` bridge. -/
theorem parity_not_altO_block_findep {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    (s w F d : ℕ) [NeZero w] (hsw : s ≤ w) (hs : 1 ≤ s) (hF : n < F)
    (hr' : (2 * p / (1 - p)) * (4 * w + 1) < 1)
    (C₀ : Layered n) (τ₀ : Fin n → Option Bool)
    (hC₀ : AltO (d + 2) C₀) (hbw₀ : BottomWidth w C₀) (hcl₀ : BottomClean C₀)
    (hτ₀ : s ≤ SwitchingCounting.stars τ₀)
    (hsched : ∀ (C : Layered n) (τ : Fin n → Option Bool), BottomWidth w C → BottomClean C →
        s ≤ SwitchingCounting.stars τ →
        (∑ σ ∈ (extBox τ).filter (fun σ => SwitchingCounting.stars σ ≤ s - 1), pweight p σ)
          + ((bottomGatesG C).card : ℚ)
              * ((((2 * p / (1 - p)) * (4 * w + 1)) ^ s
                    / (1 - (2 * p / (1 - p)) * (4 * w + 1)))
                  * ((1 - p) / 2) ^ (n - SwitchingCounting.stars τ))
        < ((1 - p) / 2) ^ (n - SwitchingCounting.stars τ)) :
    ∃ x : Fin n → Bool, eval C₀ x ≠ DTree.parity x :=
  parity_not_altO_block_width_aware_clean s w F d hsw C₀ τ₀ hC₀ hbw₀ hcl₀ hτ₀
    (fun C τ hbw hcl hst =>
      hsurv_block_round hp0 hp3 hs hF C τ hbw hcl hr' (hsched C τ hbw hcl hst))

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.parity_not_altO_block_findep
