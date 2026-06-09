import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ParityWidthAwareBlockCleanSeq
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3HsurvBlockREL2

/-!
# Block-DT model, route-2 step [171c]: the m-free general-`d` block bound on a threshold schedule

The assembly of [171a] (per-round-threshold block tower) and [171b] (two-threshold survivor): the
survivor `hsurv` is discharged, reducing the whole m-free depth-`d` block bound to **two clean
schedule conditions**:

* `hgap` — the *pure* schedule gap `7·s(i+1) < s i · p` (a condition on the threshold sequence only).
  Combined with the round invariant `s i ≤ stars τ` it yields the Chernoff gap `7·s(i+1) < stars τ·p`.
* `hunion` — the per-round union bound `card(C) · (r')^{s(i+1)}/(1-r') < 1/2` (depends on the gate
  count of the reachable tower `C`).

* `parity_not_altO_block_seq_findep` — a depth-`(d+2)` alternating, width-`≤ w`, `BottomClean` tower
  on a decreasing threshold schedule `s` does not compute parity, given the schedule gap `hgap` and the
  per-round union bound `hunion`.

This is the m-free depth-`d` bound with the survivor fully internalised; what remains ([171d]) is a
concrete geometric schedule discharging `hgap`, a gate-count bound for `hunion`, and a numeric instance.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

/-- **The m-free general-`d` block parity bound on a threshold schedule.**  The per-round survivor is
discharged from the schedule gap `hgap` (pure) and the per-round union bound `hunion`. -/
theorem parity_not_altO_block_seq_findep {p : ℚ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp3 : 3 * p ≤ 1)
    (s : ℕ → ℕ) (w F d : ℕ) [NeZero w]
    (hmono : ∀ i, s (i + 1) ≤ s i) (hsw : ∀ i, s (i + 1) ≤ w) (hpos : ∀ i, 2 ≤ s (i + 1))
    (hF : n < F) (hr' : (2 * p / (1 - p)) * (4 * w + 1) < 1)
    (C₀ : Layered n) (τ₀ : Fin n → Option Bool) (hC₀ : AltO (d + 2) C₀)
    (hbw₀ : BottomWidth w C₀) (hcl₀ : BottomClean C₀) (hτ₀ : s 0 ≤ SwitchingCounting.stars τ₀)
    (hgap : ∀ i, 7 * (s (i + 1) : ℚ) < (s i : ℚ) * p)
    (hunion : ∀ (i : ℕ) (C : Layered n), BottomWidth w C → BottomClean C →
        ((bottomGatesG C).card : ℚ)
          * (((2 * p / (1 - p)) * (4 * w + 1)) ^ s (i + 1)
              / (1 - (2 * p / (1 - p)) * (4 * w + 1))) < 1 / 2) :
    ∃ x : Fin n → Bool, eval C₀ x ≠ DTree.parity x :=
  parity_not_altO_block_width_aware_clean_seq s w F d hmono hsw C₀ τ₀ hC₀ hbw₀ hcl₀ hτ₀
    (fun i C τ hbw hcl hst =>
      hsurv_block_REL2_round hp0 hp1 hp3 (hpos i) hF C τ hbw hcl hr'
        (lt_of_lt_of_le (hgap i)
          (mul_le_mul_of_nonneg_right (by exact_mod_cast hst) hp0))
        (hunion i C hbw hcl))

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.parity_not_altO_block_seq_findep
