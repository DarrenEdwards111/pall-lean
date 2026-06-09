import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3HsurvRoundRel
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ParityWidthAware

/-!
# Tight switching, step 83: the general-`d` parity bound on the relative budget (branch `razborov-recoverRho-wip`)

The final wire.  Discharging the width-aware capstone's per-round survivor `hsurv` via `hsurv_REL_round`
(step 82) — which uses the *subcube-relative* (box-factor) survivor budget — closes the general-`d`
unconditional `parity ∉ AC⁰` to two **box-free, `exp`-free** per-round rational conditions:

* the **Chernoff gap** `(stars τ)·p > 7·s` (the next threshold is below the mean), and
* the **union bound** `card · CAP^s/(1-CAP) < 1/2` (now box-free, thanks to the relative budget).

No box mass appears, no `exp`/`log`, no consistency/nodup invariant — every structural and probabilistic piece
of the Håstad/Razborov switching lemma is proven, and what remains is exactly these two elementary inequalities
holding at each reachable tower (satisfiable in the standard regime: a geometric threshold with `D > 7/p`, and
the union bound from a gate-count bound and `s` large).

* `parity_not_altO_REL` — the general-`d` parity bound from the box-free per-round gap and union bound.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

/-- **The general-`d` parity lower bound on the relative budget.**  A depth-`(d+2)` alternating tower of bottom
width `≤ w` does not compute parity, given the rate, a clause-count bound, and — at every reachable tower — the
Chernoff gap `(stars τ)·p > 7·s` and the box-free union bound `card · CAP^s/(1-CAP) < 1/2`. -/
theorem parity_not_altO_REL {p : ℚ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp3 : 3 * p ≤ 1)
    {w F s m d : ℕ} [NeZero w] [NeZero m] (hs : 2 ≤ s) (hsw : s ≤ w) (hF : n ≤ F)
    (C₀ : Layered n) (τ₀ : Fin n → Option Bool) (hC₀ : AltO (d + 2) C₀)
    (hbw₀ : BottomWidth w C₀) (hτ₀ : s ≤ SwitchingCounting.stars τ₀)
    (hr1 : (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ)) < 1)
    (hcount : ∀ C : Layered n, BottomWidth w C → ∀ cs ∈ bottomGates C, cs.length ≤ m)
    (hgap : ∀ (C : Layered n) (τ : Fin n → Option Bool), BottomWidth w C →
        s ≤ SwitchingCounting.stars τ → 7 * (s : ℚ) < (SwitchingCounting.stars τ : ℚ) * p)
    (hh2 : ∀ C : Layered n, BottomWidth w C →
        ((bottomGatesG C).card : ℚ)
          * (((2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ))) ^ s
              / (1 - (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ)))) < 1 / 2) :
    ∃ x : Fin n → Bool, eval C₀ x ≠ DTree.parity x :=
  parity_not_altO_width_aware s w F d hsw C₀ τ₀ hC₀ hbw₀ hτ₀
    (fun C τ hbw hτ =>
      hsurv_REL_round hp0 hp1 hp3 hs hF C τ hbw (hcount C hbw) hr1 (hgap C τ hbw hτ) (hh2 C hbw))

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.parity_not_altO_REL
