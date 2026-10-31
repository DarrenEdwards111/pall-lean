import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3H1Assemble

/-!
# Tight switching, step 72: the per-round inequality from the gap and the union bound (branch `razborov-recoverRho-wip`)

Composing the Chernoff atom `h1_of_gap` (step 71) with the factoring `hcf_of_split` (step 67): at the Markov
parameter `t = 1 - 1/s_out`, the per-round closed-form inequality `hcf` follows from just two clean rational
conditions —

* the **Chernoff gap** `(stars τ)·p > 7·s_out` (concentration: the next threshold sits below the mean), and
* the **union bound** `card · capGeo < box/2` (one deep-gate failure per bottom gate).

So `hcf` is no longer analytic at all: it is `gap ∧ h2`, both elementary rational inequalities.

* `hcf_from_gap` — `hcf` (at `t = 1-1/s_out`) from the gap and the union bound.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

/-- **The per-round inequality from the gap and the union bound.**  At `t = 1 - 1/s_out`, the Chernoff gap
`(stars τ)·p > 7·s_out` and the union bound `card·capGeo < box/2` give the per-round closed-form inequality. -/
theorem hcf_from_gap {p : ℚ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp_lt : p < 1)
    {n starsτ sOut : ℕ} (card capGeo : ℚ) (hs : 1 ≤ sOut)
    (hgap : 7 * (sOut : ℚ) < (starsτ : ℚ) * p)
    (h2 : card * capGeo < ((1 - p) / 2) ^ (n - starsτ) / 2) :
    ((1 - p) / 2) ^ (n - starsτ)
        * ((1 - 1 / (sOut : ℚ)) * p + (1 - p)) ^ starsτ / (1 - 1 / (sOut : ℚ)) ^ (sOut - 1)
      + card * capGeo
      < ((1 - p) / 2) ^ (n - starsτ) :=
  hcf_of_split hp_lt card capGeo (h1_of_gap hp0 hp1 starsτ sOut hs hgap) h2

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.hcf_from_gap
