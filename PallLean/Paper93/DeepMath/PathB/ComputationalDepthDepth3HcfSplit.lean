import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3HsmallChernoff

/-!
# Tight switching, step 67: factoring the per-round inequality into its two atoms (branch `razborov-recoverRho-wip`)

The per-round closed-form inequality `hcf` (step 66) is the sum of two physically distinct terms — the
*Chernoff concentration* `box · (t·p+(1-p))^(stars τ)/t^(s-1)` (the conditional low-star tail) and the
*union-bound* term `card · cap^s/(1-cap)` (one deep-gate failure per bottom gate).  `hcf_of_split` factors it:
if each is below half the box mass, their sum is below the box.  The Chernoff half reduces to a *dimensionless*
inequality `(t·p+(1-p))^(stars τ)/t^(s-1) < 1/2` (independent of the box), and the union half to
`card · cap^s/(1-cap) < box/2`.  These are the two genuine analytic atoms of every switching-lemma argument.

* `hcf_of_split` — `hcf` from the dimensionless Chernoff bound and the union-bound bound.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

/-- **Factoring the per-round inequality.**  Below `p < 1`, if the dimensionless Chernoff term is below `1/2`
and the union-bound term is below half the box mass, the per-round closed-form inequality holds. -/
theorem hcf_of_split {p t : ℚ} (hp_lt : p < 1) {n starsτ sOut : ℕ} (card capGeo : ℚ)
    (h1 : (t * p + (1 - p)) ^ starsτ / t ^ (sOut - 1) < 1 / 2)
    (h2 : card * capGeo < ((1 - p) / 2) ^ (n - starsτ) / 2) :
    ((1 - p) / 2) ^ (n - starsτ) * (t * p + (1 - p)) ^ starsτ / t ^ (sOut - 1) + card * capGeo
      < ((1 - p) / 2) ^ (n - starsτ) := by
  have hbox : (0 : ℚ) < ((1 - p) / 2) ^ (n - starsτ) := pow_pos (by linarith) _
  rw [mul_div_assoc]
  have ht1 := mul_lt_mul_of_pos_left h1 hbox
  have hhalf : ((1 - p) / 2) ^ (n - starsτ) * (1 / 2) = ((1 - p) / 2) ^ (n - starsτ) / 2 := by ring
  rw [hhalf] at ht1
  linarith

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.hcf_of_split
