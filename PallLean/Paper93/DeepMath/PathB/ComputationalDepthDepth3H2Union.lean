import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3HcfFromGap

/-!
# Tight switching, step 74: the union-bound atom `h2` (branch `razborov-recoverRho-wip`)

The second atom of the per-round inequality (step 67), the union bound `card · capGeo < box/2`.  Two reductions:

* `h2_of_geom` — the algebraic step removing the geometric denominator: `h2` from `card·cap^s < box·(1-cap)/2`.
* `h2_rel_clean` — **the key one.**  The survivor lemma's deep-gate mass is bounded *relative to the box*:
  `descent_switching_le_extends` gives `∑_{Bad ⊆ extBox τ} pweight ≤ rate^s · M_dec · box` (the
  `((1-p)/2)^(n-stars τ) = box` factor is present!).  With that relative form the union term is `card · (rate^s
  · M_dec · box)`, so `h2` becomes the **box-free** condition `card · rate^s · M_dec < 1/2` — which holds once
  `rate^s` is small (`s` large), the genuine achievable union bound.

The absolute bound `card·cap` (used by `exists_survivor_shallow_extends_uncond`, step 36, via
`tight_switching_budget_uncond`) is too lossy by a factor of `box`, which is why the per-round `h2` failed for
late rounds; the relative bound (this file) is the fix.  Wiring it needs a survivor lemma built on
`descent_switching_le_extends` (which carries the gates' consistency/nodup hypotheses).

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

/-- **The union bound, algebraic step.**  Removing the geometric denominator `1/(1-cap)`. -/
theorem h2_of_geom {cap box card : ℚ} (hcap1 : cap < 1) (s : ℕ)
    (h : card * cap ^ s < box * (1 - cap) / 2) :
    card * (cap ^ s / (1 - cap)) < box / 2 := by
  have h1c : (0 : ℚ) < 1 - cap := by linarith
  rw [← mul_div_assoc, div_lt_iff₀ h1c]
  have hbox : box * (1 - cap) / 2 = box / 2 * (1 - cap) := by ring
  linarith [h, hbox]

/-- **The relative union bound (the fix).**  When the deep-gate mass is bounded *relative to the box* — the
union term is `card · (rate^s · M_dec · box)` — the union atom `h2` reduces to the **box-free** condition
`card · rate^s · M_dec < 1/2`. -/
theorem h2_rel_clean {rate box card Mdec : ℚ} (s : ℕ) (hbox : 0 < box)
    (h : card * rate ^ s * Mdec < 1 / 2) :
    card * (rate ^ s * Mdec * box) < box / 2 := by
  rw [show card * (rate ^ s * Mdec * box) = (card * rate ^ s * Mdec) * box by ring,
    show box / 2 = (1 / 2) * box by ring]
  exact mul_lt_mul_of_pos_right h hbox

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.h2_of_geom
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.h2_rel_clean
