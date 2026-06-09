import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ParityClosedFormSeq

/-!
# Tight switching, step 68: the concrete geometric threshold schedule (branch `razborov-recoverRho-wip`)

The decreasing threshold the Håstad regime needs, made concrete: `geomSched N i = max 1 (N / 2^i)` — the
survivor count halves each round, floored at `1`.  Its structural properties (antitone, `≥ 1`, bounded by the
first post-round value `geomSched N 1`) discharge the sequence capstone's `hmono`/`hs1`/`hsw`, leaving the
specialised general-`d` parity bound `parity_not_altO_geom` with only the rate, the count bound, and the
per-round closed-form inequality `hcf` (now at the explicit geometric schedule).

* `geomSched` — the halving schedule.
* `geomSched_anti` / `geomSched_pos` / `geomSched_zero` — its structural facts.
* `parity_not_altO_geom` — the general-`d` parity bound at the geometric schedule.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

/-- The halving survivor-threshold schedule: `N`, `N/2`, `N/4`, …, floored at `1`. -/
def geomSched (N : ℕ) (i : ℕ) : ℕ := max 1 (N / 2 ^ i)

/-- The schedule is antitone: more rounds ⟹ fewer survivors. -/
theorem geomSched_anti (N : ℕ) {a b : ℕ} (hab : a ≤ b) : geomSched N b ≤ geomSched N a := by
  apply max_le_max (le_refl 1)
  exact Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) hab) (by positivity)

/-- The schedule is always at least `1`. -/
theorem geomSched_pos (N i : ℕ) : 1 ≤ geomSched N i := le_max_left _ _

/-- The schedule starts at `N` (for `N ≥ 1`). -/
theorem geomSched_zero (N : ℕ) (hN : 1 ≤ N) : geomSched N 0 = N := by
  rw [geomSched, pow_zero, Nat.div_one, max_eq_right hN]

/-- **The general-`d` parity lower bound at the geometric schedule.**  A depth-`(d+2)` alternating tower of
bottom width `≤ geomSched N 1` does not compute parity, given the rate, the count bound, and the per-round
closed-form inequality at the halving schedule.  The structural sequence hypotheses are discharged by
`geomSched`'s antitonicity and positivity. -/
theorem parity_not_altO_geom {p t : ℚ}
    (ht0 : 0 < t) (ht1 : t ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp3 : 3 * p ≤ 1)
    {F m N : ℕ} (d : ℕ) [NeZero m] (hN : 1 ≤ N) (hF : n ≤ F)
    (C₀ : Layered n) (τ₀ : Fin n → Option Bool) (hC₀ : AltO (d + 2) C₀)
    (hbw₀ : BottomWidth (geomSched N 1) C₀) (hτ₀ : N ≤ SwitchingCounting.stars τ₀)
    (hr1 : (2 * p / (1 - p)) * (2 * ((geomSched N 1 : ℕ) : ℚ) * (m : ℚ)) < 1)
    (hcount : ∀ C : Layered n, BottomWidth (geomSched N 1) C →
        ∀ cs ∈ bottomGates C, cs.length ≤ m)
    (hcf : ∀ (i : ℕ) (C : Layered n) (τ : Fin n → Option Bool), BottomWidth (geomSched N 1) C →
        geomSched N i ≤ SwitchingCounting.stars τ →
        ((1 - p) / 2) ^ (n - SwitchingCounting.stars τ)
            * (t * p + (1 - p)) ^ (SwitchingCounting.stars τ) / t ^ (geomSched N (i + 1) - 1)
          + ((bottomGatesG C).card : ℚ)
              * (((2 * p / (1 - p)) * (2 * ((geomSched N 1 : ℕ) : ℚ) * (m : ℚ))) ^ (geomSched N (i + 1))
                  / (1 - (2 * p / (1 - p)) * (2 * ((geomSched N 1 : ℕ) : ℚ) * (m : ℚ))))
        < ((1 - p) / 2) ^ (n - SwitchingCounting.stars τ)) :
    ∃ x : Fin n → Bool, eval C₀ x ≠ DTree.parity x := by
  haveI : NeZero (geomSched N 1) := ⟨(lt_of_lt_of_le one_pos (geomSched_pos N 1)).ne'⟩
  refine parity_not_altO_closed_form_seq ht0 ht1 hp0 hp1 hp3 (geomSched N) d
    (fun i => geomSched_anti N (Nat.le_succ i)) (fun i => geomSched_pos N (i + 1))
    (fun i => geomSched_anti N (by omega : 1 ≤ i + 1)) hF C₀ τ₀ hC₀ hbw₀ ?_ hr1 hcount hcf
  rw [geomSched_zero N hN]; exact hτ₀

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.parity_not_altO_geom
