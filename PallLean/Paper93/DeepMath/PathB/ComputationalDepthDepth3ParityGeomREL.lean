import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ParityWCSeq
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3HsurvRoundRel
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3GeomGap
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3H2Schedule
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3GateCount

/-!
# Tight switching, step 92: the fully-assembled general-`d` parity bound at the geometric schedule (branch `razborov-recoverRho-wip`)

The final assembly.  Instantiating the width-and-count-aware capstone (step 91) at the base-`D` geometric
schedule, discharging the per-round survivor from the schedule itself:

* the **Chernoff gap** by `geomSchedB_gap` (step 84), given `D·p > 7` and the threshold not floored;
* the **union bound** by `h2_of_count_pow` (step 85), given `CAP ≤ 1/2`, the gate count `≤ 2M`
  (`bottomGatesG_card_le`, step 86), and the threshold large.

So a depth-`(d+2)` alternating tower of bottom width `≤ geomSchedB D N 1` does not compute parity, in the
standard Håstad regime (`D > 7/p`, `N ≥ 2·D^{d+1}`, `CAP ≤ 1/2`, `8M < 2^{geomSchedB D N (d+1)}`), with the sole
remaining structural input the per-gate clause-count bound `hm` (the bottom gates have `≤ m` clauses).

* `parity_not_altO_geomREL` — the general-`d` parity bound at the geometric schedule on the relative budget.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

/-- **The fully-assembled general-`d` parity lower bound at the geometric schedule.**  Every per-round
condition (Chernoff gap, union bound, gate-count, width) is discharged from the schedule and the regime
constants; only the per-gate clause-count bound `hm` remains as a structural input. -/
theorem parity_not_altO_geomREL {p : ℚ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp3 : 3 * p ≤ 1)
    {F D N M m d : ℕ} [NeZero m] (hN1 : 1 ≤ N) (hF : n ≤ F)
    (hDp : 7 < (D : ℚ) * p)
    (hcap : 2 * ((2 * p / (1 - p)) * (2 * ((geomSchedB D N 1 : ℕ) : ℚ) * (m : ℚ))) ≤ 1)
    (hr1 : (2 * p / (1 - p)) * (2 * ((geomSchedB D N 1 : ℕ) : ℚ) * (m : ℚ)) < 1)
    (hN2 : ∀ i, i ≤ d → 2 * D ^ (i + 1) ≤ N)
    (hNd : ∀ i, i ≤ d → D ^ (i + 1) ≤ N)
    (hbig : ∀ i, i ≤ d → 8 * (M : ℚ) < 2 ^ (geomSchedB D N (i + 1)))
    (C₀ : Layered n) (τ₀ : Fin n → Option Bool) (hC₀ : AltO (d + 2) C₀)
    (hbw₀ : BottomWidth (geomSchedB D N 1) C₀) (hcnt₀ : (bottomGates C₀).length ≤ M)
    (hτ₀ : N ≤ SwitchingCounting.stars τ₀)
    (hm : ∀ (C : Layered n), BottomWidth (geomSchedB D N 1) C →
        ∀ cs ∈ bottomGates C, cs.length ≤ m) :
    ∃ x : Fin n → Bool, eval C₀ x ≠ DTree.parity x := by
  haveI : NeZero (geomSchedB D N 1) := ⟨(lt_of_lt_of_le one_pos (geomSchedB_pos D N 1)).ne'⟩
  have hDpos : 0 < D := by
    rcases Nat.eq_zero_or_pos D with hD | hD
    · subst hD; simp at hDp; nlinarith [hp1, hp0, hDp]
    · exact hD
  refine parity_not_altO_wc_seq (geomSchedB D N) (geomSchedB D N 1) F d M
    (fun i => geomSchedB_anti D N (by omega) (Nat.le_succ i))
    (fun i => geomSchedB_anti D N (by omega) (by omega : 1 ≤ i + 1))
    C₀ τ₀ hC₀ hbw₀ hcnt₀ (by rw [geomSchedB_zero D N hN1]; exact hτ₀) ?_
  intro i hi C τ hbw hcnt hstars
  -- threshold ≥ D at round i (not floored)
  have hgeD : D ≤ geomSchedB D N i := by
    rw [geomSchedB]
    have : D ≤ N / D ^ i := by
      rw [Nat.le_div_iff_mul_le (by positivity)]
      calc D * D ^ i = D ^ (i + 1) := by rw [pow_succ]; ring
        _ ≤ N := hNd i hi
    omega
  -- threshold (i+1) ≥ 2
  have hge2 : 2 ≤ geomSchedB D N (i + 1) := by
    rw [geomSchedB]
    have : 2 ≤ N / D ^ (i + 1) := by
      rw [Nat.le_div_iff_mul_le (by positivity)]
      calc 2 * D ^ (i + 1) ≤ N := hN2 i hi
      _ = N := rfl
    omega
  refine hsurv_REL_round hp0 hp1 hp3 hge2 hF C τ hbw (hm C hbw) hr1 ?_ ?_
  · -- the Chernoff gap
    have hsg := geomSchedB_gap (N := N) hp1 hDp hgeD
    have hcast : (geomSchedB D N i : ℚ) ≤ (SwitchingCounting.stars τ : ℚ) := by exact_mod_cast hstars
    nlinarith [hsg, hcast, hp0, mul_le_mul_of_nonneg_right hcast hp0]
  · -- the union bound
    have hcardle : ((bottomGatesG C).card : ℚ) ≤ (2 * M : ℕ) := by
      have := le_trans (bottomGatesG_card_le C) (by omega : 2 * (bottomGates C).length ≤ 2 * M)
      exact_mod_cast this
    have hcap0 : (0 : ℚ) ≤ (2 * p / (1 - p)) * (2 * ((geomSchedB D N 1 : ℕ) : ℚ) * (m : ℚ)) := by
      have h1p : (0 : ℚ) < 1 - p := by linarith
      positivity
    refine h2_of_count_pow (by positivity) hcardle hcap0 hcap ?_
    have h2M : (4 : ℚ) * (2 * M : ℕ) = 8 * (M : ℚ) := by push_cast; ring
    rw [h2M]; exact hbig i hi

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.parity_not_altO_geomREL
