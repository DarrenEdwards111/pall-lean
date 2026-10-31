import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ParityWCSeq3
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3HsurvRoundREL2
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3GeomGap
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3H2Schedule
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3GateCount

/-!
# Tight switching, step 100: the fully self-contained general-`d` parity bound (two-parameter, geometric schedule) (branch `razborov-recoverRho-wip`)

The culmination of the two-parameter rework.  Instantiating the four-invariant capstone (step 99) at the
geometric *star* schedule `geomSchedB D N` and a *constant* depth threshold `t`, with the per-round survivor
discharged by `hsurv_REL2_round` (step 96).  Because the depth threshold `t` is constant, the clause-count
`m`, the width `t`, and the rate are all *constant in `n`* — so the union bound `8M < 2^t` is a single
constant condition (not per-round), and the gap holds round by round from the geometric schedule (`D > 7/p`).

This is the fully self-contained statement: a depth-`(d+2)` alternating tower of bottom width `≤ t`, gate count
`≤ M`, per-gate clause-count `≤ m` does **not** compute parity, with all per-round conditions discharged —
**no `hm` hypothesis left** (the clause-count is threaded as `BottomCount m`).

* `parity_not_altO_geomREL2` — the fully-assembled two-parameter general-`d` parity bound.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

/-- **The fully self-contained two-parameter general-`d` parity bound.**  All per-round conditions (gap at the
geometric star threshold, union at the constant depth `t`, gate count, width, clause count) are discharged from
the regime constants; nothing per-gate is left as a hypothesis. -/
theorem parity_not_altO_geomREL2 {p : ℚ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp3 : 3 * p ≤ 1)
    {F D N M t m d : ℕ} (ht1 : 1 ≤ t) (hN1 : 1 ≤ N) (hF : n ≤ F)
    (hDp : 7 < (D : ℚ) * p)
    (hcap : 2 * ((2 * p / (1 - p)) * (2 * (t : ℚ) * (m : ℚ))) ≤ 1)
    (hr1 : (2 * p / (1 - p)) * (2 * (t : ℚ) * (m : ℚ)) < 1)
    (hM1 : 1 ≤ M) (hMm : M * 2 ^ t ≤ m)
    (hbig : 8 * (M : ℚ) < 2 ^ t)
    (htd : t ≤ geomSchedB D N (d + 1))
    (hN2 : ∀ i, i ≤ d → 2 * D ^ (i + 1) ≤ N) (hNd : ∀ i, i ≤ d → D ^ (i + 1) ≤ N)
    (C₀ : Layered n) (τ₀ : Fin n → Option Bool) (hC₀ : AltO (d + 2) C₀)
    (hbw₀ : BottomWidth t C₀) (hcnt₀ : (bottomGates C₀).length ≤ M) (hmc₀ : BottomCount m C₀)
    (hτ₀ : N ≤ SwitchingCounting.stars τ₀) :
    ∃ x : Fin n → Bool, eval C₀ x ≠ DTree.parity x := by
  haveI : NeZero t := ⟨by omega⟩
  haveI : NeZero m := ⟨by have h0 : 0 < M * 2 ^ t := Nat.mul_pos (by omega) (by positivity); omega⟩
  have hDpos : 0 < D := by
    rcases Nat.eq_zero_or_pos D with hD | hD
    · subst hD; simp at hDp; nlinarith [hp1, hp0, hDp]
    · exact hD
  refine parity_not_altO_wc_seq3 (geomSchedB D N) t F d M m
    (fun i => geomSchedB_anti D N (by omega) (Nat.le_succ i)) htd hM1 hMm
    C₀ τ₀ hC₀ hbw₀ hcnt₀ hmc₀ (by rw [geomSchedB_zero D N hN1]; exact hτ₀) ?_
  intro i hi C τ hbw hcnt hmcc hstars
  have hgeD : D ≤ geomSchedB D N i := by
    rw [geomSchedB]
    have : D ≤ N / D ^ i := by
      rw [Nat.le_div_iff_mul_le (by positivity)]
      calc D * D ^ i = D ^ (i + 1) := by rw [pow_succ]; ring
        _ ≤ N := hNd i hi
    omega
  have hge2 : 2 ≤ geomSchedB D N (i + 1) := by
    rw [geomSchedB]
    have : 2 ≤ N / D ^ (i + 1) := by
      rw [Nat.le_div_iff_mul_le (by positivity)]; exact hN2 i hi
    omega
  refine hsurv_REL2_round hp0 hp1 hp3 hge2 hF C τ hbw hmcc hr1 ?_ ?_
  · have hsg := geomSchedB_gap (N := N) hp1 hDp hgeD
    have hcast : (geomSchedB D N i : ℚ) ≤ (SwitchingCounting.stars τ : ℚ) := by exact_mod_cast hstars
    nlinarith [hsg, hcast, hp0, mul_le_mul_of_nonneg_right hcast hp0]
  · have hcardle : ((bottomGatesG C).card : ℚ) ≤ (2 * M : ℕ) := by
      have := le_trans (bottomGatesG_card_le C) (by omega : 2 * (bottomGates C).length ≤ 2 * M)
      exact_mod_cast this
    have hcap0 : (0 : ℚ) ≤ (2 * p / (1 - p)) * (2 * (t : ℚ) * (m : ℚ)) := by
      have h1p : (0 : ℚ) < 1 - p := by linarith
      positivity
    refine h2_of_count_pow (by positivity) hcardle hcap0 hcap ?_
    have h2M : (4 : ℚ) * (2 * M : ℕ) = 8 * (M : ℚ) := by push_cast; ring
    rw [h2M]; exact hbig

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.parity_not_altO_geomREL2
