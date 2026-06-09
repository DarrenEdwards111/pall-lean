import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SwitchingProbFindep
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CanonicalParity
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3PNormalize

/-!
# Block-DT model, route-2 step [156]: F-INDEPENDENT switching refutes parity (branch `razborov-recoverRho-wip`)

The payoff of route 2.  `parity_refuted_by_switching` (brick 62) refutes parity once the switching cap
`(2p/(1-p))^s · (4^w+1)^F` drops below the high-star weight — but that cap is **`F`-dependent**, so it is
vacuous for large `F` (the depth-`(d+2)` regime).  Here we use the `F`-independent bound
`descent_switching_prob_findep` (brick 155c) to refute parity with an **`F`-independent** cap
`(r')^s/(1-r')`, `r' = (2p/(1-p))(4w+1) < 1`.

* `descent_switching_findep_le` — the global `F`-independent switching bound (the `τ = ∅` case of
  brick 155c: `∑_{σ∈Bad} pweight σ ≤ (r')^s/(1-r')`).
* `parity_refuted_by_switching_findep` — if `(r')^s/(1-r') < ∑_{s ≤ stars σ < F} pweight σ`, then some
  high-star subcube witnesses `dnfValue cs ≠ parity`.

The hypothesis is again the concentration fact `∑_{s ≤ stars < F} pweight ≈ 1` (for `s < pn < F`), stated
directly.  Unlike brick 62, the cap no longer grows with `F`, so the refutation survives the iterated /
depth-graded regime — the whole point of route 2.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The global F-independent switching bound.**  The `τ = ∅` instance of brick 155c: the total p-biased
weight of deep (`depth ≥ s`) restrictions is at most `(r')^s/(1-r')`, with `r' = (2p/(1-p))(4w+1)` and **no
`F`-dependence**. -/
theorem descent_switching_findep_le {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    (cs : List (Clause n)) (hcons : ∀ T ∈ cs, Consistent T)
    (hnd : ∀ T ∈ cs, (T.lits.map litVarOf).Nodup) (w : ℕ) [NeZero w] (hw : ∀ T ∈ cs, T.lits.length ≤ w)
    (hr' : (2 * p / (1 - p)) * (4 * w + 1) < 1)
    (F s : ℕ) {Bad : Finset (Fin n → Option Bool)}
    (hBad : ∀ σ ∈ Bad, s ≤ (canonicalDTree cs w F σ).depth) :
    (∑ σ ∈ Bad, pweight p σ)
      ≤ ((2 * p / (1 - p)) * (4 * w + 1)) ^ s / (1 - (2 * p / (1 - p)) * (4 * w + 1)) := by
  have h := descent_switching_prob_findep hp0 hp3 cs hcons hnd w hw hr' F s (fun _ : Fin n => none)
    (fun σ _ v b hb => by simp at hb) hBad
  have hbox : (∑ ρ ∈ extBox (fun _ : Fin n => none), pweight p ρ) = 1 := by
    have he : extBox (fun _ : Fin n => none) = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro σ; rw [mem_extBox]; intro v b hb; simp at hb
    rw [he]; exact pweight_sum_eq_one p
  rwa [hbox, mul_one] at h

/-- **F-independent switching refutes parity.**  If the `F`-independent switching cap `(r')^s/(1-r')` is
below the p-biased weight of the high-star restrictions, a width-`≤ w` DNF cannot compute parity on all of
them: some `σ` with `s ≤ stars σ < F` has a `σ`-consistent input where `dnfValue cs ≠ parity`. -/
theorem parity_refuted_by_switching_findep {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    (cs : List (Clause n)) (hcons : ∀ T ∈ cs, Consistent T)
    (hnd : ∀ T ∈ cs, (T.lits.map litVarOf).Nodup) (w : ℕ) [NeZero w] (hw : ∀ T ∈ cs, T.lits.length ≤ w)
    (hr' : (2 * p / (1 - p)) * (4 * w + 1) < 1)
    (F s : ℕ)
    (hbig : ((2 * p / (1 - p)) * (4 * w + 1)) ^ s / (1 - (2 * p / (1 - p)) * (4 * w + 1))
        < ∑ σ ∈ Finset.univ.filter (fun σ : Fin n → Option Bool => s ≤ stars σ ∧ stars σ < F),
            pweight p σ) :
    ∃ σ : Fin n → Option Bool, s ≤ stars σ ∧ stars σ < F
      ∧ ∃ x, DTree.agreeRestriction σ x ∧ DTree.dnfValue cs x ≠ DTree.parity x := by
  by_contra hcon
  push_neg at hcon
  have hBad : ∀ σ ∈ Finset.univ.filter (fun σ : Fin n → Option Bool => s ≤ stars σ ∧ stars σ < F),
      s ≤ (canonicalDTree cs w F σ).depth := by
    intro σ hσ
    rw [Finset.mem_filter] at hσ
    obtain ⟨_, hs, hF⟩ := hσ
    have hpar : ∀ x, DTree.agreeRestriction σ x → DTree.dnfValue cs x = DTree.parity x :=
      fun x hx => hcon σ hs hF x hx
    exact le_trans hs (canonicalDTree_depth_ge_of_parity cs w F σ hF hpar)
  have h := descent_switching_findep_le hp0 hp3 cs hcons hnd w hw hr' F s hBad
  linarith

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.parity_refuted_by_switching_findep
