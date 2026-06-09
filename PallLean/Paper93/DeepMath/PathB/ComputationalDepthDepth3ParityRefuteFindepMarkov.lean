import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ParityRefuteFindepConcrete

/-!
# Block-DT model, route-2 step [160]: Markov-discharged m-free single-DNF parity refutation

Brick [159] (`dnf_not_parity_findep_of_tails`) reduced the m-free single-DNF parity refutation to a
numeric gap on explicit tail bounds `Blo`/`Bhi`.  Here we discharge those tails with the
probability-generating-function Markov bounds `stars_tail_le` / `stars_tail_ge` (brick on
`ComputationalDepthDepth3StarTail`), eliminating the two opaque star-count sums entirely.  The result
is a parity refutation whose only remaining hypothesis is a gap between **closed-form rational
quantities** in `p`, the two Markov tilts `t_lo ≤ 1 ≤ t_hi`, and `n, s, F, w`:

  `(r')^s/(1-r')  +  (t_lo·p + (1-p))^n / t_lo^(s-1)  +  (t_hi·p + (1-p))^n / t_hi^F  <  1`,

with `r' = (2p/(1-p))(4w+1)`.  The middle term is the lower (Chernoff) tail `P[stars < s]` and the
last is the upper tail `P[F ≤ stars]`, both via the Markov/PGF method `E[t^stars] = (tp+(1-p))^n`.

* `dnf_not_parity_findep_markov` — no opaque sums; the gap is a concrete arithmetic inequality.
  Instantiating `p, t_lo, t_hi, n, s, F, w` at the standard Håstad regime (`s,F` bracketing the
  mean `pn`) and checking the gap numerically yields a fully unconditional refutation (brick [161]).

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **m-free single-DNF parity refutation with the star-tails discharged by the PGF Markov bounds.**
Picking a lower tilt `0 < t_lo ≤ 1` and an upper tilt `1 ≤ t_hi`, the low/high star-count tails are
bounded by `(t·p+(1-p))^n / t^k` (the generating function `E[t^stars] = (t·p+(1-p))^n` divided by
`t^k` à la Markov).  The refutation then follows from a gap between closed-form rationals only. -/
theorem dnf_not_parity_findep_markov {p t_lo t_hi : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    (ht_lo0 : 0 < t_lo) (ht_lo1 : t_lo ≤ 1) (ht_hi1 : 1 ≤ t_hi)
    {w F s : ℕ} [NeZero w] (hs : 1 ≤ s) (D : List (Clause n))
    (hcons : ∀ T ∈ D, Consistent T) (hnd : ∀ T ∈ D, (T.lits.map litVarOf).Nodup)
    (hw : ∀ T ∈ D, T.lits.length ≤ w)
    (hr' : (2 * p / (1 - p)) * (4 * w + 1) < 1)
    (hgap : ((2 * p / (1 - p)) * (4 * w + 1)) ^ s / (1 - (2 * p / (1 - p)) * (4 * w + 1))
              + (t_lo * p + (1 - p)) ^ n / t_lo ^ (s - 1)
              + (t_hi * p + (1 - p)) ^ n / t_hi ^ F < 1) :
    ∃ (ρ : Restriction n) (x : Fin n → Bool),
      DTree.agreeRestriction ρ x ∧ DTree.dnfValue D x ≠ DTree.parity x := by
  have hp1 : p ≤ 1 := by linarith
  have ht_hi0 : (0 : ℚ) < t_hi := by linarith
  -- lower (Chernoff) tail:  P[stars < s] = P[stars ≤ s-1] ≤ (t_lo·p+(1-p))^n / t_lo^(s-1)
  have hlo : (∑ ρ ∈ Finset.univ.filter (fun ρ : Restriction n => SwitchingCounting.stars ρ < s),
        pweight p ρ) ≤ (t_lo * p + (1 - p)) ^ n / t_lo ^ (s - 1) := by
    have hfilter :
        (Finset.univ.filter (fun ρ : Restriction n => SwitchingCounting.stars ρ < s))
          = Finset.univ.filter (fun ρ : Restriction n => SwitchingCounting.stars ρ ≤ s - 1) := by
      apply Finset.filter_congr; intro ρ _; omega
    rw [hfilter, le_div_iff₀ (pow_pos ht_lo0 (s - 1)), mul_comm]
    exact stars_tail_le (n := n) ht_lo0.le ht_lo1 hp0 hp1 (s - 1)
  -- upper tail:  P[F ≤ stars] ≤ (t_hi·p+(1-p))^n / t_hi^F
  have hhi : (∑ ρ ∈ Finset.univ.filter (fun ρ : Restriction n => F ≤ SwitchingCounting.stars ρ),
        pweight p ρ) ≤ (t_hi * p + (1 - p)) ^ n / t_hi ^ F := by
    rw [le_div_iff₀ (pow_pos ht_hi0 F), mul_comm]
    exact stars_tail_ge (n := n) ht_hi1 hp0 hp1 F
  exact dnf_not_parity_findep_of_tails hp0 hp3 D hcons hnd hw hr' hlo hhi hgap

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.dnf_not_parity_findep_markov
