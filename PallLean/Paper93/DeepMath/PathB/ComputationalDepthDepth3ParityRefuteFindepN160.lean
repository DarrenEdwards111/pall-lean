import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ParityRefuteFindepMarkov

/-!
# Block-DT model, route-2 step [161]: a fully UNCONDITIONAL m-free single-DNF parity refutation

The capstone of the m-free single-gate story: a concrete instantiation of
`dnf_not_parity_findep_markov` (brick [160]) at the standard Håstad regime, with the gap discharged
numerically by `norm_num` (no `native_decide`).  The parameters

  `n = 160`,  `p = 1/16`,  `w = 1`,  `s = 6`,  `F = 15`,
  lower tilt `t_lo = 15/31 ≤ 1`,  upper tilt `t_hi = 3/2 ≥ 1`,

place the star-thresholds `s = 6 < F = 15` bracketing the mean `p·n = 10`, so the geometric
deep-cap `r' = 2/3` (giving `(2/3)^6/(1/3) = 64/243 ≈ 0.263`), the lower (Chernoff) tail
`(30/31)^160/(15/31)^5 ≈ 0.199`, and the upper tail `(33/32)^160/(3/2)^15 ≈ 0.314` total
`≈ 0.776 < 1` — an honest margin of `≈ 0.224`.

* `parity_not_dnf_width1_n160` — **no hypotheses beyond the shape of `D`**: every width-`≤ 1`,
  consistent, nodup-variable DNF over `160` variables disagrees with parity at some subcube point.
  This is the fully unconditional, parameter-free statement that brick [158]'s budget made possible.

The width here is `1` (the smallest non-degenerate case that exercises the whole pipeline); the same
template instantiates at any constant width `w` by re-balancing `p ≈ 1/(8w)`, `s, F` around `p·n`,
and `n` large enough — the gap is then again a finite `norm_num` check.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

/-- **Unconditional m-free parity refutation at `n = 160`, width `1`.**  Every consistent,
nodup-variable DNF of width `≤ 1` over `160` variables fails to compute parity: there is a
restriction `ρ` and a point `x` of its subcube where the DNF and parity disagree.  No probabilistic
or budget hypothesis — the Håstad regime `(p,s,F,t_lo,t_hi) = (1/16, 6, 15, 15/31, 3/2)` discharges
the switching gap outright. -/
theorem parity_not_dnf_width1_n160 (D : List (Clause 160))
    (hcons : ∀ T ∈ D, Consistent T) (hnd : ∀ T ∈ D, (T.lits.map litVarOf).Nodup)
    (hw : ∀ T ∈ D, T.lits.length ≤ 1) :
    ∃ (ρ : Restriction 160) (x : Fin 160 → Bool),
      DTree.agreeRestriction ρ x ∧ DTree.dnfValue D x ≠ DTree.parity x := by
  haveI : NeZero (1 : ℕ) := ⟨one_ne_zero⟩
  refine dnf_not_parity_findep_markov (n := 160) (p := 1/16) (t_lo := 15/31) (t_hi := 3/2)
      (w := 1) (F := 15) (s := 6)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) D hcons hnd hw (by norm_num) ?_
  norm_num

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.parity_not_dnf_width1_n160
