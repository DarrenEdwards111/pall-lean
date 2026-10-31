import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameDragCeiling

/-!
# N-Frame: coneExcess amplification — the recursion that escapes `log|Y| ≤ N`

The drag caps at `3N` because its only handle on `coneExcess` is single-cut capacity, and
`log₂|Y| ≤ N`.  A SINGLE cut cannot escape it.  A RECURSION can: if an explicit family satisfies

    coneExcess(f_{2N}) ≥ 2·coneExcess(f_N) + c·N,

then unrolling gives `coneExcess(f_N) ≥ c·N·log₂N` — SUPER-LINEAR — and CRUCIALLY, each level's
`+c·N` term is certified by a cut of size `c·N ≤ (level size)`, so NO single cut ever exceeds its
level's input count.  The recursion sums many small (`≤ level`) certificates across `log N`
scales; the `log|Y| ≤ N` bound is per-cut, and the recursion never violates it at any level.

  `coneExcess_amplify` — **PROVED, THE UNROLLING**: `2·T k + c·2^{k+1} ≤ T (k+1)` for all `k`
        ⟹ `c·(k·2^k) ≤ T k` for all `k` — the recurrence solves to `Θ(N log N)` (`N = 2^k`).
  `amplify_exceeds_linear` — **PROVED**: with `c ≥ 1`, `T` exceeds EVERY linear bound
        `b·N` (`b·2^b ≤ T b`) — the recursion is genuinely super-linear, past the `3N` ceiling.

## Honest scope — the recursion is the right SHAPE; proving it is the open problem

`coneExcess_amplify` shows the recursion `coneExcess(f_{2N}) ≥ 2·coneExcess(f_N) + cN` DOES
escape the cut-capacity cap and reaches `Θ(N log N)`.  The candidate family: RECURSIVE RIGID
MIXING — `f_{2N}(x) = g_N(f_N(x₁), f_N(x₂))` on disjoint inputs `x₁, x₂`, with `g_N` a cut-rigid
mixing (a `qform`-over-expander on the `2·(#outputs)` intermediate values) forcing `+cN` fresh
`coneExcess` at the top level, and the two `f_N` sub-cones DISJOINT so their `coneExcess` adds.

The OPEN step is the recursion inequality itself: it requires that a MINIMAL circuit for `f_{2N}`
must (i) contain two disjoint sub-cones each with `coneExcess ≥ coneExcess(f_N)`, and (ii) pay a
fresh `+cN` for the mixing — i.e. it CANNOT share/avoid the sub-instances.  Minimal circuits need
NOT respect the recursive definition, so proving no-avoidance is the crux — and it is exactly the
general SUPER-LINEAR circuit lower bound problem (open, with the linear-size-superconcentrator
barrier: pure CONNECTIVITY is achievable in linear size, so the recursion must force fresh
coneExcess via RIGIDITY of `g_N` at every scale, not mere connectivity).  So this file proves the
amplification's ARITHMETIC is sound (the escape is real IF the recursion holds); the recursion for
an explicit `f` is the honest open target, precisely located.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameConeAmplify

/-- **THE UNROLLING (proved)**: the coneExcess recursion `2·T k + c·2^{k+1} ≤ T (k+1)` solves to
`c·(k·2^k) ≤ T k` — i.e. `Θ(N log N)` with `N = 2^k`, super-linear. -/
theorem coneExcess_amplify (c : ℕ) (T : ℕ → ℕ)
    (hrec : ∀ k, 2 * T k + c * 2 ^ (k + 1) ≤ T (k + 1)) :
    ∀ k, c * (k * 2 ^ k) ≤ T k := by
  intro k
  induction k with
  | zero => simp
  | succ n ih =>
    have hr := hrec n
    have e1 : c * ((n + 1) * 2 ^ (n + 1)) = 2 * (c * (n * 2 ^ n)) + c * 2 ^ (n + 1) := by
      rw [pow_succ]
      ring
    have hmul : 2 * (c * (n * 2 ^ n)) ≤ 2 * T n := by
      exact Nat.mul_le_mul_left 2 ih
    rw [e1]
    omega

/-- **SUPER-LINEAR (proved)**: with `c ≥ 1`, the amplified `T` exceeds every linear bound
`b · N` — for `N = 2^b`, `b·N ≤ T b`.  So the recursion breaks the `3N` drag ceiling. -/
theorem amplify_exceeds_linear (c : ℕ) (T : ℕ → ℕ) (hc : 1 ≤ c)
    (hrec : ∀ k, 2 * T k + c * 2 ^ (k + 1) ≤ T (k + 1)) (b : ℕ) :
    b * 2 ^ b ≤ T b := by
  have hamp := coneExcess_amplify c T hrec b
  calc b * 2 ^ b = 1 * (b * 2 ^ b) := by rw [one_mul]
    _ ≤ c * (b * 2 ^ b) := Nat.mul_le_mul_right _ hc
    _ ≤ T b := hamp

/-- **THE UNCONDITIONAL 1× COROLLARY (proved)**: a SINGLE level of cut-rigidity — cut-rank
`r ≤ coneExcess` (from an induced matching, `NFrameInducedMatch.induced_matching_distinct`) — plus
the ledger `2K + coneExcess ≤ length + 1` gives `2K + r ≤ length + 1`.  With `r = c·N` (the
expander's cut-rank), this is the UNCONDITIONAL `cbudget ≥ (2+c)N` for the flat cut-rigid family,
NO `(KRW-C)` needed — the `1×` (log-factor `1`) bound that the conditional recursion lifts to the
`Θ(N log N)` (log-factor `log N`) of `amplify_exceeds_linear`. -/
theorem cut_rank_linear_bound (K r coneExcess length : ℕ)
    (hr : r ≤ coneExcess) (hled : 2 * K + coneExcess ≤ length + 1) :
    2 * K + r ≤ length + 1 := by
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameConeAmplify

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameConeAmplify.coneExcess_amplify
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameConeAmplify.amplify_exceeds_linear
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameConeAmplify.cut_rank_linear_bound
