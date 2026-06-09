import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingBinomialRegime

/-!
# Block-DT model, route-1 bridge step 1: the `(2^w)`-base binomial decay (branch `razborov-recoverRho-wip`)

The decay lemma for the **compact** tight count's base.  The existing `count_decay_step`
(`ComputationalDepthSwitchingBinomialRegime`) proves the half-step decay
`2·M_{s+1} ≤ M_s` for `M_s = 2^{n-K+s}·C(n,K-s)·(2w)^s` (the `(2w)^s` label base), feeding the geometric
tail-sum and `exists_depth_lt_in_of_decay`.  The tight **compact** count `block_switching_count_tight` uses
the position-set label `BlockPathLabel w s` of base `(2^w)^s` (each block a `Finset (Fin w)`), so to route it
through the same decay engine we need the decay for `M_s = 2^{n-K+s}·C(n,K-s)·(2^w)^s`.

The decay multiplier works out to `2·2·2^w = 4·2^w` (the strict-halving `2`, the `2` from `2^{n-K+s+1}`, and
the `2^w` from `(2^w)^{s+1}`), so the regime is `(4·2^w)·K + K ≤ n+1` and the binomial step needs
`(4·2^w)·C(n,K-(s+1)) ≤ C(n,K-s)`.  We prove a **generic-multiplier** binomial step (the `8w`-specialised
`binomial_ratio_strict_step` generalised to any `r`) and specialise it.

* `binomial_ratio_strict_step_gen` — `r·C(n,K-(s+1)) ≤ C(n,K-s)` under `r·K + K ≤ n+1`.
* `count_decay_step_pow` — `2·M_{s+1} ≤ M_s` for the `(2^w)^s`-base count, under `(4·2^w)·K + K ≤ n+1`.

## Honest scope

This is the binomial decay for the compact `(2^w)^s` base — the route-1 building block that lets
`block_switching_count_tight` feed `exists_depth_lt_in_of_decay`.  The keystone that still remains is the
**canonical-DT-depth-graded** `m`-free per-shell count (`block_switching_count_tight` grades by `blockStream`
length, the decay engine by `canonicalDT` depth); reconciling those two gradings is the remaining work.  This
brick supplies the decay; it does not yet assemble the shallow-existence.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

/-- **Generic-multiplier strict binomial step.**  For any multiplier `r`, under the slack regime
`r·K + K ≤ n+1`, the binomial coefficient grows by a factor `≥ r` as the lower index increases by one. -/
theorem binomial_ratio_strict_step_gen {n r K s : ℕ} (hs : s < K) (hreg : r * K + K ≤ n + 1) :
    r * n.choose (K - (s + 1)) ≤ n.choose (K - s) := by
  have hKs : K - s = (K - (s + 1)) + 1 := by omega
  rw [hKs]
  refine choose_step ?_
  have hmul : r * ((K - (s + 1)) + 1) ≤ r * K := mul_le_mul_left' (by omega) r
  omega

/-- **Count-form decay for the compact `(2^w)^s` base.**  The compact switching count
`M_s = 2^{n-K+s}·C(n,K-s)·(2^w)^s` at least halves at each step, in the slack regime `(4·2^w)·K + K ≤ n+1`. -/
theorem count_decay_step_pow {n w K s : ℕ} (hs : s < K) (hreg : (4 * 2 ^ w) * K + K ≤ n + 1) :
    2 * (2 ^ (n - K + (s + 1)) * n.choose (K - (s + 1)) * (2 ^ w) ^ (s + 1))
      ≤ 2 ^ (n - K + s) * n.choose (K - s) * (2 ^ w) ^ s := by
  have hstep : (4 * 2 ^ w) * n.choose (K - (s + 1)) ≤ n.choose (K - s) :=
    binomial_ratio_strict_step_gen hs hreg
  have hexp : n - K + (s + 1) = (n - K + s) + 1 := by omega
  rw [hexp, pow_succ, pow_succ]
  calc 2 * (2 ^ (n - K + s) * 2 * n.choose (K - (s + 1)) * ((2 ^ w) ^ s * 2 ^ w))
      = (2 ^ (n - K + s) * (2 ^ w) ^ s) * ((4 * 2 ^ w) * n.choose (K - (s + 1))) := by ring
    _ ≤ (2 ^ (n - K + s) * (2 ^ w) ^ s) * n.choose (K - s) := Nat.mul_le_mul_left _ hstep
    _ = 2 ^ (n - K + s) * n.choose (K - s) * (2 ^ w) ^ s := by ring

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.count_decay_step_pow
