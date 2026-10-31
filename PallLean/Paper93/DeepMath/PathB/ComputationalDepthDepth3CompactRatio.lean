import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingBinomialRegime

/-!
# Block-DT model, hbound-discharge lemma 2: the compact `(2^w)^s` binomial ratio (branch `razborov-recoverRho-wip`)

The second of the three small lemmas discharging `circuit_collapse_exists`'s union bound.  The compact tight
count carries the base `(2^w)^s`; to absorb it (and the gate count) into the shell ratio we need the binomial
ratio `(4·2^w)^s · C(n,K-s) ≤ C(n,K)` (the multiplier `4·2^w = 2^{w+2}` is the one brick 148's decay uses).

The existing `binomial_ratio_regime_strict` is hardcoded to the `8w` multiplier; we generalise it to an
arbitrary multiplier `r` via the engine `pow_mul_choose_le` (the slack regime `r·K + K ≤ n+1` makes the
per-step condition `r·(k+1) ≤ n-k` hold for every `k < K`), then specialise to `4·2^w`.

* `binomial_ratio_regime_gen` — `r^T · C(n,K-T) ≤ C(n,K)` under `r·K + K ≤ n+1`, any multiplier `r`.
* `compact_binom_ratio` — `(4·2^w)^s · C(n,K-s) ≤ C(n,K)` under `(4·2^w)·K + K ≤ n+1`.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

/-- **Generic-multiplier binomial regime ratio.**  Under the slack regime `r·K + K ≤ n+1`, lowering the index
by `T ≤ K` costs at least a factor `r^T`. -/
theorem binomial_ratio_regime_gen {n r K T : ℕ} (hTK : T ≤ K) (hreg : r * K + K ≤ n + 1) :
    r ^ T * n.choose (K - T) ≤ n.choose K := by
  have h := pow_mul_choose_le (n := n) (r := r) (m := K - T) T (fun k _hk1 hk2 => by
    have hkK : k + 1 ≤ K := by omega
    calc r * (k + 1) ≤ r * K := by gcongr
      _ ≤ n - k := by omega)
  rwa [Nat.sub_add_cancel hTK] at h

/-- **The compact `(4·2^w)^s` binomial ratio.**  Specialisation of `binomial_ratio_regime_gen` to the compact
multiplier `4·2^w = 2^{w+2}` used by the compact tight count's decay (brick 148). -/
theorem compact_binom_ratio {n w K s : ℕ} (hsK : s ≤ K) (hreg : (4 * 2 ^ w) * K + K ≤ n + 1) :
    (4 * 2 ^ w) ^ s * n.choose (K - s) ≤ n.choose K :=
  binomial_ratio_regime_gen hsK hreg

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.compact_binom_ratio
