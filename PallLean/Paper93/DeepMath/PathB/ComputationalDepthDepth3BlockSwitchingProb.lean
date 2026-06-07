import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BlockTightCount
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Block-DT model, foundation 11: count → probability bound (branch only)

The tight holographic switching count `|Bad| ≤ |{σ : stars σ ≤ K-s}| · (2^w)^s` is turned into a
**fraction / probability** statement under the uniform distribution on the `K`-star shell
`Ω = {σ : stars σ = K}` (`|Ω| = C(n,K)·2^(n-K)`, `card_stars_eq`).  This is the classic Håstad payoff
in holographic dress: each restricted star contributes a multiplicative geometric gain.

* `block_switching_count_explicit` — substitute `card_stars_le`: `|Bad| ≤ (∑_{j≤K-s} C(n,j)·2^(n-j))·(2^w)^s`.
* `shell_ratio_nat` — the **per-star geometric gain** from `binom_layer_ratio` (the heart of Håstad):
  `C(n,K-s)·2^(n-K+s)·(n-K+1)^s ≤ C(n,K)·2^(n-K)·(2K)^s`, i.e. the `(K-s)`-shell is a
  `(2K/(n-K+1))^s`-fraction of the `K`-shell.  With `K ≈ pn`, `2K/(n-K+1) ≈ 2p/(1-p)`.
* `block_switching_prob_le` — the probability bound: `Pr_Ω[block-DT depth ≥ s] ≤ (RHS)/|Ω|`, the exact
  fraction of the `K`-shell that is `Bad`, bounded by the explicit count.

## Honest scope

`block_switching_prob_le` gives the **exact** fraction bound (count ÷ shell), fully rigorous.
`shell_ratio_nat` gives the genuine per-star gain `(2K/(n-K+1))^s`.  Collapsing the *cumulative* sum
`∑_{j≤K-s}` into the closed Håstad form `(2^{w+1}K/(n-K+1))^s/(1-r)` needs the geometric-tail estimate
(`r = 2K/(n-K+1) < 1`, i.e. the `p < 1/3` regime) summed over shells — the remaining analytic step,
flagged here rather than hidden.  AC⁰/depth-3; not P≠NP-strength.

Clean, no `sorry`, no `native_decide`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **Binomial layer-ratio** (inlined to avoid the `RestrictionStarCount` ↔ `SwitchingBridge`
`card_stars_eq` name clash; same statement as `SwitchingCounting.binom_layer_ratio`).  Iterating the
Pascal recurrence: for `s ≤ t ≤ N`, `C(N, t-s)·(N-t+1)^s ≤ C(N, t)·t^s`. -/
private theorem binom_layer_ratio' {N : ℕ} : ∀ (s t : ℕ), s ≤ t → t ≤ N →
    Nat.choose N (t - s) * (N - t + 1) ^ s ≤ Nat.choose N t * t ^ s := by
  intro s
  induction s with
  | zero => intro t _ _; simp
  | succ s ih =>
    intro t hst ht
    have hstep : Nat.choose N (t - (s + 1)) * (N - t + 1) ≤ Nat.choose N (t - s) * t := by
      have hrec := Nat.choose_succ_right_eq N (t - (s + 1))
      have he1 : (t - (s + 1)) + 1 = t - s := by omega
      have he2 : N - (t - (s + 1)) = N - t + s + 1 := by omega
      rw [he1, he2] at hrec
      calc Nat.choose N (t - (s + 1)) * (N - t + 1)
          ≤ Nat.choose N (t - (s + 1)) * (N - t + s + 1) := mul_le_mul_left' (by omega) _
        _ = Nat.choose N (t - s) * (t - s) := hrec.symm
        _ ≤ Nat.choose N (t - s) * t := mul_le_mul_left' (by omega) _
    have ihs : Nat.choose N (t - s) * (N - t + 1) ^ s ≤ Nat.choose N t * t ^ s :=
      ih t (by omega) ht
    calc Nat.choose N (t - (s + 1)) * (N - t + 1) ^ (s + 1)
        = (Nat.choose N (t - (s + 1)) * (N - t + 1)) * (N - t + 1) ^ s := by ring
      _ ≤ (Nat.choose N (t - s) * t) * (N - t + 1) ^ s := mul_le_mul_right' hstep _
      _ = t * (Nat.choose N (t - s) * (N - t + 1) ^ s) := by ring
      _ ≤ t * (Nat.choose N t * t ^ s) := mul_le_mul_left' ihs _
      _ = Nat.choose N t * t ^ (s + 1) := by ring

/-- **Explicit count.**  Substituting the cumulative shell cardinality `card_stars_le` into the tight
holographic count: `|Bad| ≤ (∑_{j≤K-s} C(n,j)·2^(n-j)) · (2^w)^s`. -/
theorem block_switching_count_explicit (cs : List (Clause n)) (w F K s : ℕ)
    (hcons : ∀ T ∈ cs, Consistent T) (hw : ∀ T ∈ cs, T.lits.length ≤ w)
    {Bad : Finset (Restriction n)}
    (hstars : ∀ ρ ∈ Bad, SwitchingCounting.stars ρ = K)
    (hdepth : ∀ ρ ∈ Bad, (blockStream cs F ρ).length = s) :
    Bad.card
      ≤ (∑ j ∈ Finset.range (K - s + 1), n.choose j * 2 ^ (n - j)) * (2 ^ w) ^ s := by
  have h := block_switching_count_tight cs w F K s hcons hw hstars hdepth
  rwa [card_stars_le (K - s)] at h

/-- **Per-star geometric gain (the heart of Håstad).**  From the binomial layer-ratio: the
`(K-s)`-shell weight is at most a `(2K/(n-K+1))^s`-fraction of the `K`-shell weight.  Stated in cleared
integer form: `C(n,K-s)·2^(n-K+s)·(n-K+1)^s ≤ C(n,K)·2^(n-K)·(2K)^s`. -/
theorem shell_ratio_nat (K s : ℕ) (hsK : s ≤ K) (hKn : K ≤ n) :
    n.choose (K - s) * 2 ^ (n - K + s) * (n - K + 1) ^ s
      ≤ n.choose K * 2 ^ (n - K) * (2 * K) ^ s := by
  have key : n.choose (K - s) * (n - K + 1) ^ s ≤ n.choose K * K ^ s :=
    binom_layer_ratio' s K hsK hKn
  calc n.choose (K - s) * 2 ^ (n - K + s) * (n - K + 1) ^ s
      = (n.choose (K - s) * (n - K + 1) ^ s) * (2 ^ (n - K) * 2 ^ s) := by
        rw [pow_add]; ring
    _ ≤ (n.choose K * K ^ s) * (2 ^ (n - K) * 2 ^ s) := by
        exact Nat.mul_le_mul_right _ key
    _ = n.choose K * 2 ^ (n - K) * (2 * K) ^ s := by rw [mul_pow]; ring

/-- **The probability bound.**  Under the uniform distribution on the `K`-star shell
`Ω = {σ : stars σ = K}` (`|Ω| = C(n,K)·2^(n-K)`), the fraction of restrictions whose block-DT has
depth `≥ s` (the set `Bad`) is bounded by the explicit holographic count divided by `|Ω|`. -/
theorem block_switching_prob_le (cs : List (Clause n)) (w F K s : ℕ)
    (hcons : ∀ T ∈ cs, Consistent T) (hw : ∀ T ∈ cs, T.lits.length ≤ w)
    {Bad : Finset (Restriction n)}
    (hstars : ∀ ρ ∈ Bad, SwitchingCounting.stars ρ = K)
    (hdepth : ∀ ρ ∈ Bad, (blockStream cs F ρ).length = s) :
    (Bad.card : ℚ) / ((n.choose K) * 2 ^ (n - K))
      ≤ ((∑ j ∈ Finset.range (K - s + 1), n.choose j * 2 ^ (n - j) : ℕ) : ℚ) * (2 ^ w : ℚ) ^ s
          / ((n.choose K) * 2 ^ (n - K)) := by
  have hcount := block_switching_count_explicit cs w F K s hcons hw hstars hdepth
  have hcast : (Bad.card : ℚ)
      ≤ ((∑ j ∈ Finset.range (K - s + 1), n.choose j * 2 ^ (n - j) : ℕ) : ℚ) * (2 ^ w : ℚ) ^ s := by
    have h := (Nat.cast_le (α := ℚ)).mpr hcount
    push_cast at h
    push_cast
    linarith [h]
  gcongr

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.block_switching_count_explicit
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.shell_ratio_nat
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.block_switching_prob_le
