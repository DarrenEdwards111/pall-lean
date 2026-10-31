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

## The geometric-tail collapse (now closed)

The cumulative sum `∑_{j≤K-s}` is collapsed into the closed Håstad form:

* `shell_ratio_nat_gen` — the per-shell integer ratio for every `j ≤ K` (generalises `shell_ratio_nat`).
* `term_ratio_q` — the per-shell ℚ bound `C(n,j)2^(n-j) ≤ |Ω|·r^(K-j)` with `r = 2K/(n-K+1)`.
* `geom_tail_le` — `∑_{i<N} r^i ≤ 1/(1-r)` for `0 ≤ r < 1`.
* `sum_term_le` — reindex (`j ↦ K-j`, `sum_range_reflect`) + geometric tail: `∑_{j≤K-s} C(n,j)2^(n-j) ≤ |Ω|·r^s/(1-r)`.
* `block_switching_prob_closed` — **the closed Håstad bound**:
  `Pr_Ω[block-DT depth ≥ s] ≤ (2^w · 2K/(n-K+1))^s / (1 - 2K/(n-K+1))`, valid in the `2K < n-K+1`
  regime (`r < 1`, i.e. `p < 1/3`).

`block_switching_prob_le` retains the exact fraction bound (count ÷ shell).  AC⁰/depth-3; not
P≠NP-strength.

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

/-! ## The geometric-tail collapse to the closed Håstad form -/

/-- **Generalised per-shell integer ratio.**  For every `j ≤ K ≤ n`:
`C(n,j)·2^(n-j)·(n-K+1)^(K-j) ≤ C(n,K)·2^(n-K)·(2K)^(K-j)`.  (`shell_ratio_nat` is the case `j = K-s`.) -/
theorem shell_ratio_nat_gen (j K : ℕ) (hjK : j ≤ K) (hKn : K ≤ n) :
    n.choose j * 2 ^ (n - j) * (n - K + 1) ^ (K - j)
      ≤ n.choose K * 2 ^ (n - K) * (2 * K) ^ (K - j) := by
  have key : n.choose j * (n - K + 1) ^ (K - j) ≤ n.choose K * K ^ (K - j) := by
    have h := binom_layer_ratio' (K - j) K (Nat.sub_le K j) hKn
    rwa [Nat.sub_sub_self hjK] at h
  have hexp : n - j = (n - K) + (K - j) := by omega
  calc n.choose j * 2 ^ (n - j) * (n - K + 1) ^ (K - j)
      = (n.choose j * (n - K + 1) ^ (K - j)) * 2 ^ (n - j) := by ring
    _ = (n.choose j * (n - K + 1) ^ (K - j)) * (2 ^ (n - K) * 2 ^ (K - j)) := by
        rw [hexp, pow_add]
    _ ≤ (n.choose K * K ^ (K - j)) * (2 ^ (n - K) * 2 ^ (K - j)) := by gcongr
    _ = n.choose K * 2 ^ (n - K) * (2 * K) ^ (K - j) := by rw [mul_pow]; ring

/-- **Per-shell ℚ ratio.**  For `j ≤ K ≤ n`, the `j`-shell weight is at most a `r^(K-j)`-fraction of
the `K`-shell weight `|Ω| = C(n,K)·2^(n-K)`, where `r = 2K/(n-K+1)`. -/
theorem term_ratio_q (j K : ℕ) (hjK : j ≤ K) (hKn : K ≤ n) :
    (↑(n.choose j) * 2 ^ (n - j) : ℚ)
      ≤ (↑(n.choose K) * 2 ^ (n - K)) * (((2 * K : ℕ) : ℚ) / ((n - K + 1 : ℕ) : ℚ)) ^ (K - j) := by
  have hnat := shell_ratio_nat_gen j K hjK hKn
  have hdpos : (0 : ℚ) < ((n - K + 1 : ℕ) : ℚ) := by exact_mod_cast Nat.succ_pos (n - K)
  have hdpow : (0 : ℚ) < ((n - K + 1 : ℕ) : ℚ) ^ (K - j) := pow_pos hdpos _
  rw [div_pow, ← mul_div_assoc, le_div_iff₀ hdpow]
  calc (↑(n.choose j) * 2 ^ (n - j) : ℚ) * ((n - K + 1 : ℕ) : ℚ) ^ (K - j)
      = ((n.choose j * 2 ^ (n - j) * (n - K + 1) ^ (K - j) : ℕ) : ℚ) := by push_cast; ring
    _ ≤ ((n.choose K * 2 ^ (n - K) * (2 * K) ^ (K - j) : ℕ) : ℚ) := by exact_mod_cast hnat
    _ = (↑(n.choose K) * 2 ^ (n - K)) * ((2 * K : ℕ) : ℚ) ^ (K - j) := by push_cast; ring

/-- **Geometric tail.**  For `0 ≤ r < 1`, `∑_{i<N} r^i ≤ 1/(1-r)`. -/
theorem geom_tail_le {r : ℚ} (h0 : 0 ≤ r) (h1 : r < 1) (N : ℕ) :
    ∑ i ∈ Finset.range N, r ^ i ≤ 1 / (1 - r) := by
  have hd : (0 : ℚ) < 1 - r := by linarith
  have hne : (1 : ℚ) - r ≠ 0 := ne_of_gt hd
  have hpart : (1 - r) * ∑ i ∈ Finset.range N, r ^ i = 1 - r ^ N := by
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ, mul_add, ih, pow_succ]; ring
  have key : ∑ i ∈ Finset.range N, r ^ i = (1 - r ^ N) / (1 - r) := by
    rw [eq_div_iff hne, mul_comm]; exact hpart
  rw [key]
  have h2 : 1 / (1 - r) - (1 - r ^ N) / (1 - r) = r ^ N / (1 - r) := by field_simp; ring
  have h3 : 0 ≤ r ^ N / (1 - r) := div_nonneg (pow_nonneg h0 N) (le_of_lt hd)
  linarith [h2, h3]

/-- **Cumulative-sum collapse.**  In the `2K < n-K+1` regime (`r < 1`):
`∑_{j≤K-s} C(n,j)·2^(n-j) ≤ |Ω|·r^s/(1-r)`, where `r = 2K/(n-K+1)`. -/
theorem sum_term_le (K s : ℕ) (hsK : s ≤ K) (hKn : K ≤ n) (hr : 2 * K < n - K + 1) :
    ∑ j ∈ Finset.range (K - s + 1), (↑(n.choose j) * 2 ^ (n - j) : ℚ)
      ≤ (↑(n.choose K) * 2 ^ (n - K)) *
          ((((2 * K : ℕ) : ℚ) / ((n - K + 1 : ℕ) : ℚ)) ^ s
            / (1 - ((2 * K : ℕ) : ℚ) / ((n - K + 1 : ℕ) : ℚ))) := by
  have hdpos : (0 : ℚ) < ((n - K + 1 : ℕ) : ℚ) := by exact_mod_cast Nat.succ_pos (n - K)
  set r : ℚ := ((2 * K : ℕ) : ℚ) / ((n - K + 1 : ℕ) : ℚ) with hr_def
  have hrnn : (0 : ℚ) ≤ r := by rw [hr_def]; positivity
  have hr1 : r < 1 := by rw [hr_def, div_lt_one hdpos]; exact_mod_cast hr
  -- termwise bound, then factor out |Ω|
  have step1 : ∑ j ∈ Finset.range (K - s + 1), (↑(n.choose j) * 2 ^ (n - j) : ℚ)
      ≤ ∑ j ∈ Finset.range (K - s + 1), (↑(n.choose K) * 2 ^ (n - K)) * r ^ (K - j) := by
    apply Finset.sum_le_sum
    intro j hj
    have hjK : j ≤ K := by rw [Finset.mem_range] at hj; omega
    rw [hr_def]; exact term_ratio_q j K hjK hKn
  rw [← Finset.mul_sum] at step1
  refine step1.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  -- remaining: ∑_{j≤K-s} r^(K-j) ≤ r^s/(1-r)
  have hsum_eq : ∑ j ∈ Finset.range (K - s + 1), r ^ (K - j)
      = r ^ s * ∑ j ∈ Finset.range (K - s + 1), r ^ ((K - s) - j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    rw [← pow_add]
    congr 1
    omega
  have hreflect : ∑ j ∈ Finset.range (K - s + 1), r ^ ((K - s) - j)
      = ∑ i ∈ Finset.range (K - s + 1), r ^ i := by
    have hcore := Finset.sum_range_reflect (fun k => r ^ k) (K - s + 1)
    rw [← hcore]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Nat.add_sub_cancel]
  calc ∑ j ∈ Finset.range (K - s + 1), r ^ (K - j)
      = r ^ s * ∑ j ∈ Finset.range (K - s + 1), r ^ ((K - s) - j) := hsum_eq
    _ = r ^ s * ∑ i ∈ Finset.range (K - s + 1), r ^ i := by rw [hreflect]
    _ ≤ r ^ s * (1 / (1 - r)) :=
        mul_le_mul_of_nonneg_left (geom_tail_le hrnn hr1 (K - s + 1)) (pow_nonneg hrnn s)
    _ = r ^ s / (1 - r) := by rw [mul_one_div]

/-- **The closed Håstad bound (count → probability, tail collapsed).**  In the `2K < n-K+1` regime
(`r = 2K/(n-K+1) < 1`, i.e. `p < 1/3`), the fraction of the `K`-star shell whose block-DT has depth
`≥ s` decays geometrically:
`Pr_Ω[block-DT depth ≥ s] ≤ (2^w · 2K/(n-K+1))^s / (1 - 2K/(n-K+1))`. -/
theorem block_switching_prob_closed (cs : List (Clause n)) (w F K s : ℕ)
    (hcons : ∀ T ∈ cs, Consistent T) (hw : ∀ T ∈ cs, T.lits.length ≤ w)
    {Bad : Finset (Restriction n)}
    (hstars : ∀ ρ ∈ Bad, SwitchingCounting.stars ρ = K)
    (hdepth : ∀ ρ ∈ Bad, (blockStream cs F ρ).length = s)
    (hsK : s ≤ K) (hKn : K ≤ n) (hr : 2 * K < n - K + 1) :
    (Bad.card : ℚ) / ((n.choose K) * 2 ^ (n - K))
      ≤ ((2 : ℚ) ^ w * (((2 * K : ℕ) : ℚ) / ((n - K + 1 : ℕ) : ℚ))) ^ s
          / (1 - ((2 * K : ℕ) : ℚ) / ((n - K + 1 : ℕ) : ℚ)) := by
  have hcpos : 0 < n.choose K := Nat.choose_pos hKn
  have hDc : (0 : ℚ) < ↑(n.choose K) := by exact_mod_cast hcpos
  have hD : (0 : ℚ) < ↑(n.choose K) * 2 ^ (n - K) := mul_pos hDc (by positivity)
  have hcount := block_switching_count_explicit cs w F K s hcons hw hstars hdepth
  have hbad : (Bad.card : ℚ)
      ≤ (∑ j ∈ Finset.range (K - s + 1), (↑(n.choose j) * 2 ^ (n - j) : ℚ)) * ((2 : ℚ) ^ w) ^ s := by
    exact_mod_cast hcount
  have hsum := sum_term_le K s hsK hKn hr
  rw [div_le_iff₀ hD]
  calc (Bad.card : ℚ)
      ≤ (∑ j ∈ Finset.range (K - s + 1), (↑(n.choose j) * 2 ^ (n - j) : ℚ)) * ((2 : ℚ) ^ w) ^ s :=
        hbad
    _ ≤ ((↑(n.choose K) * 2 ^ (n - K)) *
          ((((2 * K : ℕ) : ℚ) / ((n - K + 1 : ℕ) : ℚ)) ^ s
            / (1 - ((2 * K : ℕ) : ℚ) / ((n - K + 1 : ℕ) : ℚ)))) * ((2 : ℚ) ^ w) ^ s :=
        mul_le_mul_of_nonneg_right hsum (by positivity)
    _ = ((2 : ℚ) ^ w * (((2 * K : ℕ) : ℚ) / ((n - K + 1 : ℕ) : ℚ))) ^ s
          / (1 - ((2 * K : ℕ) : ℚ) / ((n - K + 1 : ℕ) : ℚ)) * (↑(n.choose K) * 2 ^ (n - K)) := by
        rw [mul_pow]; ring

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.block_switching_count_explicit
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.shell_ratio_nat
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.block_switching_prob_le
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.sum_term_le
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.block_switching_prob_closed
