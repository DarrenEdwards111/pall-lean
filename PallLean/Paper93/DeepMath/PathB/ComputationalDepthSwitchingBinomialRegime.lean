import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-!
# The binomial-ratio parameter regime numerics

The collapse needs the switching ratio below `1`: with `|F| = |{stars=K}| = C(n,K)·2^(n-K)` and
`|Short| = |{stars=K-s}| = C(n,K-s)·2^(n-K+s)`, the parameter inequality `|Short|·(2w)^s ≤ |F|`
reduces (cancelling the `2`-powers, `2^s·(2w)^s = (4w)^s`) to the **binomial ratio**

  `C(n,K-s)·(4w)^s ≤ C(n,K)`.

This file proves it, from a clean combinatorial induction (no analysis, no `sorry`):

* `choose_step` — one ratio step: `r·(k+1) ≤ n-k ⟹ r·C(n,k) ≤ C(n,k+1)`
  (from `Nat.choose_succ_right_eq : C(n,k+1)·(k+1) = C(n,k)·(n-k)`).
* `pow_mul_choose_le` — iterate: if every factor `k ∈ [m, m+s)` satisfies `r·(k+1) ≤ n-k`, then
  `r^s·C(n,m) ≤ C(n,m+s)`.
* `binomial_ratio_regime` — **the regime**: under `(4w)·K + K ≤ n+1` (i.e. `(4w+1)·K ≤ n+1`, so
  `K ≲ n/(4w)`) and `s ≤ K`,  `(4w)^s·C(n,K-s) ≤ C(n,K)`.
* `short_family_ratio` — the parameter inequality itself: `|Short|·(2w)^s ≤ |F|`, i.e.
  `2^(n-K+s)·C(n,K-s)·(2w)^s ≤ 2^(n-K)·C(n,K)`.

So in the regime `(4w+1)·K ≤ n+1` the switching ratio is `≤ 1`; a strict `< 1` (which the
pigeonhole `exists_good_restriction_in` consumes) follows from any one unit of slack in the regime.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

/-- **One binomial-ratio step.**  If `r·(k+1) ≤ n-k`, then `r·C(n,k) ≤ C(n,k+1)`. -/
theorem choose_step {n r k : ℕ} (h : r * (k + 1) ≤ n - k) :
    r * n.choose k ≤ n.choose (k + 1) := by
  have hid : n.choose (k + 1) * (k + 1) = n.choose k * (n - k) := Nat.choose_succ_right_eq n k
  have hstep : r * n.choose k * (k + 1) ≤ n.choose (k + 1) * (k + 1) := by
    calc r * n.choose k * (k + 1) = r * (k + 1) * n.choose k := by ring
      _ ≤ (n - k) * n.choose k := mul_le_mul_right' h (n.choose k)
      _ = n.choose k * (n - k) := by ring
      _ = n.choose (k + 1) * (k + 1) := hid.symm
  exact Nat.le_of_mul_le_mul_right hstep (Nat.succ_pos k)

/-- **Iterated binomial ratio.**  If every factor in `[m, m+s)` satisfies `r·(k+1) ≤ n-k`, then
`r^s·C(n,m) ≤ C(n,m+s)`. -/
theorem pow_mul_choose_le {n r m : ℕ} :
    ∀ s, (∀ k, m ≤ k → k < m + s → r * (k + 1) ≤ n - k) →
      r ^ s * n.choose m ≤ n.choose (m + s) := by
  intro s
  induction s with
  | zero => intro _; simp
  | succ s ih =>
    intro hk
    have ih' := ih (fun k hk1 hk2 => hk k hk1 (by omega))
    calc r ^ (s + 1) * n.choose m = r * (r ^ s * n.choose m) := by ring
      _ ≤ r * n.choose (m + s) := mul_le_mul_left' ih' r
      _ ≤ n.choose (m + s + 1) := choose_step (hk (m + s) (by omega) (by omega))

/-- **The binomial-ratio regime.**  Under `(4w)·K + K ≤ n+1` (so `K ≲ n/(4w)`) and `s ≤ K`,
`(4w)^s·C(n,K-s) ≤ C(n,K)`: the switching ratio is `≤ 1`. -/
theorem binomial_ratio_regime {n w K s : ℕ} (hsK : s ≤ K) (hreg : (4 * w) * K + K ≤ n + 1) :
    (4 * w) ^ s * n.choose (K - s) ≤ n.choose K := by
  have hfac : ∀ k, K - s ≤ k → k < (K - s) + s → (4 * w) * (k + 1) ≤ n - k := by
    intro k _ hk2
    have hkK : k + 1 ≤ K := by rw [Nat.sub_add_cancel hsK] at hk2; omega
    have hmul : (4 * w) * (k + 1) ≤ (4 * w) * K := mul_le_mul_left' hkK (4 * w)
    omega
  have h := pow_mul_choose_le s hfac
  rwa [Nat.sub_add_cancel hsK] at h

/-- **The parameter inequality.**  `|Short|·(2w)^s ≤ |F|`, i.e.
`2^(n-K+s)·C(n,K-s)·(2w)^s ≤ 2^(n-K)·C(n,K)`, in the regime `(4w+1)·K ≤ n+1`.  The `2`-powers absorb
the `2^s` (`2^s·(2w)^s = (4w)^s`) and the binomial ratio finishes. -/
theorem short_family_ratio {n w K s : ℕ} (hsK : s ≤ K) (hreg : (4 * w) * K + K ≤ n + 1) :
    2 ^ (n - K + s) * n.choose (K - s) * (2 * w) ^ s ≤ 2 ^ (n - K) * n.choose K := by
  have hbin := binomial_ratio_regime hsK hreg
  have hpow : (2 : ℕ) ^ (n - K + s) = 2 ^ (n - K) * 2 ^ s := pow_add 2 (n - K) s
  have hmul : (2 * w) ^ s * 2 ^ s = (4 * w) ^ s := by rw [← mul_pow]; congr 1; ring
  calc 2 ^ (n - K + s) * n.choose (K - s) * (2 * w) ^ s
      = 2 ^ (n - K) * (n.choose (K - s) * ((2 * w) ^ s * 2 ^ s)) := by rw [hpow]; ring
    _ = 2 ^ (n - K) * (n.choose (K - s) * (4 * w) ^ s) := by rw [hmul]
    _ = 2 ^ (n - K) * ((4 * w) ^ s * n.choose (K - s)) := by ring
    _ ≤ 2 ^ (n - K) * n.choose K := by gcongr

/-- **The strict binomial step (doubled slack).**  Under `(8w)·K + K ≤ n+1` (i.e. `(8w+1)·K ≤ n+1`,
twice the slack of the `≤ 1` regime) and `s < K`,

  `8w·C(n,K-s-1) ≤ C(n,K-s)`,

i.e. the single-step binomial ratio is `≤ 1/2`.  This is `choose_step` with the constant `8w`
(the factor of `2` margin over the `4w` of `binomial_ratio_regime`). -/
theorem binomial_ratio_strict_step {n w K s : ℕ} (hs : s < K)
    (hreg : (8 * w) * K + K ≤ n + 1) :
    (8 * w) * n.choose (K - (s + 1)) ≤ n.choose (K - s) := by
  have hKs : K - s = (K - (s + 1)) + 1 := by omega
  rw [hKs]
  refine choose_step ?_
  have hmul : (8 * w) * ((K - (s + 1)) + 1) ≤ (8 * w) * K :=
    mul_le_mul_left' (by omega) (8 * w)
  omega

/-- **Count-form decay.**  The switching count `M_s = 2^(n-K+s)·C(n,K-s)·(2w)^s` at least **halves**
at each step, in the doubled-slack regime `(8w)·K + K ≤ n+1`:

  `2·M_{s+1} ≤ M_s`   for `s < K`.

This is exactly the decay hypothesis the geometric tail-sum (`geom_range_sum`) consumes: the deep
fraction is then geometrically dominated, so `∑_{s≥T} M_s ≤ 2·M_T`. -/
theorem count_decay_step {n w K s : ℕ} (hs : s < K) (hreg : (8 * w) * K + K ≤ n + 1) :
    2 * (2 ^ (n - K + (s + 1)) * n.choose (K - (s + 1)) * (2 * w) ^ (s + 1))
      ≤ 2 ^ (n - K + s) * n.choose (K - s) * (2 * w) ^ s := by
  have hstep := binomial_ratio_strict_step hs hreg
  have hexp : n - K + (s + 1) = (n - K + s) + 1 := by omega
  rw [hexp, pow_succ, pow_succ]
  calc 2 * (2 ^ (n - K + s) * 2 * n.choose (K - (s + 1)) * ((2 * w) ^ s * (2 * w)))
      = (2 ^ (n - K + s) * (2 * w) ^ s) * ((8 * w) * n.choose (K - (s + 1))) := by ring
    _ ≤ (2 ^ (n - K + s) * (2 * w) ^ s) * n.choose (K - s) := mul_le_mul_left' hstep _
    _ = 2 ^ (n - K + s) * n.choose (K - s) * (2 * w) ^ s := by ring

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.binomial_ratio_regime
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.short_family_ratio
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.binomial_ratio_strict_step
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.count_decay_step
