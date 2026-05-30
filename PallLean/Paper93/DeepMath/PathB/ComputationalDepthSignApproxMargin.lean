import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Margin-controlled polynomial approximation of `sign` (the positive brick)

The cheap-bottom-realizer question (see `ComputationalDepthMarginFreeUPP.lean`)
reduces to one analytic statement: a low-degree polynomial approximating `sign`
on `{ |z| ≥ γ }`.  This file proves the **quantitative** version, with the
degree's dependence on the margin `γ` fully explicit.

The construction is the truncated binomial series for `|z|⁻¹ = (1 - (1-z²))^{-1/2}`:
`p_N(z) = z · ∑_{i≤N} C(2i,i)/4^i · (1-z²)^i`, a polynomial of degree `2N+1`.
The approximation error is the binomial *tail*, which — because the central
binomial coefficients satisfy `C(2i,i)/4^i ≤ 1` — is dominated by a geometric
series:

  `|p_N(z) − sign z| ≤ (1−γ²)^{N+1} / γ²`   for `γ ≤ |z| ≤ 1`.

So to reach error `ε` one needs `N+1 ≥ log(1/(εγ²)) / log(1/(1−γ²)) = Θ((1/γ²)·log(1/(εγ)))`,
i.e. the degree blows up polynomially in `1/γ` as the margin shrinks — this is the
quantitative wall, now an explicit theorem (`exists_sign_approx_margin`).

**Honest scope.**  The whole *quantitative* content (the tail/degree bound) is
proved here.  It rests on the single classical identity
`(1−u)^{-1/2} = ∑_i C(2i,i)/4^i · u^i` (`centralBinomGF`), carried as an explicit
hypothesis: Mathlib has the abstract generalized binomial series but not this
central-binomial specialization in `HasSum` form.  Discharging `centralBinomGF`
(via `Ring.choose (-1/2)` ↔ `centralBinom/4^i`) is the remaining, self-contained
formalization step — it is `γ`- and `ε`-independent, so it does NOT touch the
quantitative wall above.
-/

namespace PallLean.Paper93.DeepMath.PathB.SignApproxMargin

open scoped BigOperators

/-- The central binomial coefficients satisfy `C(2i,i) ≤ 4^i`, hence
`C(2i,i)/4^i ∈ [0,1]`. -/
theorem centralBinom_div_four_pow_le_one (i : ℕ) :
    (Nat.centralBinom i / 4 ^ i : ℝ) ≤ 1 := by
  have h4 : (0 : ℝ) < 4 ^ i := by positivity
  rw [div_le_one h4]
  have hnat : Nat.centralBinom i ≤ 4 ^ i := by
    have hsum : Nat.centralBinom i ≤ ∑ k ∈ Finset.range (2 * i + 1), (2 * i).choose k := by
      rw [Nat.centralBinom]
      exact Finset.single_le_sum (f := fun k => (2 * i).choose k)
        (fun k _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
    calc Nat.centralBinom i ≤ ∑ k ∈ Finset.range (2 * i + 1), (2 * i).choose k := hsum
      _ = 2 ^ (2 * i) := Nat.sum_range_choose (2 * i)
      _ = 4 ^ i := by rw [pow_mul]; norm_num
  calc (Nat.centralBinom i : ℝ) ≤ ((4 ^ i : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = (4 : ℝ) ^ i := by push_cast; ring

theorem centralBinom_div_four_pow_nonneg (i : ℕ) :
    (0 : ℝ) ≤ (Nat.centralBinom i / 4 ^ i : ℝ) := by positivity

/-- **The central-binomial generating function**, carried as a hypothesis:
`(1-u)^{-1/2} = ∑_i C(2i,i)/4^i · u^i` for `0 ≤ u < 1` (here `(1-u)^{-1/2}` is
written `(√(1-u))⁻¹`).  Classical; Mathlib has the abstract generalized binomial
series but not this specialization. -/
def CentralBinomGF : Prop :=
  ∀ u : ℝ, 0 ≤ u → u < 1 →
    HasSum (fun i => (Nat.centralBinom i / 4 ^ i : ℝ) * u ^ i) (Real.sqrt (1 - u))⁻¹

/-- **Quantitative tail bound (the quantitative core).**  Modulo the central
binomial generating function, the degree-`(2N+1)` truncation
`z · ∑_{i≤N} C(2i,i)/4^i (1-z²)^i` approximates `sign z` to error
`(1-γ²)^{N+1}/γ²` on the margin band `γ ≤ |z| ≤ 1`. -/
theorem sign_approx_tail_bound (hGF : CentralBinomGF)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (N : ℕ) {z : ℝ} (hz : γ ≤ |z|) (hz1 : |z| ≤ 1) :
    |z * (∑ i ∈ Finset.range (N + 1), (Nat.centralBinom i / 4 ^ i : ℝ) * (1 - z ^ 2) ^ i)
        - (if 0 < z then (1 : ℝ) else -1)| ≤ (1 - γ ^ 2) ^ (N + 1) / γ ^ 2 := by
  -- set `u = 1 - z²`
  set u : ℝ := 1 - z ^ 2 with hu
  have hzsq_ge : γ ^ 2 ≤ z ^ 2 := by
    rw [← sq_abs z]; exact pow_le_pow_left₀ hγ0.le hz 2
  have hzsq_le : z ^ 2 ≤ 1 := by rw [← sq_abs z]; nlinarith [abs_nonneg z, hz1]
  have hu_nonneg : 0 ≤ u := by rw [hu]; linarith
  have hu_lt : u < 1 := by rw [hu]; nlinarith [hγ0]
  have hu_le : u ≤ 1 - γ ^ 2 := by rw [hu]; linarith
  have hzsq_pos : 0 < z ^ 2 := lt_of_lt_of_le (by positivity) hzsq_ge
  -- the generating function at `u`, and `(√(1-u))⁻¹ = |z|⁻¹`
  have hsum := hGF u hu_nonneg hu_lt
  have h1u : (1 : ℝ) - u = z ^ 2 := by rw [hu]; ring
  -- the geometric dominating series
  have hgeo : HasSum (fun i => u ^ i) (1 - u)⁻¹ := hasSum_geometric_of_lt_one hu_nonneg hu_lt
  set c : ℕ → ℝ := fun i => (Nat.centralBinom i / 4 ^ i : ℝ) with hc
  have hcle : ∀ i, c i * u ^ i ≤ u ^ i := fun i => by
    rw [hc]
    have := centralBinom_div_four_pow_le_one i
    nlinarith [pow_nonneg hu_nonneg i, centralBinom_div_four_pow_nonneg i]
  have hcnonneg : ∀ i, 0 ≤ c i * u ^ i := fun i =>
    mul_nonneg (centralBinom_div_four_pow_nonneg i) (pow_nonneg hu_nonneg i)
  -- tail = total − partial
  have htail : (Real.sqrt (1 - u))⁻¹ - (∑ i ∈ Finset.range (N + 1), c i * u ^ i)
      = ∑' i, c (i + (N + 1)) * u ^ (i + (N + 1)) := by
    rw [← hsum.tsum_eq, ← Summable.sum_add_tsum_nat_add (N + 1) hsum.summable]
    ring
  -- |tail| ≤ geometric tail = u^{N+1}/(1-u)
  have hsummf : Summable (fun i => c (i + (N + 1)) * u ^ (i + (N + 1))) :=
    hsum.summable.comp_injective (add_left_injective (N + 1))
  have hsummg : Summable (fun i => u ^ (i + (N + 1))) :=
    hgeo.summable.comp_injective (add_left_injective (N + 1))
  have htailbound : |∑' i, c (i + (N + 1)) * u ^ (i + (N + 1))| ≤ u ^ (N + 1) / (1 - u) := by
    rw [abs_of_nonneg (tsum_nonneg (fun i => hcnonneg _))]
    refine (Summable.tsum_le_tsum (fun i => hcle _) hsummf hsummg).trans (le_of_eq ?_)
    rw [show (∑' i, u ^ (i + (N + 1))) = ∑' i, u ^ (N + 1) * u ^ i from
      tsum_congr (fun i => by rw [pow_add]; ring)]
    rw [tsum_mul_left, hgeo.tsum_eq, div_eq_mul_inv]
  -- combine: |partial − |z|⁻¹| ≤ u^{N+1}/(1-u)
  have hsqrt : (Real.sqrt (1 - u))⁻¹ = |z|⁻¹ := by
    rw [h1u, Real.sqrt_sq_eq_abs]
  have hpart : |(∑ i ∈ Finset.range (N + 1), c i * u ^ i) - |z|⁻¹| ≤ u ^ (N + 1) / (1 - u) := by
    have hthis := htailbound
    rw [← htail, hsqrt] at hthis
    rwa [abs_sub_comm] at hthis
  -- multiply by |z| ≤ 1 and identify z·|z|⁻¹ = sign z
  have hzne : z ≠ 0 := by rw [← abs_pos]; linarith
  have hsign : z * |z|⁻¹ = (if 0 < z then (1 : ℝ) else -1) := by
    rcases lt_or_gt_of_ne hzne with hlt | hgt
    · rw [if_neg (not_lt.mpr hlt.le), abs_of_neg hlt, ← div_eq_mul_inv, div_neg, div_self hzne]
    · rw [if_pos hgt, abs_of_pos hgt, ← div_eq_mul_inv, div_self hzne]
  have hfactor : z * (∑ i ∈ Finset.range (N + 1), c i * u ^ i) - (if 0 < z then (1 : ℝ) else -1)
      = z * ((∑ i ∈ Finset.range (N + 1), c i * u ^ i) - |z|⁻¹) := by
    rw [← hsign]; ring
  rw [hfactor, abs_mul]
  calc |z| * |(∑ i ∈ Finset.range (N + 1), c i * u ^ i) - |z|⁻¹|
      ≤ 1 * (u ^ (N + 1) / (1 - u)) := mul_le_mul hz1 hpart (abs_nonneg _) (by norm_num)
    _ = u ^ (N + 1) / z ^ 2 := by rw [one_mul, h1u]
    _ ≤ (1 - γ ^ 2) ^ (N + 1) / γ ^ 2 :=
        div_le_div₀ (pow_nonneg (le_trans hu_nonneg hu_le) (N + 1))
          (pow_le_pow_left₀ hu_nonneg hu_le (N + 1)) (by positivity) hzsq_ge

/-- **Margin-controlled sign approximation (the positive brick).**  Modulo the
central-binomial generating function, for every margin `γ ∈ (0,1]` and accuracy
`ε > 0` there is a degree-`(2N+1)` polynomial approximating `sign` to error `ε` on
`γ ≤ |z| ≤ 1`, with `N` the least integer making `(1-γ²)^N < εγ²` — i.e.
`N = Θ((1/γ²)·log(1/(εγ)))`.  The degree's `1/γ` blow-up as the margin shrinks is
the quantitative wall, now explicit. -/
theorem exists_sign_approx_margin (hGF : CentralBinomGF)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ z : ℝ, γ ≤ |z| → |z| ≤ 1 →
      |z * (∑ i ∈ Finset.range (N + 1), (Nat.centralBinom i / 4 ^ i : ℝ) * (1 - z ^ 2) ^ i)
          - (if 0 < z then (1 : ℝ) else -1)| ≤ ε := by
  have h1γ : (0 : ℝ) ≤ 1 - γ ^ 2 := by nlinarith
  have h1γ1 : 1 - γ ^ 2 < 1 := by nlinarith
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (by positivity : (0 : ℝ) < ε * γ ^ 2) h1γ1
  refine ⟨n, fun z hz hz1 => (sign_approx_tail_bound hGF hγ0 hγ1 n hz hz1).trans ?_⟩
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < γ ^ 2)]
  calc (1 - γ ^ 2) ^ (n + 1)
      ≤ (1 - γ ^ 2) ^ n := pow_le_pow_of_le_one h1γ (le_of_lt h1γ1) (Nat.le_succ n)
    _ ≤ ε * γ ^ 2 := le_of_lt hn

/-- **Coefficient form (bridge interface).**  Repackages
`exists_sign_approx_margin` as a standard monomial polynomial `∑_b a_b z^b` (the
form the circuit bridge `weightedApproxRealizer_ofPolyApprox` consumes), by taking
the coefficients of `X · ∑_i C(2i,i)/4^i (1-X²)^i`. -/
theorem exists_sign_approx_margin_coeffs (hGF : CentralBinomGF)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ (d : ℕ) (a : ℕ → ℝ), ∀ z : ℝ, γ ≤ |z| → |z| ≤ 1 →
      |(∑ b ∈ Finset.range (d + 1), a b * z ^ b) - (if 0 < z then (1 : ℝ) else -1)| ≤ ε := by
  obtain ⟨N, hN⟩ := exists_sign_approx_margin hGF hγ0 hγ1 hε
  set P : Polynomial ℝ :=
    Polynomial.X * ∑ i ∈ Finset.range (N + 1),
      Polynomial.C (Nat.centralBinom i / 4 ^ i : ℝ) * (1 - Polynomial.X ^ 2) ^ i with hP
  have hPeval : ∀ z : ℝ, P.eval z
      = z * ∑ i ∈ Finset.range (N + 1), (Nat.centralBinom i / 4 ^ i : ℝ) * (1 - z ^ 2) ^ i := by
    intro z
    rw [hP]
    simp [Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_C, Polynomial.eval_X]
  refine ⟨P.natDegree, P.coeff, fun z hz hz1 => ?_⟩
  rw [← Polynomial.eval_eq_sum_range, hPeval z]
  exact hN z hz hz1

end PallLean.Paper93.DeepMath.PathB.SignApproxMargin

#print axioms PallLean.Paper93.DeepMath.PathB.SignApproxMargin.sign_approx_tail_bound
#print axioms PallLean.Paper93.DeepMath.PathB.SignApproxMargin.exists_sign_approx_margin
