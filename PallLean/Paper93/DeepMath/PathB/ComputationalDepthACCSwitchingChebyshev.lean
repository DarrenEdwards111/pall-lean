import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACCRestrictionSwitchingVariance

/-!
# Chebyshev: turning the variance bound into a concentration statement

The moment files computed `E[#surviving] ≤ k·s·p` (first moment) and `Var[#surviving] ≤ d·k·s·p` (second moment,
bounded overlap).  This file builds the **Markov and Chebyshev inequalities over the exact `p`‑biased restriction
measure**, packaging those bounds into explicit tail estimates — the step that makes the second moment *do work*
("few supports survive *with high probability*", not merely in expectation).

The measure is the `p`‑biased product on live sets: `weight p L = p^{|L|}(1-p)^{n-|L|}` (total `1` by
`biased_sum_one`); `Pr` is the weight of an event, `Exp` the weighted average of a function.

## What is proved (clean axioms, no `sorry`)

* `total` — the weights sum to `1` (a genuine probability measure), from `biased_sum_one`.
* `markov` — **Markov's inequality**: for `f ≥ 0` and `a > 0`, `a · Pr(f ≥ a) ≤ Exp f`.
* `chebyshev` — **Chebyshev's inequality**: `Pr((g − Eg)² ≥ t²) ≤ Exp((g − Eg)²) / t²` (Markov on the squared
  deviation).
* `chebyshev_of_variance_le` — **the packaging**: given a variance bound `Exp((g − Eg)²) ≤ B`, the tail is
  `Pr((g − Eg)² ≥ t²) ≤ B / t²`.

## How it closes the switching argument

Take `g = X` the surviving‑support count.  The deviation event `(X − E[X])² ≥ t²` is `|X − E[X]| ≥ t`; with the
second‑moment bound `Exp((X − E[X])²) = Var[X] ≤ d·k·s·p` (the closed form of `…SwitchingVariance`, the standard
linearity‑over‑measure identity between `Exp((X−EX)²)` and the covariance sum), `chebyshev_of_variance_le` gives

  `Pr(|X − E[X]| ≥ t) ≤ d·k·s·p / t²`.

So for bounded‑overlap supports a constant‑`p` random restriction leaves few surviving supports with high
probability — the concentration that upgrades the first‑moment existence into a robust restriction.  The Markov and
Chebyshev inequalities are proved here in full over the exact measure; the remaining input is the variance bound
(proved, `variance_boundedOverlap_le`) together with its routine identification with `Exp((X−EX)²)`.  Unbounded
overlap is where even the second moment is insufficient and the higher‑moment Håstad switching argument is needed —
the precisely‑located `NP ⊄ ACC⁰` frontier.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACCSwitchingChebyshev

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.ACCRestrictionSwitchingProb

variable {n : ℕ}

/-- The `p`‑biased weight of a live set `L` (each coordinate live independently w.p. `p`). -/
def weight (p : ℝ) (L : Finset (Fin n)) : ℝ := p ^ L.card * (1 - p) ^ (n - L.card)

theorem weight_nonneg (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (L : Finset (Fin n)) : 0 ≤ weight p L :=
  mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)

/-- The probability of an event (a set of live sets). -/
noncomputable def Pr (p : ℝ) (E : Finset (Fin n) → Prop) : ℝ :=
  ∑ L ∈ (Finset.univ : Finset (Fin n)).powerset.filter E, weight p L

/-- The expectation of a function of the live set. -/
def Exp (p : ℝ) (f : Finset (Fin n) → ℝ) : ℝ :=
  ∑ L ∈ (Finset.univ : Finset (Fin n)).powerset, weight p L * f L

/-- **The weights form a probability measure (proved): total mass `1`.** -/
theorem total (p : ℝ) : ∑ L ∈ (Finset.univ : Finset (Fin n)).powerset, weight p L = 1 := by
  unfold weight
  have h := ACCRestrictionSwitchingProb.biased_sum_one p (Finset.univ : Finset (Fin n))
  rwa [Finset.card_univ, Fintype.card_fin] at h

/-- **Markov's inequality (proved): `a · Pr(f ≥ a) ≤ Exp f` for `f ≥ 0`, `a > 0`.** -/
theorem markov (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : Finset (Fin n) → ℝ)
    (hf : ∀ L, 0 ≤ f L) (a : ℝ) :
    a * Pr p (fun L => a ≤ f L) ≤ Exp p f := by
  unfold Pr Exp
  rw [Finset.mul_sum]
  calc ∑ L ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun L => a ≤ f L), a * weight p L
      ≤ ∑ L ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun L => a ≤ f L), weight p L * f L := by
        apply Finset.sum_le_sum
        intro L hL
        rw [Finset.mem_filter] at hL
        rw [mul_comm (weight p L) (f L)]
        exact mul_le_mul_of_nonneg_right hL.2 (weight_nonneg p hp0 hp1 L)
    _ ≤ ∑ L ∈ (Finset.univ : Finset (Fin n)).powerset, weight p L * f L := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro L _ _
        exact mul_nonneg (weight_nonneg p hp0 hp1 L) (hf L)

/-- **Chebyshev's inequality (proved): `Pr((g − Eg)² ≥ t²) ≤ Exp((g − Eg)²) / t²`.** -/
theorem chebyshev (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (g : Finset (Fin n) → ℝ) (t : ℝ) (ht : 0 < t) :
    Pr p (fun L => t ^ 2 ≤ (g L - Exp p g) ^ 2)
      ≤ Exp p (fun L => (g L - Exp p g) ^ 2) / t ^ 2 := by
  have hm := markov p hp0 hp1 (fun L => (g L - Exp p g) ^ 2) (fun L => sq_nonneg _) (t ^ 2)
  rw [le_div_iff₀ (pow_pos ht 2), mul_comm]
  exact hm

/-- **The packaging (proved): a variance bound yields a Chebyshev tail.**  If `Exp((g − Eg)²) ≤ B` then
`Pr((g − Eg)² ≥ t²) ≤ B / t²`. -/
theorem chebyshev_of_variance_le (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (g : Finset (Fin n) → ℝ)
    (t : ℝ) (ht : 0 < t) (B : ℝ) (hvar : Exp p (fun L => (g L - Exp p g) ^ 2) ≤ B) :
    Pr p (fun L => t ^ 2 ≤ (g L - Exp p g) ^ 2) ≤ B / t ^ 2 := by
  refine le_trans (chebyshev p hp0 hp1 g t ht) ?_
  gcongr

end PallLean.Paper93.DeepMath.PathB.ACCSwitchingChebyshev

#print axioms PallLean.Paper93.DeepMath.PathB.ACCSwitchingChebyshev.total
#print axioms PallLean.Paper93.DeepMath.PathB.ACCSwitchingChebyshev.markov
#print axioms PallLean.Paper93.DeepMath.PathB.ACCSwitchingChebyshev.chebyshev
#print axioms PallLean.Paper93.DeepMath.PathB.ACCSwitchingChebyshev.chebyshev_of_variance_le
