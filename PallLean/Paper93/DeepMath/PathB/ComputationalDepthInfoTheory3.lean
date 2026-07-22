import PallLean.Paper93.DeepMath.PathB.ComputationalDepthInfoTheory2

/-!
# Information-theory foundations 3: the Gibbs / KL inequality

The key inequality behind `I(X;Y) ≥ 0` and subadditivity: relative entropy (KL
divergence) is nonnegative.  Proved elementarily from `log x ≤ x − 1`.

* **`gibbs` (proved)** — for a distribution `p` and a subprobability `q` with
  `q i > 0` wherever `p i > 0`: `∑ p i · log(q i / p i) ≤ 0`;
* **`kl_nonneg` (proved)** — `0 ≤ ∑ p i · log(p i / q i)`: KL divergence `D(p‖q) ≥ 0`.

The per-term bound `p·log(q/p) ≤ q − p` (from `log(q/p) ≤ q/p − 1`) sums to
`∑ q − ∑ p ≤ 0`.  Real analysis, not `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.InfoTheory

open Real Finset

variable {γ : Type*} [Fintype γ]

/-- **The Gibbs inequality (proved)**: `∑ p·log(q/p) ≤ 0` for a distribution `p`
and a subprobability `q` absolutely continuous w.r.t. `p`. -/
theorem gibbs {p q : γ → ℝ}
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∑ i, q i ≤ 1)
    (hac : ∀ i, 0 < p i → 0 < q i) :
    ∑ i, p i * Real.log (q i / p i) ≤ 0 := by
  have hterm : ∀ i, p i * Real.log (q i / p i) ≤ q i - p i := by
    intro i
    by_cases hpi : p i = 0
    · rw [hpi]; simp only [zero_mul, sub_zero]; exact hq0 i
    · have hpos : 0 < p i := lt_of_le_of_ne (hp0 i) (Ne.symm hpi)
      have hne : p i ≠ 0 := ne_of_gt hpos
      have hqpos : 0 < q i := hac i hpos
      have hxpos : 0 < q i / p i := div_pos hqpos hpos
      have hlog : Real.log (q i / p i) ≤ q i / p i - 1 := Real.log_le_sub_one_of_pos hxpos
      have hstep : p i * (q i / p i - 1) = q i - p i := by field_simp
      calc p i * Real.log (q i / p i)
          ≤ p i * (q i / p i - 1) := mul_le_mul_of_nonneg_left hlog (le_of_lt hpos)
        _ = q i - p i := hstep
  calc ∑ i, p i * Real.log (q i / p i)
      ≤ ∑ i, (q i - p i) := Finset.sum_le_sum (fun i _ => hterm i)
    _ = (∑ i, q i) - ∑ i, p i := by rw [Finset.sum_sub_distrib]
    _ ≤ 0 := by rw [hp1]; linarith [hq1]

/-- **KL divergence is nonnegative (proved)**: `0 ≤ ∑ p·log(p/q)`. -/
theorem kl_nonneg {p q : γ → ℝ}
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∑ i, q i ≤ 1)
    (hac : ∀ i, 0 < p i → 0 < q i) :
    0 ≤ ∑ i, p i * Real.log (p i / q i) := by
  have hg := gibbs hp0 hp1 hq0 hq1 hac
  have hflip : ∑ i, p i * Real.log (p i / q i) = - ∑ i, p i * Real.log (q i / p i) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hpi : p i = 0
    · rw [hpi]; simp
    · have hpos : 0 < p i := lt_of_le_of_ne (hp0 i) (Ne.symm hpi)
      have hqpos : 0 < q i := hac i hpos
      rw [Real.log_div (ne_of_gt hpos) (ne_of_gt hqpos),
        Real.log_div (ne_of_gt hqpos) (ne_of_gt hpos)]
      ring
  rw [hflip]; linarith [hg]

end PallLean.Paper93.DeepMath.PathB.InfoTheory

#print axioms PallLean.Paper93.DeepMath.PathB.InfoTheory.gibbs
#print axioms PallLean.Paper93.DeepMath.PathB.InfoTheory.kl_nonneg
