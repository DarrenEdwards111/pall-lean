import PallLean.Paper93.DeepMath.PathB.ComputationalDepthInfoTheory1

/-!
# Information-theory foundations 2: conditional entropy and the chain rule

Joint distributions on `α × β`, marginals, conditional entropy, and the chain
rule `H(X,Y) = H(Y) + H(X|Y)`.

* **`marginalX` / `marginalY`** — the marginals of a joint distribution;
  **`marginalY_isProbDist` (proved)** — a marginal is a distribution;
* **`condEntropy p := ∑ p(a,b)·(log pY(b) − log p(a,b))`** — conditional entropy
  `H(X|Y)` (Mathlib's `log 0 = 0` makes the `p = 0` terms vanish);
* **`chain_rule` (proved)** — `entropy p = entropy (marginalY p) + condEntropy p`;
* **`condEntropy_nonneg` (proved)** — `H(X|Y) ≥ 0` (each term `≥ 0` since
  `p(a,b) ≤ pY(b)` and `log` is monotone);
* **`entropy_ge_marginal` (proved)** — `H(X,Y) ≥ H(Y)`: entropy grows with more
  variables.

Real analysis / finite sums, not `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.InfoTheory

open Real Finset

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The `α`-marginal of a joint distribution. -/
def marginalX (p : α × β → ℝ) : α → ℝ := fun a => ∑ b, p (a, b)

/-- The `β`-marginal of a joint distribution. -/
def marginalY (p : α × β → ℝ) : β → ℝ := fun b => ∑ a, p (a, b)

theorem marginalY_isProbDist {p : α × β → ℝ} (hp : IsProbDist p) :
    IsProbDist (marginalY p) := by
  refine ⟨fun b => Finset.sum_nonneg (fun a _ => hp.1 (a, b)), ?_⟩
  calc ∑ b, marginalY p b
      = ∑ b, ∑ a, p (a, b) := rfl
    _ = ∑ a, ∑ b, p (a, b) := Finset.sum_comm
    _ = ∑ ab : α × β, p ab := (Fintype.sum_prod_type p).symm
    _ = 1 := hp.2

/-- Conditional entropy `H(X | Y) = ∑ p(a,b)·(log pY(b) − log p(a,b))`. -/
noncomputable def condEntropy (p : α × β → ℝ) : ℝ :=
  ∑ ab : α × β, p ab * (Real.log (marginalY p ab.2) - Real.log (p ab))

/-- **The chain rule (proved)**: `H(X,Y) = H(Y) + H(X|Y)`. -/
theorem chain_rule (p : α × β → ℝ) :
    entropy p = entropy (marginalY p) + condEntropy p := by
  have helper : ∑ b : β, marginalY p b * Real.log (marginalY p b)
      = ∑ ab : α × β, p ab * Real.log (marginalY p ab.2) := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    show marginalY p b * Real.log (marginalY p b) = ∑ a : α, p (a, b) * Real.log (marginalY p b)
    exact Finset.sum_mul Finset.univ (fun a => p (a, b)) (Real.log (marginalY p b))
  have hey : entropy (marginalY p) = - ∑ ab : α × β, p ab * Real.log (marginalY p ab.2) := by
    rw [entropy, ← helper, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun b _ => by rw [Real.negMulLog]; ring)
  have hep : entropy p = - ∑ ab : α × β, p ab * Real.log (p ab) := by
    rw [entropy, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun ab _ => by rw [Real.negMulLog]; ring)
  have hcond : condEntropy p = (∑ ab : α × β, p ab * Real.log (marginalY p ab.2))
      - ∑ ab : α × β, p ab * Real.log (p ab) := by
    rw [condEntropy, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun ab _ => by rw [mul_sub])
  rw [hey, hcond, hep]; ring

/-- **Conditional entropy is nonnegative (proved)**: `H(X|Y) ≥ 0`. -/
theorem condEntropy_nonneg {p : α × β → ℝ} (hp : ∀ ab, 0 ≤ p ab) :
    0 ≤ condEntropy p := by
  rw [condEntropy]
  apply Finset.sum_nonneg
  rintro ⟨a, b⟩ _
  by_cases hpab : p (a, b) = 0
  · rw [hpab]; simp
  · have hpos : 0 < p (a, b) := lt_of_le_of_ne (hp (a, b)) (Ne.symm hpab)
    have hle : p (a, b) ≤ marginalY p b :=
      Finset.single_le_sum (fun a' _ => hp (a', b)) (Finset.mem_univ a)
    have hlog : Real.log (p (a, b)) ≤ Real.log (marginalY p b) := Real.log_le_log hpos hle
    exact mul_nonneg (hp (a, b)) (by linarith)

/-- **Entropy grows with more variables (proved)**: `H(X,Y) ≥ H(Y)`. -/
theorem entropy_ge_marginal {p : α × β → ℝ} (hp : ∀ ab, 0 ≤ p ab) :
    entropy (marginalY p) ≤ entropy p := by
  rw [chain_rule p]
  have := condEntropy_nonneg hp
  linarith

end PallLean.Paper93.DeepMath.PathB.InfoTheory

#print axioms PallLean.Paper93.DeepMath.PathB.InfoTheory.chain_rule
#print axioms PallLean.Paper93.DeepMath.PathB.InfoTheory.condEntropy_nonneg
