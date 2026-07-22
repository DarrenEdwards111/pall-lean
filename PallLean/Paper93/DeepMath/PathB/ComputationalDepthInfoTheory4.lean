import PallLean.Paper93.DeepMath.PathB.ComputationalDepthInfoTheory3

/-!
# Information-theory foundations 4: subadditivity and mutual information

Applying Gibbs (InfoTheory3) to the product of marginals gives `I(X;Y) ≥ 0` and
subadditivity `H(X,Y) ≤ H(X) + H(Y)`.

* **`entropy_eq` / `entropy_marginalX_eq` / `entropy_marginalY_eq` (proved)** — the
  entropy expansions `-∑ p·log(·)` over the joint support;
* **`subadditivity` (proved)** — `H(X,Y) ≤ H(X) + H(Y)`;
* **`mutualInfo`** and **`mutualInfo_nonneg` (proved)** — `I(X;Y) := H(X)+H(Y)−H(X,Y)
  ≥ 0` (KL between the joint and the product of marginals).

Real analysis / finite sums, not `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.InfoTheory

open Real Finset

variable {α β : Type*} [Fintype α] [Fintype β]

theorem entropy_eq (p : α × β → ℝ) :
    entropy p = - ∑ ab : α × β, p ab * Real.log (p ab) := by
  rw [entropy, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun ab _ => by rw [Real.negMulLog]; ring)

theorem entropy_marginalX_eq (p : α × β → ℝ) :
    entropy (marginalX p) = - ∑ ab : α × β, p ab * Real.log (marginalX p ab.1) := by
  have helper : ∑ a : α, marginalX p a * Real.log (marginalX p a)
      = ∑ ab : α × β, p ab * Real.log (marginalX p ab.1) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    show marginalX p a * Real.log (marginalX p a) = ∑ b : β, p (a, b) * Real.log (marginalX p a)
    exact Finset.sum_mul Finset.univ (fun b => p (a, b)) (Real.log (marginalX p a))
  rw [entropy, ← helper, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun a _ => by rw [Real.negMulLog]; ring)

theorem entropy_marginalY_eq (p : α × β → ℝ) :
    entropy (marginalY p) = - ∑ ab : α × β, p ab * Real.log (marginalY p ab.2) := by
  have helper : ∑ b : β, marginalY p b * Real.log (marginalY p b)
      = ∑ ab : α × β, p ab * Real.log (marginalY p ab.2) := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    show marginalY p b * Real.log (marginalY p b) = ∑ a : α, p (a, b) * Real.log (marginalY p b)
    exact Finset.sum_mul Finset.univ (fun a => p (a, b)) (Real.log (marginalY p b))
  rw [entropy, ← helper, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun b _ => by rw [Real.negMulLog]; ring)

theorem marginalX_sum {p : α × β → ℝ} (hp : IsProbDist p) : ∑ a, marginalX p a = 1 := by
  calc ∑ a, marginalX p a
      = ∑ a, ∑ b, p (a, b) := rfl
    _ = ∑ ab : α × β, p ab := (Fintype.sum_prod_type p).symm
    _ = 1 := hp.2

/-- **Subadditivity of entropy (proved)**: `H(X,Y) ≤ H(X) + H(Y)`. -/
theorem subadditivity {p : α × β → ℝ} (hp : IsProbDist p) :
    entropy p ≤ entropy (marginalX p) + entropy (marginalY p) := by
  have hq0 : ∀ ab : α × β, 0 ≤ marginalX p ab.1 * marginalY p ab.2 := fun ab =>
    mul_nonneg (Finset.sum_nonneg (fun b _ => hp.1 (ab.1, b)))
      (Finset.sum_nonneg (fun a _ => hp.1 (a, ab.2)))
  have hprod : ∑ ab : α × β, marginalX p ab.1 * marginalY p ab.2
      = (∑ a, marginalX p a) * (∑ b, marginalY p b) := by
    rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
  have hqsum : ∑ ab : α × β, marginalX p ab.1 * marginalY p ab.2 = 1 := by
    rw [hprod, marginalX_sum hp, (marginalY_isProbDist hp).2, mul_one]
  have hac : ∀ ab : α × β, 0 < p ab → 0 < marginalX p ab.1 * marginalY p ab.2 := by
    rintro ⟨a, b⟩ hpab
    have hmX : 0 < marginalX p a :=
      lt_of_lt_of_le hpab (Finset.single_le_sum (fun b' _ => hp.1 (a, b')) (Finset.mem_univ b))
    have hmY : 0 < marginalY p b :=
      lt_of_lt_of_le hpab (Finset.single_le_sum (fun a' _ => hp.1 (a', b)) (Finset.mem_univ a))
    exact mul_pos hmX hmY
  have hident : ∑ ab : α × β, p ab * Real.log (marginalX p ab.1 * marginalY p ab.2 / p ab)
      = entropy p - entropy (marginalX p) - entropy (marginalY p) := by
    rw [entropy_eq p, entropy_marginalX_eq p, entropy_marginalY_eq p, sub_neg_eq_add,
      sub_neg_eq_add, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun ab _ => ?_)
    by_cases hpab : p ab = 0
    · rw [hpab]; simp
    · obtain ⟨a, b⟩ := ab
      have hpos : 0 < p (a, b) := lt_of_le_of_ne (hp.1 _) (Ne.symm hpab)
      have hmX : 0 < marginalX p a :=
        lt_of_lt_of_le hpos (Finset.single_le_sum (fun b' _ => hp.1 (a, b')) (Finset.mem_univ b))
      have hmY : 0 < marginalY p b :=
        lt_of_lt_of_le hpos (Finset.single_le_sum (fun a' _ => hp.1 (a', b)) (Finset.mem_univ a))
      rw [Real.log_div (ne_of_gt (mul_pos hmX hmY)) (ne_of_gt hpos),
        Real.log_mul (ne_of_gt hmX) (ne_of_gt hmY)]
      ring
  have hg := gibbs hp.1 hp.2 hq0 (le_of_eq hqsum) hac
  rw [hident] at hg
  linarith [hg]

/-- Mutual information `I(X;Y) = H(X) + H(Y) − H(X,Y)`. -/
noncomputable def mutualInfo (p : α × β → ℝ) : ℝ :=
  entropy (marginalX p) + entropy (marginalY p) - entropy p

/-- **Mutual information is nonnegative (proved)**: `I(X;Y) ≥ 0`. -/
theorem mutualInfo_nonneg {p : α × β → ℝ} (hp : IsProbDist p) : 0 ≤ mutualInfo p := by
  have := subadditivity hp
  rw [mutualInfo]; linarith

end PallLean.Paper93.DeepMath.PathB.InfoTheory

#print axioms PallLean.Paper93.DeepMath.PathB.InfoTheory.subadditivity
#print axioms PallLean.Paper93.DeepMath.PathB.InfoTheory.mutualInfo_nonneg
