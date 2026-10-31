import PallLean.Paper93.DeepMath.PathB.ComputationalDepthInfoTheory7

/-!
# Information-theory foundations 8: independence and the rectangle structure

The information-theoretic form of the rectangle property of deterministic
protocols: independent inputs carry zero mutual information, and conditioned on the
transcript (a combinatorial rectangle) the inputs stay independent, so
`I(X;Y | Π) = 0`.

* **`prodDist pX pY`** — the product distribution `(a,b) ↦ pX(a)·pY(b)`;
* **`marginalX_prodDist` / `marginalY_prodDist` (proved)** — its marginals are
  `pX`, `pY`;
* **`entropy_prodDist` (proved)** — `H(pX ⊗ pY) = H(pX) + H(pY)` (via
  `negMulLog_mul`);
* **`mutualInfo_prodDist_eq_zero` (proved)** — `I(X;Y) = 0` for independent `X,Y`;
* **`avgMutualInfo_zero_of_prodDist` (proved)** — if the input is a product given
  every transcript value (the rectangle property), then `I(X;Y | Π) = 0`.

Real analysis / finite sums, not `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.InfoTheory

open Real Finset

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The product distribution `(a,b) ↦ pX(a)·pY(b)`. -/
def prodDist (pX : α → ℝ) (pY : β → ℝ) : α × β → ℝ := fun ab => pX ab.1 * pY ab.2

theorem marginalX_prodDist (pX : α → ℝ) {pY : β → ℝ} (hY : ∑ b, pY b = 1) :
    marginalX (prodDist pX pY) = pX := by
  funext a
  show ∑ b, pX a * pY b = pX a
  rw [← Finset.mul_sum, hY, mul_one]

theorem marginalY_prodDist {pX : α → ℝ} (pY : β → ℝ) (hX : ∑ a, pX a = 1) :
    marginalY (prodDist pX pY) = pY := by
  funext b
  show ∑ a, pX a * pY b = pY b
  rw [← Finset.sum_mul, hX, one_mul]

/-- **Entropy of a product is additive (proved)**: `H(pX ⊗ pY) = H(pX) + H(pY)`. -/
theorem entropy_prodDist {pX : α → ℝ} {pY : β → ℝ} (hX : ∑ a, pX a = 1)
    (hY : ∑ b, pY b = 1) : entropy (prodDist pX pY) = entropy pX + entropy pY := by
  have key : entropy (prodDist pX pY)
      = ∑ a, ∑ b, (pY b * Real.negMulLog (pX a) + pX a * Real.negMulLog (pY b)) := by
    rw [entropy, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    show Real.negMulLog (pX a * pY b) = pY b * Real.negMulLog (pX a) + pX a * Real.negMulLog (pY b)
    exact Real.negMulLog_mul (pX a) (pY b)
  have h1 : ∑ a, ∑ b, pY b * Real.negMulLog (pX a) = entropy pX := by
    rw [entropy]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Finset.sum_mul, hY, one_mul]
  have h2 : ∑ a, ∑ b, pX a * Real.negMulLog (pY b) = entropy pY := by
    have hb : ∀ a, ∑ b, pX a * Real.negMulLog (pY b) = pX a * entropy pY := by
      intro a; rw [entropy, ← Finset.mul_sum]
    simp_rw [hb]
    rw [← Finset.sum_mul, hX, one_mul]
  rw [key]
  simp_rw [Finset.sum_add_distrib]
  rw [h1, h2]

/-- **Independent variables have zero mutual information (proved)**: `I(X;Y) = 0`. -/
theorem mutualInfo_prodDist_eq_zero {pX : α → ℝ} {pY : β → ℝ} (hX : ∑ a, pX a = 1)
    (hY : ∑ b, pY b = 1) : mutualInfo (prodDist pX pY) = 0 := by
  rw [mutualInfo, marginalX_prodDist pX hY, marginalY_prodDist pY hX, entropy_prodDist hX hY]
  ring

/-- **The rectangle property (proved)**: if the input is a product given every
transcript value, then `I(X;Y | Π) = 0`. -/
theorem avgMutualInfo_zero_of_prodDist {Z : Type*} [Fintype Z] {lam : Z → ℝ}
    {pX : Z → α → ℝ} {pY : Z → β → ℝ}
    (hX : ∀ z, ∑ a, pX z a = 1) (hY : ∀ z, ∑ b, pY z b = 1) :
    avgMutualInfo lam (fun z => prodDist (pX z) (pY z)) = 0 := by
  rw [avgMutualInfo]
  refine Finset.sum_eq_zero (fun z _ => ?_)
  rw [mutualInfo_prodDist_eq_zero (hX z) (hY z), mul_zero]

end PallLean.Paper93.DeepMath.PathB.InfoTheory

#print axioms PallLean.Paper93.DeepMath.PathB.InfoTheory.mutualInfo_prodDist_eq_zero
#print axioms PallLean.Paper93.DeepMath.PathB.InfoTheory.avgMutualInfo_zero_of_prodDist
