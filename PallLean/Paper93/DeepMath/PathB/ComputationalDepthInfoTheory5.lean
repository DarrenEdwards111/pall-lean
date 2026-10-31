import PallLean.Paper93.DeepMath.PathB.ComputationalDepthInfoTheory4

/-!
# Information-theory foundations 5: conditional information quantities

The conditioned quantities `H(X | Z)` and `I(X;Y | Z)`, built by averaging over `Z`
(with weights `λ z = pZ(z)` and `p z` the conditional distribution given `Z = z`).
Averaging transfers the non-negativity results of InfoTheory1–4 directly.

* **`avgEntropy λ p := ∑ z, λ z · H(p z)`** — conditional entropy `H(X|Z)`;
* **`avgMutualInfo λ p := ∑ z, λ z · I(p z)`** — conditional mutual information
  `I(X;Y|Z)`;
* **`avgEntropy_nonneg` / `avgMutualInfo_nonneg` (proved)** — `H(X|Z) ≥ 0`,
  `I(X;Y|Z) ≥ 0` (conditioning never makes information negative);
* **`avgEntropy_le_log_card` (proved)** — `H(X|Z) ≤ (∑ λ)·log|α|`.

These are the building blocks of the information cost of a protocol.  Real
analysis / finite sums, not `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.InfoTheory

open Real Finset

variable {Z α β : Type*} [Fintype Z] [Fintype α] [Fintype β]

/-- Conditional entropy `H(X | Z)` as an average over `Z`. -/
noncomputable def avgEntropy (lam : Z → ℝ) (p : Z → α → ℝ) : ℝ :=
  ∑ z, lam z * entropy (p z)

/-- Conditional mutual information `I(X;Y | Z)` as an average over `Z`. -/
noncomputable def avgMutualInfo (lam : Z → ℝ) (p : Z → α × β → ℝ) : ℝ :=
  ∑ z, lam z * mutualInfo (p z)

/-- **Conditional entropy is nonnegative (proved)**: `H(X|Z) ≥ 0`. -/
theorem avgEntropy_nonneg {lam : Z → ℝ} {p : Z → α → ℝ}
    (hlam : ∀ z, 0 ≤ lam z) (hp : ∀ z, IsProbDist (p z)) :
    0 ≤ avgEntropy lam p :=
  Finset.sum_nonneg (fun z _ => mul_nonneg (hlam z) (entropy_nonneg (hp z)))

/-- **Conditional mutual information is nonnegative (proved)**: `I(X;Y|Z) ≥ 0`. -/
theorem avgMutualInfo_nonneg {lam : Z → ℝ} {p : Z → α × β → ℝ}
    (hlam : ∀ z, 0 ≤ lam z) (hp : ∀ z, IsProbDist (p z)) :
    0 ≤ avgMutualInfo lam p :=
  Finset.sum_nonneg (fun z _ => mul_nonneg (hlam z) (mutualInfo_nonneg (hp z)))

/-- **Conditional entropy is bounded by `log |α|` (proved)**: `H(X|Z) ≤ (∑ λ)·log|α|`. -/
theorem avgEntropy_le_log_card [Nonempty α] {lam : Z → ℝ} {p : Z → α → ℝ}
    (hlam : ∀ z, 0 ≤ lam z) (hp : ∀ z, IsProbDist (p z)) :
    avgEntropy lam p ≤ (∑ z, lam z) * Real.log (Fintype.card α) := by
  rw [avgEntropy, Finset.sum_mul]
  refine Finset.sum_le_sum (fun z _ => ?_)
  exact mul_le_mul_of_nonneg_left (entropy_le_log_card (hp z)) (hlam z)

end PallLean.Paper93.DeepMath.PathB.InfoTheory

#print axioms PallLean.Paper93.DeepMath.PathB.InfoTheory.avgMutualInfo_nonneg
#print axioms PallLean.Paper93.DeepMath.PathB.InfoTheory.avgEntropy_le_log_card
