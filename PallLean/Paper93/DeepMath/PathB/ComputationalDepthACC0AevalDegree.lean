import Mathlib

/-!
# The composition-degree lemma — `totalDegree (aeval f p) ≤ totalDegree p · D`

The low-degree substitution (`…ACC0LowDegreeSubstitution`) took the per-gate degree factor as a hypothesis, because
Mathlib has no `totalDegree`-of-composition lemma.  This file **discharges** it: substituting polynomials `f i` of
degree `≤ D` for the variables of `p` produces a polynomial of degree `≤ totalDegree p · D`.

The proof expands `aeval f p = ∑_{d∈p.support} C(coeff_d) · ∏_i (f i)^{d_i}` (`eval₂_eq`); the degree of the image of
one monomial `d` is `≤ ∑_i d_i · deg(f i) ≤ (∑_i d_i)·D = deg(d)·D ≤ totalDegree p · D`
(`totalDegree_finset_prod`, `totalDegree_pow`, `le_totalDegree`), and the sup over `d` keeps the bound
(`totalDegree_finset_sum`).

## What is proved (clean axioms, no `sorry`)

* **`aeval_totalDegree_le`** — `(∀ i, (f i).totalDegree ≤ D) ⇒ (aeval f p).totalDegree ≤ p.totalDegree · D`.
* **`unaGate_degree`** — `(aeval ![A] G).totalDegree ≤ G.totalDegree · A.totalDegree` (unary gate composition).
* **`binGate_degree`** — `(aeval ![A,B] G).totalDegree ≤ G.totalDegree · max A.totalDegree B.totalDegree` (binary
  gate composition) — exactly the per-gate degree factor `…ACC0LowDegreeSubstitution.psubst_degree` assumed, now a
  theorem: a gate polynomial of degree `≤ δ` composed with its children raises degree by at most the factor `δ`.

## Honest scope

This removes the per-gate degree-factor *hypothesis* of the low-degree substitution: composing a degree-`≤ δ` gate
polynomial with children raises total degree by at most `δ`, so a constant-depth circuit of degree-`δ` gate
polynomials has degree `≤ δ^{depth}` unconditionally on that interface.  The abstract `williams`/`hierarchy` Props
remain the named Route-B sockets keeping the final separation conditional.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0AevalDegree

open scoped BigOperators
open MvPolynomial

variable {R : Type*} [CommSemiring R] {σ τ : Type*}

/-- **The composition-degree lemma (proved): substituting degree-`≤ D` polynomials raises total degree by at most the
factor `D`.**  `(aeval f p).totalDegree ≤ p.totalDegree · D`. -/
theorem aeval_totalDegree_le (f : σ → MvPolynomial τ R) (p : MvPolynomial σ R) (D : ℕ)
    (hf : ∀ i, (f i).totalDegree ≤ D) :
    (aeval f p).totalDegree ≤ p.totalDegree * D := by
  rw [aeval_def, eval₂_eq]
  refine le_trans (totalDegree_finset_sum _ _) ?_
  rw [Finset.sup_le_iff]
  intro d hd
  refine le_trans (totalDegree_mul _ _) ?_
  have hC : ((algebraMap R (MvPolynomial τ R)) (coeff d p)).totalDegree = 0 := by
    rw [algebraMap_eq]; exact totalDegree_C _
  rw [hC, zero_add]
  refine le_trans (totalDegree_finset_prod _ _) ?_
  calc ∑ i ∈ d.support, ((f i) ^ (d i)).totalDegree
      ≤ ∑ i ∈ d.support, (d i) * D :=
        Finset.sum_le_sum (fun i _ =>
          le_trans (totalDegree_pow (f i) (d i)) (Nat.mul_le_mul (le_refl (d i)) (hf i)))
    _ = (∑ i ∈ d.support, d i) * D := by rw [← Finset.sum_mul]
    _ ≤ p.totalDegree * D := Nat.mul_le_mul (le_totalDegree hd) (le_refl D)

/-- **Unary gate composition degree (proved): `(aeval ![A] G).totalDegree ≤ G.totalDegree · A.totalDegree`.** -/
theorem unaGate_degree {n : ℕ} (G : MvPolynomial (Fin 1) R) (A : MvPolynomial (Fin n) R) :
    (aeval ![A] G).totalDegree ≤ G.totalDegree * A.totalDegree := by
  apply aeval_totalDegree_le
  intro i
  fin_cases i
  simpa using le_refl A.totalDegree

/-- **Binary gate composition degree (proved): `(aeval ![A,B] G).totalDegree ≤ G.totalDegree · max A.totalDegree
B.totalDegree`.**  This is exactly the per-gate degree factor that `…ACC0LowDegreeSubstitution.psubst_degree` took as
a hypothesis: a gate polynomial of degree `≤ δ` composed with its children raises total degree by at most `δ`. -/
theorem binGate_degree {n : ℕ} (G : MvPolynomial (Fin 2) R) (A B : MvPolynomial (Fin n) R) :
    (aeval ![A, B] G).totalDegree ≤ G.totalDegree * max A.totalDegree B.totalDegree := by
  apply aeval_totalDegree_le
  intro i
  fin_cases i
  · simpa using le_max_left A.totalDegree B.totalDegree
  · simpa using le_max_right A.totalDegree B.totalDegree

end PallLean.Paper93.DeepMath.PathB.ACC0AevalDegree

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0AevalDegree.aeval_totalDegree_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0AevalDegree.unaGate_degree
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0AevalDegree.binGate_degree
