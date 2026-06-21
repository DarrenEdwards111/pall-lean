import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0MonomialCount

/-!
# Brick C — degree composes multiplicatively under substitution (proved)

The genuine core of the Yao–Beigel–Tarui depth reduction.  The tree previously showed that composing low-degree
representations over the **gate count** blows up doubly-exponentially (`ACC0Composition.composed_budget_ge_double_exp`) —
that is the *wrong* parameter.  The right parameter is the **polynomial degree**, which composes *multiplicatively*: if the
outer polynomial has total degree `≤ D₁` and each substituted polynomial has total degree `≤ D₂`, the composition has total
degree `≤ D₁ · D₂`.

Iterating over a *constant* depth `d`, the degree stays `≤ D^d` (polylog for polylog `D`); Brick D
(`degLeMonomials_card_le`) then bounds the monomials by `(n+1)^{D^d}` = quasipolynomial.  This is exactly the degree control
the YBT normal form needs — and it is the parameter the naive blow-up missed.

## What is proved (clean axioms, no `sorry`)

* **`totalDegree_bind₁_le`** (PROVED) — `(∀ i, (g i).totalDegree ≤ d) → (bind₁ g P).totalDegree ≤ P.totalDegree * d`: the
  substitution degree bound (one composition layer).
* **`totalDegree_bind₁_comp_le`** (PROVED) — two layers: `(bind₁ g (bind₁ h P)).totalDegree ≤ P.totalDegree * dₕ * d_g`
  — degree multiplies across depth.

## Honest scope

This is the **degree-composition law** (the correct degree control over constant depth), a single-ring statement.  It does
**not** by itself assemble general YBT: composing *different-prime* `MOD` gates needs the product observer (Brick A.1, the
single field is proven dead), the prime-power (`e≥2`) Toda lifting remains, and wiring degree-`D^d` + Brick D + the `SYM∘AND`
form into `composite_BT_degree` over an `ACC0Circuit` is the remaining assembly.  General YBT / `composite_BT_degree` remains
open.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0DegreeCompose

open MvPolynomial

variable {σ τ υ R : Type*} [CommSemiring R]

/-- **Substitution degree bound (PROVED): degree composes multiplicatively (one layer).** -/
theorem totalDegree_bind₁_le (g : σ → MvPolynomial τ R) (P : MvPolynomial σ R) (d : ℕ)
    (hg : ∀ i, (g i).totalDegree ≤ d) :
    (bind₁ g P).totalDegree ≤ P.totalDegree * d := by
  have hexp : bind₁ g P = ∑ e ∈ P.support, C (coeff e P) * ∏ i ∈ e.support, (g i) ^ (e i) := by
    rw [bind₁, aeval_def, eval₂_eq]; simp only [MvPolynomial.algebraMap_eq]
  rw [hexp]
  refine totalDegree_finsetSum_le (fun e he => ?_)
  refine le_trans (totalDegree_mul _ _) ?_
  rw [totalDegree_C, zero_add]
  refine le_trans (totalDegree_finset_prod _ _) ?_
  calc ∑ i ∈ e.support, (g i ^ e i).totalDegree
      ≤ ∑ i ∈ e.support, e i * d := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        calc (g i ^ e i).totalDegree ≤ e i * (g i).totalDegree := totalDegree_pow _ _
          _ ≤ e i * d := by gcongr; exact hg i
    _ = (∑ i ∈ e.support, e i) * d := by rw [Finset.sum_mul]
    _ ≤ P.totalDegree * d := by gcongr; exact le_totalDegree he

/-- **Two-layer composition (PROVED): degree multiplies across depth.** -/
theorem totalDegree_bind₁_comp_le (g : τ → MvPolynomial υ R) (h : σ → MvPolynomial τ R)
    (P : MvPolynomial σ R) (dg dh : ℕ) (hg : ∀ i, (g i).totalDegree ≤ dg) (hh : ∀ i, (h i).totalDegree ≤ dh) :
    (bind₁ g (bind₁ h P)).totalDegree ≤ P.totalDegree * dh * dg := by
  exact le_trans (totalDegree_bind₁_le g (bind₁ h P) dg hg)
    (Nat.mul_le_mul_right _ (totalDegree_bind₁_le h P dh hh))

/-!
**The degree-composition law, proved.**  Degree composes multiplicatively, so a constant-depth `d` composition stays at
degree `≤ D^d` (polylog), and Brick D bounds the monomials by `(n+1)^{D^d}` (quasipoly) — the correct degree control the
naive gate-count blow-up missed.  Next: the product-observer cross-prime composition, the prime-power lifting, and wiring
into `composite_BT_degree`.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0DegreeCompose

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DegreeCompose.totalDegree_bind₁_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DegreeCompose.totalDegree_bind₁_comp_le
