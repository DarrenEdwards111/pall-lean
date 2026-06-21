import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0MonomialCount
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0DepthDegree

/-!
# Bridge — degree `⇒` quasipolynomial `AND`-term count (proved)

The multilinearization bridge connecting Brick C (degree) to Brick D (`AND`-term count).  On Boolean inputs each monomial
`∏ Xᵢ^{eᵢ}` collapses to the `AND` of its *variable set* `e.support` (since `xᵢ^k = xᵢ`).  The variable set of a monomial of
degree `≤ D` has size `≤ D`, so it is one of the degree-`≤ D` `AND`-terms (`degLeMonomials`, Brick D) — and there are at most
`(n+1)^D` of those.  Hence a degree-`≤ D` polynomial uses at most `(n+1)^D` distinct `AND`-terms.

Combined with Brick C-iterate, a depth-`d` composition (degree `≤ D^d`) uses at most `(n+1)^{deg · D^d}` `AND`-terms —
quasipolynomial for constant `d` — the size guarantee of its `SYM∘AND` form.

## What is proved (clean axioms, no `sorry`)

* **`support_card_le_totalDegree`** (PROVED) — a monomial of `P`'s support has variable-set size `≤ P.totalDegree`.
* **`andTerms_card_le`** (PROVED) — `P.totalDegree ≤ D → (P.support.image (·.support)).card ≤ (n+1)^D`.
* **`composed_andTerms_card_le`** (PROVED) — a depth-`d` composition uses `≤ (n+1)^{P.totalDegree · D^d}` `AND`-terms.

## Honest scope

This is the **degree → `AND`-term count** bridge (the multilinear size side).  It does **not** build the `AND`/`OR`
approximate polynomials, cross-prime nesting, prime-power composition, nor the `ACC0Circuit`-level `composite_BT_degree`.
General YBT remains open.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0Multilinearize

open Finset MvPolynomial
open PallLean.Paper93.DeepMath.PathB.ACC0MonomialCount (degLeMonomials degLeMonomials_card_le)
open PallLean.Paper93.DeepMath.PathB.ACC0DepthDegree (totalDegree_bind₁_iterate)

variable {n : ℕ} {R : Type*} [CommSemiring R]

/-- **A monomial's variable-set size is at most the total degree (PROVED).** -/
theorem support_card_le_totalDegree (P : MvPolynomial (Fin n) R) (e : Fin n →₀ ℕ) (he : e ∈ P.support) :
    e.support.card ≤ P.totalDegree := by
  refine le_trans ?_ (le_totalDegree he)
  have h1 : e.sum (fun _ x => x) = ∑ i ∈ e.support, e i := rfl
  rw [h1, Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum (fun i hi => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))

/-- **A degree-`≤ D` polynomial uses at most `(n+1)^D` distinct `AND`-terms (PROVED).** -/
theorem andTerms_card_le (P : MvPolynomial (Fin n) R) (D : ℕ) (hP : P.totalDegree ≤ D) :
    (P.support.image (fun e => e.support)).card ≤ (n + 1) ^ D := by
  refine le_trans (Finset.card_le_card ?_) (degLeMonomials_card_le n D)
  intro S hS
  rw [Finset.mem_image] at hS
  obtain ⟨e, he, rfl⟩ := hS
  rw [degLeMonomials, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨Finset.subset_univ _, le_trans (support_card_le_totalDegree P e he) hP⟩

/-- **A depth-`d` composition uses at most `(n+1)^{deg · D^d}` `AND`-terms (PROVED).** -/
theorem composed_andTerms_card_le (g : Fin n → MvPolynomial (Fin n) R) (D : ℕ)
    (hg : ∀ i, (g i).totalDegree ≤ D) (P : MvPolynomial (Fin n) R) (d : ℕ) :
    (((bind₁ g)^[d] P).support.image (fun e => e.support)).card ≤ (n + 1) ^ (P.totalDegree * D ^ d) :=
  andTerms_card_le _ _ (totalDegree_bind₁_iterate g D hg P d)

/-!
**The degree → `AND`-term bridge, proved.**  Degree (Brick C) controls the `AND`-term count (Brick D): a depth-`d`
composition uses `≤ (n+1)^{deg·D^d}` distinct `AND`-terms, quasipolynomial for constant `d` — the `SYM∘AND` size guarantee.
Remaining for general YBT: `AND`/`OR` approximate polynomials, cross-prime, prime-power composition, circuit assembly.  Not a
separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0Multilinearize

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Multilinearize.andTerms_card_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Multilinearize.composed_andTerms_card_le
