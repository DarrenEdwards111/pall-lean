import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBoosting
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDimension
import Mathlib

/-!
# Assembling the boosting step into the dimension count (PROVED)

`ComputationalDepthBoosting` proved the folding identity (a high-degree monomial `∏_{i∈S} xᵢ` equals the full
product times a low-degree complementary monomial).  This file assembles it: it shows **every** monomial reduces
to a degree-`≤ n/2` monomial scaled by a factor in `{1, full product}`, and counts the reduced index set.

  `monomial_dichotomy` — every monomial `∏_{i∈S} xᵢ` on the `{-1,+1}` cube equals `c · ∏_{i∈T} xᵢ` with
        `2|T| ≤ n` (degree `≤ n/2`) and `c ∈ {1, ∏ᵢ xᵢ}`.  (`|S| ≤ n/2` ⇒ keep `S`; else fold to `Sᶜ`.)
  `card_low_monomials` — the reduced index set `{T : 2|T| ≤ n}` has size `Σ_{i ≤ n/2} C(n,i)` (the dimension
        count of `ComputationalDepthDimension`, at `m = n/2`).

So, replacing the full product by a degree-`d` approximator, every function on `G` (a sum of monomials) lies in
the span of `{∏_T, a·∏_T : 2|T| ≤ n}` — a set of `2·Σ_{i≤n/2} C(n,i)` functions — whence
`|G| ≤ 2·Σ_{i≤n/2} C(n,i)` by `card_le_of_surjective`.  The remaining step is the multilinear span / surjectivity
(every function on the cube is a sum of monomials) and plugging in the OR/`MOD` approximator.
-/

open PallLean.Paper93.DeepMath.PathB

namespace PallLean.Paper93.DeepMath.PathB.Boosting

variable {R : Type*} [CommMonoid R] {n : ℕ}

/-- **Monomial reduction (assembled folding).**  Every monomial reduces, on the `{-1,+1}` cube, to a
degree-`≤ n/2` monomial times a factor that is either `1` or the full product: `∏_{i∈S} xᵢ = c · ∏_{i∈T} xᵢ`
with `2|T| ≤ n` and `c ∈ {1, ∏ᵢ xᵢ}`.  (Keep `S` if it is already low degree; otherwise fold to `Sᶜ`.) -/
theorem monomial_dichotomy (x : Fin n → R) (hx : ∀ i, x i ^ 2 = 1) (S : Finset (Fin n)) :
    ∃ T : Finset (Fin n), 2 * T.card ≤ n ∧
      (∏ i ∈ S, x i = ∏ i ∈ T, x i ∨ ∏ i ∈ S, x i = (∏ i, x i) * ∏ i ∈ T, x i) := by
  by_cases h : 2 * S.card ≤ n
  · exact ⟨S, h, Or.inl rfl⟩
  · refine ⟨Sᶜ, ?_, Or.inr (prod_eq_full_mul_prod_compl x hx S)⟩
    rw [Finset.card_compl, Fintype.card_fin]
    omega

/-- **The reduced index set has the dimension count.**  The low-degree monomials `{T : 2|T| ≤ n}` (degree
`≤ n/2`) number exactly `Σ_{i ≤ n/2} C(n,i)` — the dimension count of `ComputationalDepthDimension` at `m = n/2`.
With the `{1, full product}` factor, the boosting spanning set has size `≤ 2·Σ_{i≤n/2} C(n,i)`. -/
theorem card_low_monomials :
    (Finset.univ.filter (fun T : Finset (Fin n) => 2 * T.card ≤ n)).card
      = ∑ i ∈ Finset.range (n / 2 + 1), n.choose i := by
  rw [← Dimension.card_subsets_card_le n (n / 2)]
  congr 1
  apply Finset.filter_congr
  intro T _
  constructor <;> intro h <;> omega

end PallLean.Paper93.DeepMath.PathB.Boosting

#print axioms PallLean.Paper93.DeepMath.PathB.Boosting.monomial_dichotomy
#print axioms PallLean.Paper93.DeepMath.PathB.Boosting.card_low_monomials
