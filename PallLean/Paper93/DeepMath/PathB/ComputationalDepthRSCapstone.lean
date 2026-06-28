import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTailBound
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMultilinear
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBoostingAssembly
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthOrApprox
import Mathlib

/-!
# Razborov–Smolensky: final assembly of the dimension argument (PROVED skeleton)

This file composes the proved cores into the dimension argument's conclusion.  The five machine-checked
ingredients, each unconditional and `sorry`-free:

* **OR approximation** (`OrApprox.orApproxT_disagree_count`) — `OR` has a degree-`t(p-1)` probabilistic
  `𝔽_p`-polynomial with error `≤ 2⁻ᵗ`.
* **Multilinear span** (`Multilinear.eval_surjective`) — every function on `{0,1}ⁿ` is a multilinear polynomial.
* **Boosting / folding** (`Boosting.monomial_dichotomy`) — every monomial reduces to a degree-`≤ n/2` monomial
  times `{1, full product}`; replacing the full product by a degree-`d` approximator gives degree `≤ n/2 + d`.
* **Dimension count + surjection** (`Dimension.card_subsets_card_le`, `Dimension.card_le_of_surjective`).
* **Tail bound** (`Dimension.sum_choose_lt`) — `Σ_{i≤m} C(n,i) < 2ⁿ` for `m < n`.

`dimension_argument` assembles four of them: **given** the boosting surjection — that every function on `G` is
realised by a degree-`≤m` polynomial (`m < n`), the content the OR approximation + multilinear span + folding
produce — the counting forces `|G| < 2ⁿ`.  `low_degree_insufficient` is the clean corollary: degree-`<n`
polynomials cannot realise *every* function on the cube.  Combined with "`MOD_q ∈ AC⁰[p]` ⇒ `MOD_q` is
low-degree-realisable on a large `G`" (the circuit-approximation direction, the remaining input), this is
`MOD_q ∉ AC⁰[p]`.
-/

open PallLean.Paper93.DeepMath.PathB

namespace PallLean.Paper93.DeepMath.PathB.RazborovSmolensky

/-- **The dimension argument (assembled).**  Let `G` be a finite set of points and `m < n`.  If the coefficient
space of degree-`≤m` multilinear polynomials surjects onto the functions `G → 𝔽` (the boosting hypothesis: every
function on `G` is realised at degree `≤ m`), then `|G| < 2ⁿ`.  Proof: `card_le_of_surjective` bounds `|G|` by the
number of degree-`≤m` monomials `= Σ_{i≤m} C(n,i)` (`card_subsets_card_le`), which is `< 2ⁿ` (`sum_choose_lt`). -/
theorem dimension_argument {n m : ℕ} (hm : m < n)
    {F : Type*} [Fintype F] [DecidableEq F] (hF : 1 < Fintype.card F)
    {G : Type*} [Fintype G] [DecidableEq G]
    (φ : ({S : Finset (Fin n) // S.card ≤ m} → F) → (G → F))
    (hφ : Function.Surjective φ) :
    Fintype.card G < 2 ^ n := by
  have h1 : Fintype.card G ≤ Fintype.card {S : Finset (Fin n) // S.card ≤ m} :=
    Dimension.card_le_of_surjective hF φ hφ
  rw [Fintype.card_subtype, Dimension.card_subsets_card_le] at h1
  exact lt_of_le_of_lt h1 (Dimension.sum_choose_lt hm)

/-- **The sharp dimension bound.**  Same hypotheses as `dimension_argument`, but keeping the exact count: a
surjection from the degree-`≤m` coefficient space onto `G → 𝔽` forces `|G| ≤ Σ_{i≤m} C(n,i)` (the dimension of
that space), the bound `dimension_argument` discards in favour of `< 2ⁿ`.  No `m < n` is needed here. -/
theorem dimension_argument_sharp {n m : ℕ}
    {F : Type*} [Fintype F] [DecidableEq F] (hF : 1 < Fintype.card F)
    {G : Type*} [Fintype G] [DecidableEq G]
    (φ : ({S : Finset (Fin n) // S.card ≤ m} → F) → (G → F))
    (hφ : Function.Surjective φ) :
    Fintype.card G ≤ ∑ i ∈ Finset.range (m + 1), n.choose i := by
  have h1 : Fintype.card G ≤ Fintype.card {S : Finset (Fin n) // S.card ≤ m} :=
    Dimension.card_le_of_surjective hF φ hφ
  rwa [Fintype.card_subtype, Dimension.card_subsets_card_le] at h1

/-- **Low degree is insufficient (abstract lower bound).**  For `m < n`, the degree-`≤m` multilinear polynomials
do *not* surject onto all functions on the cube `{0,1}ⁿ`: there are `2ⁿ` functions but only `Σ_{i≤m} C(n,i) < 2ⁿ`
degrees of freedom.  This is the dimension argument's conclusion — the abstract shape of `MOD_q ∉ AC⁰[p]`. -/
theorem low_degree_insufficient {n m : ℕ} (hm : m < n)
    {F : Type*} [Fintype F] [DecidableEq F] (hF : 1 < Fintype.card F)
    (φ : ({S : Finset (Fin n) // S.card ≤ m} → F) → ((Fin n → Bool) → F)) :
    ¬ Function.Surjective φ := by
  intro hφ
  have hlt := dimension_argument hm hF φ hφ
  have hcard : Fintype.card (Fin n → Bool) = 2 ^ n := by
    simp [Fintype.card_bool, Fintype.card_fin]
  rw [hcard] at hlt
  exact lt_irrefl _ hlt

end PallLean.Paper93.DeepMath.PathB.RazborovSmolensky

#print axioms PallLean.Paper93.DeepMath.PathB.RazborovSmolensky.dimension_argument
#print axioms PallLean.Paper93.DeepMath.PathB.RazborovSmolensky.low_degree_insufficient
