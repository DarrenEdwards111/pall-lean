import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDimension
import Mathlib

/-!
# The binomial tail bound for the dimension argument (PROVED)

The dimension argument needs the **degree-`≤m` dimension to be strictly smaller than the full function space**:
`Σ_{i≤m} C(n,i) < 2ⁿ` for `m < n`.  This is the quantitative fact that turns the dimension bound
`|G| ≤ Σ_{i≤m} C(n,i)` into a contradiction with `|G|` large.

  `sum_choose_lt` — `Σ_{i≤m} C(n,i) < 2ⁿ` whenever `m < n` (the omitted top tail, containing `C(n,n)=1`, is
        positive).
  `dim_lt_full` — composed with the dimension count: the number of degree-`≤m` multilinear monomials is
        `< 2ⁿ = ` the number of functions on the cube.  So degree-`≤m` polynomials cannot realise *every*
        function — the engine of the lower bound.

The sharper *concentration* bound `Σ_{i ≤ n/2 + O(√n)} C(n,i) ≤ (1-δ)2ⁿ` (the `√n` threshold that yields the
exponential `AC⁰[p]` size lower bound for `MOD_q`) remains the quantitative target; this proves the qualitative
strict bound it refines.
-/

namespace PallLean.Paper93.DeepMath.PathB.Dimension

/-- **The binomial tail bound.**  For `m < n`, the partial sum `Σ_{i≤m} C(n,i)` is strictly less than the full
sum `2ⁿ`: the omitted top tail `{m+1,…,n}` contains `C(n,n) = 1 > 0`. -/
theorem sum_choose_lt {n m : ℕ} (hm : m < n) :
    ∑ i ∈ Finset.range (m + 1), n.choose i < 2 ^ n := by
  have hsub : Finset.range (m + 1) ⊆ Finset.range (n + 1) := by
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  calc ∑ i ∈ Finset.range (m + 1), n.choose i
      < ∑ i ∈ Finset.range (n + 1), n.choose i := by
        refine Finset.sum_lt_sum_of_subset hsub (i := n)
          (Finset.mem_range.mpr (by omega)) (by rw [Finset.mem_range]; omega)
          (Nat.choose_pos (le_refl n)) (fun j _ _ => Nat.zero_le _)
    _ = 2 ^ n := Nat.sum_range_choose n

/-- **Degree-`≤m` dimension `<` full function space.**  Composing the tail bound with the dimension count: for
`m < n`, the number of multilinear monomials of degree `≤ m` is strictly less than `2ⁿ`, the number of functions
on `{0,1}ⁿ`.  So no `2ⁿ`-element set of functions can all be degree-`≤m` — the quantitative contradiction the
dimension argument drives. -/
theorem dim_lt_full {n m : ℕ} (hm : m < n) :
    (Finset.univ.filter (fun S : Finset (Fin n) => S.card ≤ m)).card < 2 ^ n := by
  rw [card_subsets_card_le]
  exact sum_choose_lt hm

end PallLean.Paper93.DeepMath.PathB.Dimension

#print axioms PallLean.Paper93.DeepMath.PathB.Dimension.sum_choose_lt
#print axioms PallLean.Paper93.DeepMath.PathB.Dimension.dim_lt_full
