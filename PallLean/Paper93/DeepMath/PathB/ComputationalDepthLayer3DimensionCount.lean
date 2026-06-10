import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3AC0pFoundations
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.ZMod.Basic

/-!
# Layer 3 — Razborov–Smolensky dimension count (#low-degree monomials)

The Smolensky lower bound (`SCOPE_LAYER3_RS_APPROXIMATION.md`, brick 3) closes by a dimension count:
on the Boolean cube, the `x_i^2 = x_i` relation (`boolToZMod_sq`) collapses every monomial to a
**squarefree** (multilinear) one, so every function `{0,1}^n → ZMod p` is computed by a multilinear
polynomial.  Multilinear monomials in `n` variables are in canonical bijection with **subsets** of
`Fin n` (the support), with **total degree = support size**.  Hence the space of functions on a set
`G ⊆ {0,1}^n` computed by degree-`≤ D` polynomials has dimension at most the number of subsets of
`Fin n` of size `≤ D`.

This file builds that count and its comparisons to the cube size `2^n`:

* `lowDegMonomials n D` — the multilinear monomials of degree `≤ D` (as subsets of `Fin n`).
* `lowDegMonomials_card` — `#low-degree monomials = ∑_{k=0}^{D} C(n,k)`.  **The dimension count.**
* `lowDegMonomials_card_full` / `_le_two_pow` / `_lt_two_pow` — total `= 2^n`; bounded by `2^n`;
  *strictly* below `2^n` once `D < n`.
* `lowDegMonomials_card_halfway` — at the Smolensky half-degree (`n = 2m+1`, `D = m`) the count is
  exactly `2^{2m} = 2^{n-1}` (`Nat.sum_range_choose_halfway`).
* `boolToZMod_pow_succ` — the multilinear **reduction lever** `x^{e+1} = x` on `{0,1}` (generalising
  `boolToZMod_sq`), which is what collapses arbitrary monomials to squarefree ones on the cube.

No lower bound, no capstone: this is the combinatorial count `#{monomials of degree ≤ D}` that the
dimension argument feeds on.  The quantitative *band* margin (`< (3/4)·2^n` at `D = n/2 + o(√n)`,
needing central-binomial / entropy estimates) is left as the remaining analytic sub-frontier.  Far
below P vs NP; AC⁰[p] is a higher circuit-lower-bound layer.
-/

namespace PallLean.Paper93.DeepMath.PathB.Layer3

open Finset

/-- The **multilinear (squarefree) monomials of total degree `≤ D`** in `n` variables, presented as the
subsets of `Fin n` of cardinality `≤ D` (a monomial `∏_{i∈s} X_i` has support `s` and degree `|s|`). -/
def lowDegMonomials (n D : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Fin n)).powerset.filter (fun s => s.card ≤ D)

/-- **The dimension count.**  The number of multilinear monomials of degree `≤ D` in `n` variables is
`∑_{k=0}^{D} C(n,k)` — partition the subsets of `Fin n` of size `≤ D` by their exact size `k`, each
block being `powersetCard k univ` of cardinality `C(n,k)`. -/
theorem lowDegMonomials_card (n D : ℕ) :
    (lowDegMonomials n D).card = ∑ k ∈ range (D + 1), n.choose k := by
  classical
  have hbij : lowDegMonomials n D
      = (range (D + 1)).biUnion (fun k => (Finset.univ : Finset (Fin n)).powersetCard k) := by
    ext s
    rw [lowDegMonomials, mem_filter, mem_powerset, mem_biUnion]
    constructor
    · rintro ⟨_, hcard⟩
      exact ⟨s.card, mem_range.mpr (by omega),
        mem_powersetCard.mpr ⟨Finset.subset_univ s, rfl⟩⟩
    · rintro ⟨k, hk, hs⟩
      rw [mem_powersetCard] at hs
      rw [mem_range] at hk
      obtain ⟨_, hsc⟩ := hs
      exact ⟨Finset.subset_univ s, by omega⟩
  have hdisj : ((range (D + 1) : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (fun k => (Finset.univ : Finset (Fin n)).powersetCard k) := by
    intro i _ j _ hij
    refine Finset.disjoint_left.mpr (fun s hsi hsj => ?_)
    rw [mem_powersetCard] at hsi hsj
    exact hij (hsi.2.symm.trans hsj.2)
  rw [hbij, Finset.card_biUnion hdisj]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- All multilinear monomials (`D = n`) number exactly `2^n` — the dimension of *all* functions on the
cube `{0,1}^n` over `ZMod p`. -/
theorem lowDegMonomials_card_full (n : ℕ) : (lowDegMonomials n n).card = 2 ^ n := by
  rw [lowDegMonomials_card, Nat.sum_range_choose]

/-- Any degree threshold's monomial set is contained in the full one (`D = n`). -/
theorem lowDegMonomials_subset_full (n D : ℕ) :
    lowDegMonomials n D ⊆ lowDegMonomials n n := by
  intro s hs
  rw [lowDegMonomials, mem_filter] at hs ⊢
  exact ⟨hs.1, (Finset.card_le_card (Finset.subset_univ s)).trans_eq
    (by rw [Finset.card_univ, Fintype.card_fin])⟩

/-- **Dimension bound:** at most `2^n` multilinear monomials of any degree. -/
theorem lowDegMonomials_card_le_two_pow (n D : ℕ) :
    (lowDegMonomials n D).card ≤ 2 ^ n := by
  rw [← lowDegMonomials_card_full n]
  exact Finset.card_le_card (lowDegMonomials_subset_full n D)

/-- **Strict dimension deficit:** once the degree threshold `D` is below `n`, the count is *strictly*
less than `2^n` — the full monomial `∏_i X_i` (support `univ`, degree `n`) is excluded. -/
theorem lowDegMonomials_card_lt_two_pow (n D : ℕ) (h : D < n) :
    (lowDegMonomials n D).card < 2 ^ n := by
  rw [← lowDegMonomials_card_full n]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset (lowDegMonomials_subset_full n D)]
  refine ⟨Finset.univ, ?_, ?_⟩
  · rw [lowDegMonomials, mem_filter, mem_powerset]
    exact ⟨Finset.subset_univ _, by simp⟩
  · rw [lowDegMonomials, mem_filter, mem_powerset, not_and]
    intro _
    rw [Finset.card_univ, Fintype.card_fin]
    omega

/-- **Half-degree dimension (exact).**  For `n = 2m+1` variables and degree threshold `D = m = ⌊n/2⌋`,
the multilinear-monomial count is exactly `2^{2m} = 2^{n-1}` (`Nat.sum_range_choose_halfway`) — the
base (`Δ = 0`) case of the Smolensky low-degree dimension at the half-degree. -/
theorem lowDegMonomials_card_halfway (m : ℕ) :
    (lowDegMonomials (2 * m + 1) m).card = 2 ^ (2 * m) := by
  rw [lowDegMonomials_card, Nat.sum_range_choose_halfway, show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]

/-- **Multilinear reduction lever.**  On a `{0,1}` value, `x^{e+1} = x` — the generalisation of
`boolToZMod_sq` (`e = 1`) that collapses an arbitrary monomial `∏_i X_i^{e_i}` to the squarefree
`∏_{i : e_i>0} X_i` on the cube, justifying the multilinear (subset) presentation of monomials. -/
theorem boolToZMod_pow_succ (p : ℕ) (b : Bool) (e : ℕ) :
    (boolToZMod p b) ^ (e + 1) = boolToZMod p b := by
  rcases boolToZMod_mem p b with h | h <;> rw [h]
  · exact zero_pow (Nat.succ_ne_zero e)
  · exact one_pow _

end PallLean.Paper93.DeepMath.PathB.Layer3

#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.lowDegMonomials_card
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.lowDegMonomials_card_full
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.lowDegMonomials_card_le_two_pow
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.lowDegMonomials_card_lt_two_pow
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.lowDegMonomials_card_halfway
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.boolToZMod_pow_succ
