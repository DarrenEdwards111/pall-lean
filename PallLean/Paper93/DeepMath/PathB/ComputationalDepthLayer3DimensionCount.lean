import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3AC0pFoundations
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.Algebra.Operations
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

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
open scoped Pointwise

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

/-- **Central-binomial `√n` bound (integer form).**  `(2m+1)·C(2m,m)² ≤ 4^(2m)`, i.e.
`C(2m,m) ≤ 4^m/√(2m+1)` — the Stirling-type estimate that the `Δ ≥ 1` Smolensky band margin needs (and
which Mathlib lacked).  Proved by induction via the central-binomial recurrence
`Nat.succ_mul_centralBinom_succ`, with the step inequality `(2m+3)(2m+1) ≤ 4(m+1)²`. -/
theorem centralBinom_sq_le : ∀ m : ℕ, (2 * m + 1) * (Nat.centralBinom m) ^ 2 ≤ 4 ^ (2 * m)
  | 0 => by simp [Nat.centralBinom_zero]
  | m + 1 => by
      have ih := centralBinom_sq_le m
      have hrec := Nat.succ_mul_centralBinom_succ m
      set c := Nat.centralBinom m
      set c' := Nat.centralBinom (m + 1)
      have e1 : (m + 1) ^ 2 * c' ^ 2 = 4 * (2 * m + 1) ^ 2 * c ^ 2 := by
        rw [← mul_pow, hrec]; ring
      have key : (m + 1) ^ 2 * ((2 * (m + 1) + 1) * c' ^ 2)
          ≤ (m + 1) ^ 2 * 4 ^ (2 * (m + 1)) := by
        have h4 : (4 : ℕ) ^ (2 * (m + 1)) = 16 * 4 ^ (2 * m) := by
          rw [show 2 * (m + 1) = 2 * m + 2 from by ring, pow_add]; ring
        calc (m + 1) ^ 2 * ((2 * (m + 1) + 1) * c' ^ 2)
            = (2 * (m + 1) + 1) * ((m + 1) ^ 2 * c' ^ 2) := by ring
          _ = (2 * (m + 1) + 1) * (4 * (2 * m + 1) ^ 2 * c ^ 2) := by rw [e1]
          _ = 4 * (2 * (m + 1) + 1) * (2 * m + 1) * ((2 * m + 1) * c ^ 2) := by ring
          _ ≤ 4 * (2 * (m + 1) + 1) * (2 * m + 1) * 4 ^ (2 * m) := Nat.mul_le_mul_left _ ih
          _ ≤ (m + 1) ^ 2 * 16 * 4 ^ (2 * m) := Nat.mul_le_mul_right _ (by nlinarith)
          _ = (m + 1) ^ 2 * 4 ^ (2 * (m + 1)) := by rw [h4]; ring
      exact Nat.le_of_mul_le_mul_left key (by positivity)

/-- **Smolensky band margin at the half-degree (Δ = 0).**  At `D = m = ⌊n/2⌋` (`n = 2m+1`) the dimension
count is `2^{n-1}`, which is *strictly below* the `(3/4)·2^n` Smolensky threshold (integer form
`4·count < 3·2^n`).  So the base case of the dimension contradiction needs **no** central-binomial
estimate.  (The `Δ ≥ 1` band — `∑_{k≤m+Δ} C(2m+1,k) < (3/4)·2^n` — genuinely needs
`C(2m+1,m) ≤ 2^n/√n`, a Stirling-type bound absent from Mathlib; with only the trivial
`Nat.choose_middle_le_pow` (`C(2m+1,m) ≤ 4^m`) the band bound `Δ·4^m` is too weak.) -/
theorem lowDegMonomials_card_halfway_margin (m : ℕ) :
    4 * (lowDegMonomials (2 * m + 1) m).card < 3 * 2 ^ (2 * m + 1) := by
  rw [lowDegMonomials_card_halfway, pow_succ]
  have hX : 1 ≤ 2 ^ (2 * m) := Nat.one_le_pow _ _ (by norm_num)
  omega

/-! **Smolensky band margin (Δ ≥ 1).**  For `D = m + Δ` (`n = 2m+1`) with `Δ` in the
`O(√m)` window `16·Δ² < 2m+3`, the low-degree monomial count is still `< (3/4)·2^n` (integer form
`4·count < 3·2^n`).  Decompose `∑_{k≤m+Δ} = 2^{2m} + (band ∑_{k=m+1}^{m+Δ})`; bound the band by
`Δ·C(2m+1,m)` (each `≤` central via `Nat.choose_le_middle`); then the crux
`Δ·C(2m+1,m)·2 = Δ·centralBinom(m+1) < 2^{2m}` follows by squaring and `centralBinom_sq_le` with the
window condition.  This closes the band margin for the full Smolensky degree window. -/
open Finset in
theorem lowDegMonomials_card_band_margin (m Δ : ℕ) (hΔ : 16 * Δ ^ 2 < 2 * m + 3) :
    4 * (lowDegMonomials (2 * m + 1) (m + Δ)).card < 3 * 2 ^ (2 * m + 1) := by
  have hCB : Nat.centralBinom (m + 1) = 2 * (2 * m + 1).choose m := by
    rw [Nat.centralBinom, show 2 * (m + 1) = 2 * m + 1 + 1 from by ring, Nat.choose_succ_succ,
      Nat.choose_symm_half]; omega
  rw [lowDegMonomials_card]
  have hdecomp : (∑ k ∈ range (m + Δ + 1), (2 * m + 1).choose k)
      = (∑ k ∈ range (m + 1), (2 * m + 1).choose k)
        + (∑ k ∈ Ico (m + 1) (m + Δ + 1), (2 * m + 1).choose k) := by
    simp only [Finset.range_eq_Ico]
    exact (Finset.sum_Ico_consecutive _ (Nat.zero_le (m + 1)) (by omega)).symm
  rw [hdecomp, Nat.sum_range_choose_halfway]
  have hband : (∑ k ∈ Ico (m + 1) (m + Δ + 1), (2 * m + 1).choose k)
      ≤ Δ * (2 * m + 1).choose m := by
    calc (∑ k ∈ Ico (m + 1) (m + Δ + 1), (2 * m + 1).choose k)
        ≤ ∑ _k ∈ Ico (m + 1) (m + Δ + 1), (2 * m + 1).choose m :=
          Finset.sum_le_sum (fun k _ => by
            have hmid : (2 * m + 1) / 2 = m := by omega
            calc (2 * m + 1).choose k ≤ (2 * m + 1).choose ((2 * m + 1) / 2) :=
                  Nat.choose_le_middle k (2 * m + 1)
              _ = (2 * m + 1).choose m := by rw [hmid])
      _ = (Ico (m + 1) (m + Δ + 1)).card * (2 * m + 1).choose m := by
          rw [Finset.sum_const, smul_eq_mul]
      _ = Δ * (2 * m + 1).choose m := by rw [Nat.card_Ico]; congr 1; omega
  have hcrux : Δ * Nat.centralBinom (m + 1) < 2 ^ (2 * m) := by
    set B := Nat.centralBinom (m + 1)
    have hcb_sq : (2 * m + 3) * B ^ 2 ≤ 16 * (2 ^ (2 * m)) ^ 2 := by
      have hsl := centralBinom_sq_le (m + 1)
      have h3 : (4 : ℕ) ^ (2 * (m + 1)) = 16 * (2 ^ (2 * m)) ^ 2 := by
        rw [show 2 * (m + 1) = 2 * m + 2 from by ring, pow_add,
          show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul, ← pow_mul]; ring
      rw [show 2 * (m + 1) + 1 = 2 * m + 3 from by ring, h3] at hsl; exact hsl
    have hkey : (2 * m + 3) * (Δ * B) ^ 2 < (2 * m + 3) * (2 ^ (2 * m)) ^ 2 := by
      calc (2 * m + 3) * (Δ * B) ^ 2 = Δ ^ 2 * ((2 * m + 3) * B ^ 2) := by ring
        _ ≤ Δ ^ 2 * (16 * (2 ^ (2 * m)) ^ 2) := by gcongr
        _ = (16 * Δ ^ 2) * (2 ^ (2 * m)) ^ 2 := by ring
        _ < (2 * m + 3) * (2 ^ (2 * m)) ^ 2 := by gcongr
    have hsq : (Δ * B) ^ 2 < (2 ^ (2 * m)) ^ 2 := Nat.lt_of_mul_lt_mul_left hkey
    exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) hsq
  have h4m : (4 : ℕ) ^ m = 2 ^ (2 * m) := by rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]
  rw [h4m, show 3 * 2 ^ (2 * m + 1) = 6 * 2 ^ (2 * m) from by rw [pow_succ]; ring]
  calc 4 * (2 ^ (2 * m) + (∑ k ∈ Ico (m + 1) (m + Δ + 1), (2 * m + 1).choose k))
      ≤ 4 * (2 ^ (2 * m) + Δ * (2 * m + 1).choose m) := by gcongr
    _ = 4 * 2 ^ (2 * m) + 2 * (Δ * Nat.centralBinom (m + 1)) := by rw [hCB]; ring
    _ < 4 * 2 ^ (2 * m) + 2 * 2 ^ (2 * m) := by gcongr
    _ = 6 * 2 ^ (2 * m) := by ring

/-! ## Smolensky degree-halving (the `MOD_q`-reduction mechanism)

The dimension contradiction needs every function on the agreement set `G` to be a degree-`(n/2+Δ)`
polynomial.  The mechanism: pass to the `±1` cube (`pmOne`), where `y² = 1`, so a monomial
`χ_S = ∏_{i∈S} y_i` equals `χ_univ · χ_{Sᶜ}` (the full product times the complementary monomial of
degree `n-|S|`).  Once `χ_univ` agrees on `G` with the degree-`Δ` `AC⁰[p]` approximant `g`, a
high-degree monomial (`|S| > n/2`) collapses to `g · χ_{Sᶜ}` of degree `≤ Δ + (n-|S|) ≤ Δ + n/2`. -/

/-- `±1` encoding of a Boolean over `ZMod p` (`true ↦ -1`, `false ↦ 1`). -/
def pmOne (p : ℕ) (b : Bool) : ZMod p := if b then -1 else 1

/-- `(±1)² = 1` — the squaring identity underlying the degree-halving. -/
theorem pmOne_mul_self (p : ℕ) (b : Bool) : pmOne p b * pmOne p b = 1 := by cases b <;> simp [pmOne]

/-- **Degree-halving (evaluation form).**  `χ_univ · χ_{Sᶜ} = χ_S` on the `±1` cube. -/
theorem pm_monomial_halving (p : ℕ) {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) :
    (∏ i, pmOne p (x i)) * (∏ i ∈ Sᶜ, pmOne p (x i)) = ∏ i ∈ S, pmOne p (x i) := by
  rw [← Finset.prod_mul_prod_compl S (fun i => pmOne p (x i)), mul_assoc, ← Finset.prod_mul_distrib]
  simp only [pmOne_mul_self, Finset.prod_const_one, mul_one]

/-- **`±1` monomials form the group algebra of `(ℤ/2)ⁿ`.**  `χ_S · χ_T = χ_{S∆T}` (here `S∆T = (S∪T)\(S∩T)`):
the common indices square to `1` and cancel.  This multiplicative closure is what makes the linear span
of `{χ_S}` a *subalgebra* — the engine of the multilinear-basis argument (the `χ`-analogue of
`squarefreeEvalMonomial_mul`). -/
theorem pm_monomial_mul (p : ℕ) {n : ℕ} (S T : Finset (Fin n)) (x : Fin n → Bool) :
    (∏ i ∈ S, pmOne p (x i)) * (∏ i ∈ T, pmOne p (x i))
      = ∏ i ∈ (S ∪ T) \ (S ∩ T), pmOne p (x i) := by
  rw [← Finset.prod_union_inter,
    ← Finset.prod_sdiff (Finset.inter_subset_left.trans Finset.subset_union_left : S ∩ T ⊆ S ∪ T),
    mul_assoc, ← Finset.prod_mul_distrib]
  simp only [pmOne_mul_self, Finset.prod_const_one, mul_one]

open MvPolynomial in
/-- The `±1` monomial `χ_S = ∏_{i∈S} (1 - 2 X_i)` as a polynomial (degree `≤ |S|`). -/
noncomputable def pmMonomial (p : ℕ) {n : ℕ} (S : Finset (Fin n)) : MvPolynomial (Fin n) (ZMod p) :=
  ∏ i ∈ S, (1 - 2 * X i)

open MvPolynomial in
/-- `χ_S` has total degree `≤ |S|` (each factor `1 - 2 X_i` is degree `≤ 1`). -/
theorem pmMonomial_totalDegree_le (p : ℕ) [Fact p.Prime] {n : ℕ} (S : Finset (Fin n)) :
    (pmMonomial p S).totalDegree ≤ S.card := by
  refine le_trans (totalDegree_finset_prod S _) ?_
  refine le_trans (Finset.sum_le_sum (fun i _ => ?_)) (by rw [Finset.sum_const, smul_eq_mul, mul_one])
  refine le_trans (totalDegree_sub _ _) (max_le ?_ ?_)
  · rw [totalDegree_one]; exact Nat.zero_le 1
  · calc (2 * X i : MvPolynomial (Fin n) (ZMod p)).totalDegree
        ≤ (2 : MvPolynomial (Fin n) (ZMod p)).totalDegree + (X i).totalDegree := totalDegree_mul _ _
      _ = 1 := by
          rw [show (2 : MvPolynomial (Fin n) (ZMod p)) = C 2 from (map_ofNat C 2).symm,
            totalDegree_C, totalDegree_X]

open MvPolynomial in
/-- `χ_S` evaluated at `boolToZMod ∘ x` is `∏_{i∈S} pmOne (x i)` (so the polynomial represents the
`±1` monomial function on the cube). -/
theorem pmMonomial_eval (p : ℕ) {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) :
    eval (fun i => boolToZMod p (x i)) (pmMonomial p S) = ∏ i ∈ S, pmOne p (x i) := by
  rw [pmMonomial, map_prod]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  simp only [map_sub, map_one, map_mul, map_ofNat, eval_X, boolToZMod, pmOne]
  cases x i <;> simp <;> ring

open MvPolynomial in
/-- **The `MOD_q`-reduction step.**  If a degree-`Δ` polynomial `g` represents the full `±1` product
`χ_univ` on `G`, then *every* `±1` monomial `χ_S` agrees on `G` with a polynomial of degree
`≤ Δ + (n-|S|)` (namely `g · χ_{Sᶜ}`).  For `|S| > n/2` this is `≤ Δ + n/2` — the degree-halving that
collapses the dimension of functions on `G` to the low-degree count. -/
theorem pm_monomial_reduction (p : ℕ) [Fact p.Prime] {n : ℕ} (G : Finset (Fin n → Bool)) (Δ : ℕ)
    (g : MvPolynomial (Fin n) (ZMod p)) (hgdeg : g.totalDegree ≤ Δ)
    (hg : ∀ x ∈ G, eval (fun i => boolToZMod p (x i)) g = ∏ i, pmOne p (x i))
    (S : Finset (Fin n)) :
    ∃ h : MvPolynomial (Fin n) (ZMod p), h.totalDegree ≤ Δ + (n - S.card) ∧
      ∀ x ∈ G, eval (fun i => boolToZMod p (x i)) h = ∏ i ∈ S, pmOne p (x i) := by
  refine ⟨g * pmMonomial p Sᶜ, ?_, fun x hx => ?_⟩
  · exact le_trans (totalDegree_mul _ _)
      (le_trans (Nat.add_le_add hgdeg (pmMonomial_totalDegree_le p Sᶜ))
        (le_of_eq (by rw [Finset.card_compl, Fintype.card_fin])))
  · rw [map_mul, hg x hx, pmMonomial_eval]; exact pm_monomial_halving p S x

/-- **Multilinear reduction lever.**  On a `{0,1}` value, `x^{e+1} = x` — the generalisation of
`boolToZMod_sq` (`e = 1`) that collapses an arbitrary monomial `∏_i X_i^{e_i}` to the squarefree
`∏_{i : e_i>0} X_i` on the cube, justifying the multilinear (subset) presentation of monomials. -/
theorem boolToZMod_pow_succ (p : ℕ) (b : Bool) (e : ℕ) :
    (boolToZMod p b) ^ (e + 1) = boolToZMod p b := by
  rcases boolToZMod_mem p b with h | h <;> rw [h]
  · exact zero_pow (Nat.succ_ne_zero e)
  · exact one_pow _

/-! ## The linear-algebra bridge: dimension ≤ #low-degree monomials

The dimension count becomes a *Smolensky dimension tool* once we connect it to the actual function
space.  On the Boolean cube, the squarefree monomial `∏_{i∈S} X_i` becomes the **evaluation function**
`x ↦ ∏_{i∈S} x_i` (`squarefreeEvalMonomial`).  These evaluation functions, ranging over the low-degree
monomials `S ∈ lowDegMonomials n D`, span a subspace of the function space `(Fin n → Bool) → ZMod p`
whose dimension is at most their number — and that number is the count `∑_{k≤D} C(n,k)`
(`lowDegMonomials_card`).  This is the "dimension ≤ #monomials" half of the Smolensky argument.

(The other half — that *every* function on the agreement set `G` lands in this span after the
`MOD_q`-reduction, pushing the degree to `n/2 + Δ` — is the composition step, deferred.) -/

/-- The **Boolean-cube evaluation function** of the squarefree monomial with support `S`:
`x ↦ ∏_{i∈S} x_i` (over `ZMod p`, with `x_i ∈ {0,1}` via `boolToZMod`). -/
noncomputable def squarefreeEvalMonomial (p : ℕ) {n : ℕ} (S : Finset (Fin n)) :
    (Fin n → Bool) → ZMod p :=
  fun x => ∏ i ∈ S, boolToZMod p (x i)

/-- Each low-degree squarefree evaluation function is, trivially, in the span of the family — these are
the generators.  (After the `MOD_q`-reduction every cube function reduces to such a combination; that
reduction is the deferred composition step.) -/
theorem squarefreeEvalMonomial_mem_span (p : ℕ) [Fact p.Prime] {n D : ℕ}
    {S : Finset (Fin n)} (hS : S ∈ lowDegMonomials n D) :
    squarefreeEvalMonomial p S ∈ Submodule.span (ZMod p)
      (Set.range (fun T : {T // T ∈ lowDegMonomials n D} => squarefreeEvalMonomial p T.1)) :=
  Submodule.subset_span ⟨⟨S, hS⟩, rfl⟩

/-- **The dimension bridge.**  The span of the low-degree squarefree evaluation functions has
`ZMod p`-dimension at most the number of low-degree monomials `∑_{k≤D} C(n,k)`
(`lowDegMonomials_card`).  This turns the combinatorial count into a genuine bound on the dimension of
the space of functions a degree-`≤D` multilinear polynomial can realise on the cube. -/
theorem finrank_span_lowDegEval_le_card (p n D : ℕ) [Fact p.Prime] :
    Module.finrank (ZMod p)
      (Submodule.span (ZMod p)
        (Set.range (fun S : {S // S ∈ lowDegMonomials n D} => squarefreeEvalMonomial p S.1)))
      ≤ (lowDegMonomials n D).card := by
  classical
  refine le_trans (finrank_span_le_card _) ?_
  rw [Set.toFinset_range]
  refine le_trans Finset.card_image_le (le_of_eq ?_)
  rw [Finset.card_univ, Fintype.card_coe]

/-- **Dimension bridge, count form.**  Chaining the bridge with `lowDegMonomials_card`, the span
dimension is at most `∑_{k=0}^{D} C(n,k)` — the explicit Smolensky low-degree dimension bound. -/
theorem finrank_span_lowDegEval_le_sum (p n D : ℕ) [Fact p.Prime] :
    Module.finrank (ZMod p)
      (Submodule.span (ZMod p)
        (Set.range (fun S : {S // S ∈ lowDegMonomials n D} => squarefreeEvalMonomial p S.1)))
      ≤ ∑ k ∈ Finset.range (D + 1), n.choose k := by
  rw [← lowDegMonomials_card]
  exact finrank_span_lowDegEval_le_card p n D

/-! ## The dimension deficit: low-degree polynomials cannot compute all cube functions

Combining the bridge (`finrank_span_lowDegEval_le_card`) with the strict count `< 2^n`
(`lowDegMonomials_card_lt_two_pow`) and the ambient dimension `2^n` of the cube-function space gives
the **dimension deficit** at the heart of Smolensky: once the degree threshold `D` is below `n`, the
degree-`≤D` squarefree evaluation functions cannot span all of `(Fin n → Bool) → ZMod p`.  In the full
argument the `MOD_q`-reduction would force *every* cube function into a degree-`(n/2+Δ) < n` span,
contradicting exactly this deficit. -/

/-- The cube-function space `(Fin n → Bool) → ZMod p` has `ZMod p`-dimension `2^n`
(`Module.finrank_fintype_fun_eq_card`: the domain `Fin n → Bool` has `2^n` points). -/
theorem finrank_cubeFunctions_eq (p n : ℕ) [Fact p.Prime] :
    Module.finrank (ZMod p) ((Fin n → Bool) → ZMod p) = 2 ^ n := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- **Dimension deficit.**  For `D < n`, the degree-`≤D` squarefree evaluation functions do *not* span
the cube-function space: if they did, the ambient dimension `2^n` would be `≤ #monomials < 2^n`. -/
theorem lowDegEval_span_ne_top (p n D : ℕ) [Fact p.Prime] (h : D < n) :
    Submodule.span (ZMod p)
        (Set.range (fun S : {S // S ∈ lowDegMonomials n D} => squarefreeEvalMonomial p S.1))
      ≠ (⊤ : Submodule (ZMod p) ((Fin n → Bool) → ZMod p)) := by
  intro hspan
  have h1 := finrank_span_lowDegEval_le_card p n D
  rw [hspan, finrank_top, finrank_cubeFunctions_eq] at h1
  have h2 := lowDegMonomials_card_lt_two_pow n D h
  omega

/-- **Concrete deficit witness.**  For `D < n` there is a Boolean function `{0,1}^n → ZMod p` not in the
span of the degree-`≤D` squarefree evaluation monomials — a function no degree-`≤D` multilinear
polynomial computes on the cube. -/
theorem exists_cubeFunction_not_lowDegEval (p n D : ℕ) [Fact p.Prime] (h : D < n) :
    ∃ f : (Fin n → Bool) → ZMod p, f ∉ Submodule.span (ZMod p)
      (Set.range (fun S : {S // S ∈ lowDegMonomials n D} => squarefreeEvalMonomial p S.1)) := by
  by_contra hcon
  push_neg at hcon
  exact lowDegEval_span_ne_top p n D h (Submodule.eq_top_iff'.mpr hcon)

/-! ## The algebraic lever: multilinear monomials are multiplicatively closed on the cube

The composition step of Smolensky repeatedly *multiplies* monomials (and the `MOD_q`-approximant) and
must keep the degree controlled.  On the Boolean cube the `x_i^2 = x_i` relation makes the squarefree
evaluation monomials **multiplicatively closed**: `e_S · e_T = e_{S∪T}` (`squarefreeEvalMonomial_mul`),
with the constant `1 = e_∅` (`squarefreeEvalMonomial_empty`).  Crucially the degree is **subadditive**:
`deg(e_S · e_T) = |S∪T| ≤ |S| + |T|` (`squarefreeEvalMonomial_mul_card_le`) — multiplication does not
blow degree up to the *product* of fan-ins, which is exactly why the reduced polynomial stays low
degree.  This is the function-level form of the `boolToZMod_sq` / `boolToZMod_pow_succ` lever, and the
algebraic engine of the deferred composition step. -/

/-- The empty squarefree monomial is the constant function `1`. -/
theorem squarefreeEvalMonomial_empty (p : ℕ) {n : ℕ} :
    squarefreeEvalMonomial p (∅ : Finset (Fin n)) = 1 := by
  funext x
  simp [squarefreeEvalMonomial]

/-- **Multiplicative closure on the cube.**  `e_S · e_T = e_{S∪T}`: the product of two squarefree
evaluation monomials is the squarefree evaluation monomial on the union of supports — the overlap
`S ∩ T` is absorbed by idempotence `x_i^2 = x_i` (`boolToZMod_mem`). -/
theorem squarefreeEvalMonomial_mul (p : ℕ) {n : ℕ} (S T : Finset (Fin n)) :
    squarefreeEvalMonomial p S * squarefreeEvalMonomial p T
      = squarefreeEvalMonomial p (S ∪ T) := by
  classical
  funext x
  simp only [squarefreeEvalMonomial, Pi.mul_apply]
  have hidem : ∀ i : Fin n,
      boolToZMod p (x i) * boolToZMod p (x i) = boolToZMod p (x i) := by
    intro i; rcases boolToZMod_mem p (x i) with h | h <;> rw [h] <;> ring
  have hPP : (∏ i ∈ S ∩ T, boolToZMod p (x i)) * (∏ i ∈ S ∩ T, boolToZMod p (x i))
      = ∏ i ∈ S ∩ T, boolToZMod p (x i) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => hidem i)
  have hsub : S ∩ T ⊆ S ∪ T := Finset.inter_subset_left.trans Finset.subset_union_left
  rw [← Finset.prod_union_inter]
  conv_rhs => rw [← Finset.prod_sdiff hsub]
  conv_lhs => rw [← Finset.prod_sdiff hsub]
  rw [mul_assoc, hPP]

/-- **Degree subadditivity under multiplication.**  The product `e_S · e_T` is a squarefree evaluation
monomial whose support has size `≤ |S| + |T|` — so multiplying a degree-`≤D₁` by a degree-`≤D₂`
multilinear monomial yields a degree-`≤(D₁+D₂)` one, the degree bookkeeping the reduction relies on. -/
theorem squarefreeEvalMonomial_mul_card_le (p : ℕ) {n : ℕ} (S T : Finset (Fin n)) :
    ∃ U : Finset (Fin n),
      squarefreeEvalMonomial p S * squarefreeEvalMonomial p T = squarefreeEvalMonomial p U
        ∧ U.card ≤ S.card + T.card :=
  ⟨S ∪ T, squarefreeEvalMonomial_mul p S T, Finset.card_union_le S T⟩

/-! ## Spanning: the squarefree monomials span the entire cube-function space

The other half of the dimension argument's easy direction: the squarefree evaluation monomials don't
just bound the dimension from above — they actually **span** the whole function space
`(Fin n → Bool) → ZMod p`.  The engine is the algebraic lever (`squarefreeEvalMonomial_mul`): it makes
the span a *subalgebra* (`mul_mem_squarefreeSpan`), so the indicator of a point,
`δ_y = ∏_i (y_i ? x_i : 1-x_i)`, being a product of degree-`≤1` monomials, lands in the span
(`single_eq_prod_factor` + `prod_mem_squarefreeSpan`); the indicators are a basis, so the span is all of
the space (`squarefreeSpan_eq_top`).  Consequently *every* Boolean function is a multilinear polynomial
over `ZMod p` (`mem_squarefreeSpan`). -/

/-- The submodule spanned by **all** squarefree evaluation monomials in `n` variables. -/
noncomputable def squarefreeSpan (p n : ℕ) :
    Submodule (ZMod p) ((Fin n → Bool) → ZMod p) :=
  Submodule.span (ZMod p) (Set.range (fun S : Finset (Fin n) => squarefreeEvalMonomial p S))

/-- Each squarefree monomial is a generator, hence in the span. -/
theorem squarefreeEvalMonomial_mem_squarefreeSpan (p n : ℕ) (S : Finset (Fin n)) :
    squarefreeEvalMonomial p S ∈ squarefreeSpan p n :=
  Submodule.subset_span ⟨S, rfl⟩

/-- `1 = e_∅` is in the span. -/
theorem one_mem_squarefreeSpan (p n : ℕ) :
    (1 : (Fin n → Bool) → ZMod p) ∈ squarefreeSpan p n := by
  have h1 : (1 : (Fin n → Bool) → ZMod p) = squarefreeEvalMonomial p (∅ : Finset (Fin n)) :=
    (squarefreeEvalMonomial_empty p).symm
  rw [h1]
  exact squarefreeEvalMonomial_mem_squarefreeSpan p n ∅

/-- **The span is multiplicatively closed** (a subalgebra): products of generators are generators
(`squarefreeEvalMonomial_mul`), so `span · span ≤ span`. -/
theorem mul_mem_squarefreeSpan (p n : ℕ) {u v : (Fin n → Bool) → ZMod p}
    (hu : u ∈ squarefreeSpan p n) (hv : v ∈ squarefreeSpan p n) :
    u * v ∈ squarefreeSpan p n := by
  have hdef : squarefreeSpan p n
      = Submodule.span (ZMod p)
          (Set.range (fun S : Finset (Fin n) => squarefreeEvalMonomial p S)) := rfl
  have hclosed : squarefreeSpan p n * squarefreeSpan p n ≤ squarefreeSpan p n := by
    rw [hdef, Submodule.span_mul_span, Submodule.span_le]
    rintro c hc
    rw [Set.mem_mul] at hc
    obtain ⟨a, ⟨S, rfl⟩, b, ⟨T, rfl⟩, rfl⟩ := hc
    rw [squarefreeEvalMonomial_mul]
    exact Submodule.subset_span ⟨S ∪ T, rfl⟩
  exact hclosed (Submodule.mul_mem_mul hu hv)

/-- A finite product of span members is a span member (multiplicative closure + `1 ∈ span`). -/
theorem prod_mem_squarefreeSpan (p n : ℕ) {ι : Type*} (s : Finset ι)
    (g : ι → (Fin n → Bool) → ZMod p) (hg : ∀ i ∈ s, g i ∈ squarefreeSpan p n) :
    (∏ i ∈ s, g i) ∈ squarefreeSpan p n :=
  Finset.prod_induction g (· ∈ squarefreeSpan p n)
    (fun _ _ ha hb => mul_mem_squarefreeSpan p n ha hb)
    (one_mem_squarefreeSpan p n) hg

/-- Each indicator factor `x ↦ (y_i ? x_i : 1-x_i)` is in the span: it is `e_{i}` (degree-1 monomial)
when `y_i = true`, and `1 - e_{i}` when `y_i = false`. -/
theorem factor_mem_squarefreeSpan (p n : ℕ) (y : Fin n → Bool) (i : Fin n) :
    (fun x : Fin n → Bool => if y i then boolToZMod p (x i) else 1 - boolToZMod p (x i))
      ∈ squarefreeSpan p n := by
  by_cases hyi : y i = true
  · have he : (fun x : Fin n → Bool =>
          if y i then boolToZMod p (x i) else 1 - boolToZMod p (x i))
        = squarefreeEvalMonomial p ({i} : Finset (Fin n)) := by
      funext x
      simp [hyi, squarefreeEvalMonomial, Finset.prod_singleton]
    rw [he]
    exact squarefreeEvalMonomial_mem_squarefreeSpan p n {i}
  · have he : (fun x : Fin n → Bool =>
          if y i then boolToZMod p (x i) else 1 - boolToZMod p (x i))
        = 1 - squarefreeEvalMonomial p ({i} : Finset (Fin n)) := by
      funext x
      simp [hyi, squarefreeEvalMonomial, Finset.prod_singleton, Pi.sub_apply, Pi.one_apply]
    rw [he]
    exact Submodule.sub_mem _ (one_mem_squarefreeSpan p n)
      (squarefreeEvalMonomial_mem_squarefreeSpan p n {i})

/-- **Indicator as a monomial product.**  The point indicator `Pi.single y 1` equals the product over
coordinates of the degree-`≤1` factors `(y_i ? x_i : 1-x_i)` — value `1` iff `x = y`, else `0`. -/
theorem single_eq_prod_factor (p n : ℕ) (y : Fin n → Bool) :
    (Pi.single y (1 : ZMod p) : (Fin n → Bool) → ZMod p)
      = ∏ i, (fun x : Fin n → Bool =>
          if y i then boolToZMod p (x i) else 1 - boolToZMod p (x i)) := by
  funext x
  rw [Finset.prod_apply, Pi.single_apply]
  have hfac : ∀ i : Fin n,
      (if y i then boolToZMod p (x i) else 1 - boolToZMod p (x i))
        = (if x i = y i then (1 : ZMod p) else 0) := by
    intro i; cases y i <;> cases x i <;> simp [boolToZMod_true, boolToZMod_false]
  simp_rw [hfac]
  rw [Fintype.prod_boole]
  by_cases h : x = y
  · subst h; simp
  · rw [if_neg h, if_neg (fun hall => h (funext hall))]

/-- **Spanning.**  The squarefree evaluation monomials span the entire cube-function space:
`squarefreeSpan p n = ⊤`.  (The point indicators `Pi.single y 1` form a basis and each lies in the
span as a product of degree-`≤1` factors.) -/
theorem squarefreeSpan_eq_top (p n : ℕ) : squarefreeSpan p n = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun (ZMod p) (Fin n → Bool)).span_eq, Submodule.span_le]
  rintro _ ⟨y, rfl⟩
  rw [Pi.basisFun_apply, single_eq_prod_factor]
  exact prod_mem_squarefreeSpan p n _ _ (fun i _ => factor_mem_squarefreeSpan p n y i)

/-- **Every Boolean function is a multilinear polynomial.**  Each `f : (Fin n → Bool) → ZMod p` is a
`ZMod p`-linear combination of squarefree monomials. -/
theorem mem_squarefreeSpan (p n : ℕ) (f : (Fin n → Bool) → ZMod p) :
    f ∈ squarefreeSpan p n := by
  rw [squarefreeSpan_eq_top]; exact Submodule.mem_top

/-! ## The `±1` multilinear basis (`χ_S` span the cube-function space)

The `MOD_q`-reduction needs *every* function on the agreement set to be expressible via the `±1`
monomials `χ_S` (so the degree-halving `pm_monomial_reduction` applies termwise).  We prove the `±1`
monomials span the whole cube-function space — the `±1` analogue of `squarefreeSpan_eq_top`, built on
the group-algebra structure `pm_monomial_mul` (closure ⇒ subalgebra) and the single-variable change of
basis `boolToZMod = 2⁻¹(1 - χ_{i})` (needs `2 ≠ 0`, i.e. `p` odd). -/

/-- Single-variable change of basis (`{0,1}` ↦ `±1`): `boolToZMod b = 2⁻¹(1 - pmOne b)` (`p` odd). -/
theorem boolToZMod_eq_pm (p : ℕ) [Fact p.Prime] (hp2 : (2 : ZMod p) ≠ 0) (b : Bool) :
    boolToZMod p b = 2⁻¹ * (1 - pmOne p b) := by
  have h : (2 : ZMod p) * boolToZMod p b = 1 - pmOne p b := by
    cases b <;> simp [boolToZMod, pmOne] <;> ring
  refine mul_left_cancel₀ hp2 ?_; rw [h, ← mul_assoc, mul_inv_cancel₀ hp2, one_mul]

/-- The complementary change of basis: `1 - boolToZMod b = 2⁻¹(1 + pmOne b)` (`p` odd). -/
theorem one_sub_boolToZMod_eq_pm (p : ℕ) [Fact p.Prime] (hp2 : (2 : ZMod p) ≠ 0) (b : Bool) :
    1 - boolToZMod p b = 2⁻¹ * (1 + pmOne p b) := by
  have h : (2 : ZMod p) * (1 - boolToZMod p b) = 1 + pmOne p b := by
    cases b <;> simp [boolToZMod, pmOne] <;> ring
  refine mul_left_cancel₀ hp2 ?_; rw [h, ← mul_assoc, mul_inv_cancel₀ hp2, one_mul]

/-- The `±1` monomial `χ_S` as a function on the cube. -/
noncomputable def pmEvalMonomial (p : ℕ) {n : ℕ} (S : Finset (Fin n)) : (Fin n → Bool) → ZMod p :=
  fun x => ∏ i ∈ S, pmOne p (x i)

/-- The submodule spanned by all `±1` monomials. -/
noncomputable def pmSpan (p n : ℕ) : Submodule (ZMod p) ((Fin n → Bool) → ZMod p) :=
  Submodule.span (ZMod p) (Set.range (fun S : Finset (Fin n) => pmEvalMonomial p S))

theorem pmEvalMonomial_mem_pmSpan (p n : ℕ) (S : Finset (Fin n)) :
    pmEvalMonomial p S ∈ pmSpan p n := Submodule.subset_span ⟨S, rfl⟩

theorem one_mem_pmSpan (p n : ℕ) : (1 : (Fin n → Bool) → ZMod p) ∈ pmSpan p n := by
  have : (1 : (Fin n → Bool) → ZMod p) = pmEvalMonomial p (∅ : Finset (Fin n)) := by
    funext x; simp [pmEvalMonomial]
  rw [this]; exact pmEvalMonomial_mem_pmSpan p n ∅

/-- **The `±1` span is multiplicatively closed** (a subalgebra): `χ_S · χ_T = χ_{S∆T}`
(`pm_monomial_mul`) is again a generator. -/
theorem mul_mem_pmSpan (p n : ℕ) {u v : (Fin n → Bool) → ZMod p}
    (hu : u ∈ pmSpan p n) (hv : v ∈ pmSpan p n) : u * v ∈ pmSpan p n := by
  have hclosed : pmSpan p n * pmSpan p n ≤ pmSpan p n := by
    rw [pmSpan, Submodule.span_mul_span, Submodule.span_le]
    rintro c hc; rw [Set.mem_mul] at hc
    obtain ⟨a, ⟨S, rfl⟩, b, ⟨T, rfl⟩, rfl⟩ := hc
    have heq : pmEvalMonomial p S * pmEvalMonomial p T = pmEvalMonomial p ((S ∪ T) \ (S ∩ T)) := by
      funext x; exact pm_monomial_mul p S T x
    rw [heq]; exact Submodule.subset_span ⟨(S ∪ T) \ (S ∩ T), rfl⟩
  exact hclosed (Submodule.mul_mem_mul hu hv)

theorem prod_mem_pmSpan (p n : ℕ) {ι : Type*} (s : Finset ι) (g : ι → (Fin n → Bool) → ZMod p)
    (hg : ∀ i ∈ s, g i ∈ pmSpan p n) : (∏ i ∈ s, g i) ∈ pmSpan p n :=
  Finset.prod_induction g (· ∈ pmSpan p n) (fun _ _ ha hb => mul_mem_pmSpan p n ha hb)
    (one_mem_pmSpan p n) hg

/-- Each indicator factor is in the `±1` span (via the single-variable change of basis to `χ_{i}`). -/
theorem factor_mem_pmSpan (p n : ℕ) [Fact p.Prime] (hp2 : (2 : ZMod p) ≠ 0) (y : Fin n → Bool)
    (i : Fin n) :
    (fun x : Fin n → Bool => if y i then boolToZMod p (x i) else 1 - boolToZMod p (x i))
      ∈ pmSpan p n := by
  by_cases hyi : y i = true
  · have he : (fun x : Fin n → Bool => if y i then boolToZMod p (x i) else 1 - boolToZMod p (x i))
        = (2 : ZMod p)⁻¹ • ((1 : (Fin n → Bool) → ZMod p) - pmEvalMonomial p ({i} : Finset (Fin n))) := by
      funext x
      simp only [hyi, if_true, Pi.smul_apply, Pi.sub_apply, Pi.one_apply, pmEvalMonomial,
        Finset.prod_singleton, smul_eq_mul]
      exact boolToZMod_eq_pm p hp2 (x i)
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (one_mem_pmSpan p n)
      (pmEvalMonomial_mem_pmSpan p n {i}))
  · have he : (fun x : Fin n → Bool => if y i then boolToZMod p (x i) else 1 - boolToZMod p (x i))
        = (2 : ZMod p)⁻¹ • ((1 : (Fin n → Bool) → ZMod p) + pmEvalMonomial p ({i} : Finset (Fin n))) := by
      funext x
      simp only [hyi, if_false, Pi.smul_apply, Pi.add_apply, Pi.one_apply, pmEvalMonomial,
        Finset.prod_singleton, smul_eq_mul]
      exact one_sub_boolToZMod_eq_pm p hp2 (x i)
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _ (one_mem_pmSpan p n)
      (pmEvalMonomial_mem_pmSpan p n {i}))

/-- **The `±1` multilinear basis.**  For `p` odd, the `±1` monomials `χ_S` span the entire
cube-function space `(Fin n → Bool) → ZMod p`.  Hence *every* function — in particular every function
on the agreement set `G` — is a `ZMod p`-linear combination of `χ_S`, ready for the degree-halving
`pm_monomial_reduction`. -/
theorem pmSpan_eq_top (p n : ℕ) [Fact p.Prime] (hp2 : (2 : ZMod p) ≠ 0) : pmSpan p n = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun (ZMod p) (Fin n → Bool)).span_eq, Submodule.span_le]
  rintro _ ⟨y, rfl⟩
  rw [Pi.basisFun_apply, single_eq_prod_factor]
  exact prod_mem_pmSpan p n _ _ (fun i _ => factor_mem_pmSpan p n hp2 y i)

/-- Every function on the cube is a `ZMod p`-linear combination of `±1` monomials (`p` odd). -/
theorem mem_pmSpan (p n : ℕ) [Fact p.Prime] (hp2 : (2 : ZMod p) ≠ 0) (f : (Fin n → Bool) → ZMod p) :
    f ∈ pmSpan p n := by rw [pmSpan_eq_top p n hp2]; exact Submodule.mem_top

open MvPolynomial in
/-- **Uniform per-monomial representative.**  Given a degree-`Δ` approximant `g` for `χ_univ` on `G`,
*every* `±1` monomial `χ_S` agrees on `G` with a polynomial of degree `≤ Δ + n/2`: for `|S| ≤ n/2` use
`χ_S` itself (degree `≤ |S| ≤ n/2`), for `|S| > n/2` use the degree-halving `pm_monomial_reduction`
(`g · χ_{Sᶜ}`, degree `≤ Δ + (n-|S|) ≤ Δ + n/2`). -/
theorem pm_monomial_repr (p : ℕ) [Fact p.Prime] {n : ℕ} (G : Finset (Fin n → Bool)) (Δ : ℕ)
    (g : MvPolynomial (Fin n) (ZMod p)) (hgdeg : g.totalDegree ≤ Δ)
    (hg : ∀ x ∈ G, eval (fun i => boolToZMod p (x i)) g = ∏ i, pmOne p (x i)) (S : Finset (Fin n)) :
    ∃ h : MvPolynomial (Fin n) (ZMod p), h.totalDegree ≤ Δ + n / 2 ∧
      ∀ x ∈ G, eval (fun i => boolToZMod p (x i)) h = pmEvalMonomial p S x := by
  by_cases hS : S.card ≤ n / 2
  · exact ⟨pmMonomial p S, le_trans (pmMonomial_totalDegree_le p S) (by omega),
      fun x _ => by rw [pmEvalMonomial]; exact pmMonomial_eval p S x⟩
  · obtain ⟨h, hdeg, heval⟩ := pm_monomial_reduction p G Δ g hgdeg hg S
    exact ⟨h, le_trans hdeg (by omega), fun x hx => by rw [pmEvalMonomial]; exact heval x hx⟩

open MvPolynomial in
/-- **The Smolensky dimension collapse.**  Given a degree-`Δ` approximant `g` for the full `±1` product
`χ_univ` on `G` (the `MOD_q ∈ AC⁰[p]` consequence), *every* function `f : (Fin n → Bool) → ZMod p`
agrees on `G` with a polynomial of degree `≤ Δ + n/2`.  (Expand `f = ∑_S c_S χ_S` via the multilinear
basis `mem_pmSpan`, then apply `pm_monomial_repr` termwise; degrees are preserved under `+`/`•`.)  So the
space of functions on `G` is spanned by degree-`≤(Δ+n/2)` evaluations — the dimension bound that, with
the band margin and the agreement lower bound `|G| ≥ (3/4)·2ⁿ`, yields the contradiction. -/
theorem every_function_repr (p : ℕ) [Fact p.Prime] {n : ℕ} (hp2 : (2 : ZMod p) ≠ 0)
    (G : Finset (Fin n → Bool)) (Δ : ℕ) (g : MvPolynomial (Fin n) (ZMod p))
    (hgdeg : g.totalDegree ≤ Δ)
    (hg : ∀ x ∈ G, eval (fun i => boolToZMod p (x i)) g = ∏ i, pmOne p (x i))
    (f : (Fin n → Bool) → ZMod p) :
    ∃ h : MvPolynomial (Fin n) (ZMod p), h.totalDegree ≤ Δ + n / 2 ∧
      ∀ x ∈ G, eval (fun i => boolToZMod p (x i)) h = f x := by
  have hf : f ∈ pmSpan p n := mem_pmSpan p n hp2 f
  refine Submodule.span_induction (p := fun u _ => ∃ h : MvPolynomial (Fin n) (ZMod p),
      h.totalDegree ≤ Δ + n / 2 ∧ ∀ x ∈ G, eval (fun i => boolToZMod p (x i)) h = u x)
    ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨S, rfl⟩; exact pm_monomial_repr p G Δ g hgdeg hg S
  · exact ⟨0, by simp, fun x _ => by simp⟩
  · rintro u v _ _ ⟨hu, hud, hue⟩ ⟨hv, hvd, hve⟩
    exact ⟨hu + hv, le_trans (totalDegree_add _ _) (max_le hud hvd),
      fun x hx => by rw [map_add, hue x hx, hve x hx]; rfl⟩
  · rintro c u _ ⟨hu, hud, hue⟩
    exact ⟨c • hu, le_trans (totalDegree_smul_le c hu) hud,
      fun x hx => by rw [MvPolynomial.smul_eq_C_mul, map_mul, eval_C, hue x hx, Pi.smul_apply,
        smul_eq_mul]⟩

/-- **The `|G|` side of the dimension contradiction.**  The `ZMod p`-vector space of functions on the
agreement set `G` has dimension exactly `|G|` (`finrank` of a function space = size of the domain).
With `every_function_repr` (that space is spanned by degree-`≤(Δ+n/2)` evaluations) this is the
inequality `|G| ≤ #{deg≤(Δ+n/2) monomials}` once the squarefree-reduction spanning bridge is in place —
which, against the band margin `#{…} < (3/4)·2ⁿ` and the agreement bound `|G| ≥ (3/4)·2ⁿ`, is the
contradiction. -/
theorem finrank_functions_on_G (p : ℕ) [Fact p.Prime] {n : ℕ} (G : Finset (Fin n → Bool)) :
    Module.finrank (ZMod p) ({x // x ∈ G} → ZMod p) = G.card := by
  rw [Module.finrank_pi, Fintype.card_coe]

/-! ## Union bound: the agreement set from per-gate errors

Smolensky's composition replaces each of the `s` gates of an `AC⁰[p]` circuit by a probabilistic
low-degree approximant that errs on a `bad` set of inputs; the single composed polynomial errs only
where *some* gate does — on `⋃ gate-bad-sets`.  The **union bound** controls this: if each gate errs on
`≤ δ` inputs, the agreement set `G` (where the composed polynomial matches the circuit) has
`|G| ≥ 2^n - s·δ`, and once `4·s·δ ≤ 2^n` this gives `|G| ≥ (3/4)·2^n` — exactly the lower bound the
dimension contradiction consumes (`lowDegEval_span_ne_top` / the count `< 2^n`).

This is the *counting core* of the composition.  The per-gate approximants (`orApprox` etc.) and the
depth-`d` degree bookkeeping `((p-1)t)^d`, and the `MOD_q`-specific degree-reduction that uses the
approximant on `G`, are the surrounding pieces (still open). -/

/-- **Union bound (counting).**  The union of `s` "bad" sets has at most `∑ card` elements. -/
theorem badUnion_card_le {n s : ℕ} (B : Fin s → Finset (Fin n → Bool)) :
    (Finset.univ.biUnion B).card ≤ ∑ i, (B i).card := by
  classical exact Finset.card_biUnion_le

/-- **Agreement-set lower bound.**  If each of `s` bad sets has `≤ δ` elements, the agreement set
(complement of their union in the cube) has `≥ 2^n - s·δ` elements. -/
theorem agreement_card_ge {n s : ℕ} (B : Fin s → Finset (Fin n → Bool)) (δ : ℕ)
    (hB : ∀ i, (B i).card ≤ δ) :
    2 ^ n - s * δ ≤ ((Finset.univ : Finset (Fin n → Bool)) \ Finset.univ.biUnion B).card := by
  classical
  have hcube : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have hunion : (Finset.univ.biUnion B).card ≤ s * δ := by
    refine le_trans Finset.card_biUnion_le ?_
    refine le_trans (Finset.sum_le_sum (fun i _ => hB i)) ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), hcube]
  omega

/-- **`(3/4)·2^n` agreement (integer form).**  If `4·s·δ ≤ 2^n` then `3·2^n ≤ 4·|G|`, i.e. the agreement
set occupies at least three quarters of the cube — the precise input to the Smolensky contradiction. -/
theorem agreement_card_ge_three_quarters {n s : ℕ} (B : Fin s → Finset (Fin n → Bool)) (δ : ℕ)
    (hB : ∀ i, (B i).card ≤ δ) (hsδ : 4 * (s * δ) ≤ 2 ^ n) :
    3 * 2 ^ n ≤ 4 * ((Finset.univ : Finset (Fin n → Bool)) \ Finset.univ.biUnion B).card := by
  have h := agreement_card_ge B δ hB
  omega

end PallLean.Paper93.DeepMath.PathB.Layer3

#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.lowDegMonomials_card
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.lowDegMonomials_card_full
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.lowDegMonomials_card_le_two_pow
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.lowDegMonomials_card_lt_two_pow
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.lowDegMonomials_card_halfway
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.lowDegMonomials_card_halfway_margin
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.centralBinom_sq_le
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.lowDegMonomials_card_band_margin
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.pm_monomial_halving
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.pm_monomial_mul
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.pmSpan_eq_top
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.mem_pmSpan
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.pm_monomial_repr
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.every_function_repr
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.finrank_functions_on_G
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.pmMonomial_totalDegree_le
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.pmMonomial_eval
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.pm_monomial_reduction
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.boolToZMod_pow_succ
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.squarefreeEvalMonomial_mem_span
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.finrank_span_lowDegEval_le_card
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.finrank_span_lowDegEval_le_sum
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.finrank_cubeFunctions_eq
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.lowDegEval_span_ne_top
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.exists_cubeFunction_not_lowDegEval
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.squarefreeEvalMonomial_empty
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.squarefreeEvalMonomial_mul
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.squarefreeEvalMonomial_mul_card_le
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.mul_mem_squarefreeSpan
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.single_eq_prod_factor
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.squarefreeSpan_eq_top
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.mem_squarefreeSpan
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.agreement_card_ge
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.agreement_card_ge_three_quarters
