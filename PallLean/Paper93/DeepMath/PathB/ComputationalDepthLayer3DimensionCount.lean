import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3AC0pFoundations
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

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

end PallLean.Paper93.DeepMath.PathB.Layer3

#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.lowDegMonomials_card
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.lowDegMonomials_card_full
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.lowDegMonomials_card_le_two_pow
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.lowDegMonomials_card_lt_two_pow
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.lowDegMonomials_card_halfway
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
