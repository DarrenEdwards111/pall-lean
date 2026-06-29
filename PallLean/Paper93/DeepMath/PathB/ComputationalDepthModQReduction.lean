import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMultilinear
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTriangularInv
import Mathlib

/-!
# The `MOD_q` reduction — algebraic heart (PROVED); the `q`-ary generalization fenced

`no_parity_circuit` (`ComputationalDepthRSHardnessSkeleton`) closes the `q = 2` (parity) Razborov–Smolensky lower
bound unconditionally.  The general `MOD_q` case (`q ≠ 2`, `q` coprime to `p`) is **also a real theorem**
(Smolensky 1987) — *not* a natural-proofs barrier (that barrier concerns P/poly, far above AC⁰[p]).  What it needs
is the **`q`-ary generalization** of the whole `q = 2` argument: replace the `{−1,+1}` alphabet (`walshFn`,
boosting, dimension) by the `q`-th roots of unity `{1, ω, …, ω^{q-1}}` in a field extension `𝔽_{p^ℓ}` (with
`q ∣ p^ℓ − 1`).

This file proves the **algebraic heart** of that reduction — the part that makes `MOD_q` look like a *full product*,
exactly as parity is `∏(-1)^{xᵢ}`:

  `rootsOfUnity_filter` — for a primitive `q`-th root `ω`, the geometric/Fourier filter
        `Σ_{j<q} ω^{j·a} = q·[q ∣ a]`.
  `modq_indicator_eq` — the `MOD_q` indicator is a Fourier combination of the `q`-ary **full product**
        `∏ᵢ ω^{xᵢ}`:  `q·[q ∣ Σxᵢ] = Σ_{j<q} (∏ᵢ ω^{xᵢ})^j`.  (At `q = 2`, `ω = −1`, this is
        `2·[2 ∣ Σxᵢ] = 1 + ∏(-1)^{xᵢ} = 1 + walshFn univ`, the `q = 2` packaging.)

So `MOD_q` is, up to the field-`q`-ary Fourier transform, the full product `∏ᵢ ω^{xᵢ}` — the object the boosting /
dimension argument bounds.  **What remains (honestly fenced, a real undertaking, not faked):** generalize the
boosting surjection, the Walsh span, and the dimension argument from the binary cube to the `q`-ary cube over
`𝔽_{p^ℓ}`, and instantiate `ω` via a concrete extension with `q ∣ p^ℓ − 1`.  That re-does, `q`-ary, what the
`q = 2` files prove.  It is **not** done here; this file is the algebraic bridge only.
-/

namespace PallLean.Paper93.DeepMath.PathB.ModQReduction

open Finset

/-- **Roots-of-unity filter.**  For a primitive `q`-th root of unity `ω` (`orderOf ω = q`) in a field,
`Σ_{j<q} ω^{j·a} = q` if `q ∣ a` and `0` otherwise — the geometric sum is `q` when `ω^a = 1` and collapses
(telescopes to `0`) otherwise, since `(ω^a)^q = 1`.  The `q`-ary analogue of `[2 ∣ a] = (1 + (-1)^a)/2`. -/
theorem rootsOfUnity_filter {F : Type*} [Field F] {q : ℕ} {ω : F} (hω : orderOf ω = q) (a : ℕ) :
    ∑ j ∈ Finset.range q, ω ^ (j * a) = if q ∣ a then (q : F) else 0 := by
  have hpow : ∀ j, ω ^ (j * a) = (ω ^ a) ^ j := fun j => by rw [mul_comm, pow_mul]
  simp_rw [hpow]
  have hqa : (ω ^ a) ^ q = 1 := by
    rw [← pow_mul, mul_comm a q, pow_mul, ← hω, pow_orderOf_eq_one, one_pow]
  by_cases hdvd : q ∣ a
  · rw [if_pos hdvd]
    have h1 : ω ^ a = 1 := orderOf_dvd_iff_pow_eq_one.mp (hω.symm ▸ hdvd)
    rw [h1]; simp
  · rw [if_neg hdvd]
    have h1 : ω ^ a ≠ 1 := fun h => hdvd (hω ▸ orderOf_dvd_iff_pow_eq_one.mpr h)
    rw [geom_sum_eq h1, hqa]; simp

/-- **`MOD_q` as a Fourier combination of the `q`-ary full product.**  `q·[q ∣ Σxᵢ] = Σ_{j<q} (∏ᵢ ω^{xᵢ})^j`:
the `MOD_q` indicator on the number of `true` bits is a fixed linear combination of powers of the full product
`∏ᵢ ω^{xᵢ}`.  This is the `q`-ary `walshFn_univ_eq` — it makes `MOD_q` a function of the full product, which the
(yet-to-be-generalized) `q`-ary boosting/dimension argument bounds. -/
theorem modq_indicator_eq {F : Type*} [Field F] {n q : ℕ} {ω : F} (hω : orderOf ω = q) (x : Fin n → Bool) :
    (if q ∣ (∑ i, (x i).toNat) then (q : F) else 0)
      = ∑ j ∈ Finset.range q, (∏ i, ω ^ (x i).toNat) ^ j := by
  rw [← rootsOfUnity_filter hω (∑ i, (x i).toNat)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.prod_pow_eq_pow_sum, ← pow_mul, Nat.mul_comm]

/-- **The `q`-ary change-of-basis bridge (first step of the `q`-ary Walsh generalization).**  A `q`-ary character
`∏_{i∈S} ω^{bᵢ}` (each bit valued in `{1, ω}`) is a triangular combination of `{0,1}` multilinear monomials:
`∏_{i∈S} ω^{bᵢ} = Σ_{T⊆S} (ω−1)^{|T|} · monomialFn T b`, via `ω^{bᵢ} = (ω−1)·bᵢ + 1` for `bᵢ ∈ {0,1}`.  This is the
exact `q`-ary analogue of `RepUnify.walshFn_eq_sum_mono0` (which is the `ω = −1` case, `ω−1 = −2`).  The diagonal
term (`T = S`) is `(ω−1)^{|S|}`, so the change of basis is invertible whenever `ω ≠ 1` (any primitive `q`-th root,
`q ≥ 2`) — so it transfers the existing `Multilinear.eval_surjective` span to the `q`-ary characters, the foundation
the `q`-ary boosting/dimension argument needs.  (The folding, span transfer, and dimension count over `𝔽_{p^ℓ}`
remain to be generalized.) -/
theorem omegaProd_eq_sum_mono {F : Type*} [CommRing F] {n : ℕ} (ω : F) (b : Fin n → Bool)
    (S : Finset (Fin n)) :
    (∏ i ∈ S, (if b i then ω else 1))
      = ∑ T ∈ S.powerset, (ω - 1) ^ T.card * Multilinear.monomialFn T b := by
  have hterm : ∀ i, (if b i then ω else 1) = (ω - 1) * (if b i then (1 : F) else 0) + 1 := by
    intro i; cases b i <;> simp
  simp_rw [hterm]
  rw [Finset.prod_add]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  rw [Finset.prod_const_one, mul_one, Finset.prod_mul_distrib, Finset.prod_const, Multilinear.monomialFn]

/-! ### Multilinear products on the cube (the foundation the `q`-ary collection needs). -/

/-- **The multilinear product law.**  On the `{0,1}` cube a coordinate is idempotent, so the pointwise product of
two multilinear monomials is again a monomial: `monomialFn S · monomialFn T = monomialFn (S ∪ T)`.  Hence the
product has degree `|S ∪ T| ≤ |S| + |T|` — the bound that lets the `q`-ary boosting collection (where the character
product is *not* a clean character shift, unlike the binary Walsh case) stay low degree. -/
theorem monomialFn_mul {F : Type*} [CommRing F] {n : ℕ} (S T : Finset (Fin n)) (x : Fin n → Bool) :
    Multilinear.monomialFn (F := F) S x * Multilinear.monomialFn T x
      = Multilinear.monomialFn (S ∪ T) x := by
  simp only [Multilinear.monomialFn]
  rw [Finset.prod_boole, Finset.prod_boole, Finset.prod_boole]
  by_cases hS : ∀ i ∈ S, x i = true
  · by_cases hT : ∀ i ∈ T, x i = true
    · rw [if_pos hS, if_pos hT, if_pos (Finset.forall_mem_union.mpr ⟨hS, hT⟩), mul_one]
    · rw [if_pos hS, if_neg hT, if_neg (fun h => hT (Finset.forall_mem_union.mp h).2), mul_zero]
  · rw [if_neg hS, if_neg (fun h => hS (Finset.forall_mem_union.mp h).1), zero_mul]

/-- The multilinear convolution: `(mlConv c c') U` collects `c S · c' T` over all pairs with `S ∪ T = U` — the
coefficients of the pointwise product `eval c · eval c'`. -/
noncomputable def mlConv {F : Type*} [CommRing F] {n : ℕ} (c c' : Finset (Fin n) → F) :
    Finset (Fin n) → F :=
  fun U => ∑ p ∈ (Finset.univ ×ˢ Finset.univ : Finset (Finset (Fin n) × Finset (Fin n))).filter
    (fun p => p.1 ∪ p.2 = U), c p.1 * c' p.2

/-- **The product of multilinear evaluations is a multilinear evaluation.**  `eval c · eval c' = eval (mlConv c c')`
on the cube: expand the product, collapse each `monomialFn S · monomialFn T` to `monomialFn (S ∪ T)`
(`monomialFn_mul`), and group the pairs by their union. -/
theorem eval_mul {F : Type*} [CommRing F] {n : ℕ} (c c' : Finset (Fin n) → F) (x : Fin n → Bool) :
    Multilinear.eval c x * Multilinear.eval c' x = Multilinear.eval (mlConv c c') x := by
  have hterm : ∀ S T : Finset (Fin n),
      (c S * Multilinear.monomialFn (F := F) S x) * (c' T * Multilinear.monomialFn T x)
        = (c S * c' T) * Multilinear.monomialFn (S ∪ T) x :=
    fun S T => by rw [← monomialFn_mul]; ring
  rw [Multilinear.eval, Multilinear.eval, Finset.sum_mul_sum]
  simp_rw [hterm]
  rw [← Finset.sum_product']
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun p : Finset (Fin n) × Finset (Fin n) => p.1 ∪ p.2)
    (t := Finset.univ) (fun p _ => Finset.mem_univ _)]
  rw [Multilinear.eval]
  refine Finset.sum_congr rfl (fun U _ => ?_)
  rw [mlConv, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [Finset.mem_filter] at hp
  rw [hp.2]

/-- **The product is degree-additive.**  If `c` is supported on `|S| ≤ a` and `c'` on `|T| ≤ b`, then `mlConv c c'`
is supported on `|U| ≤ a + b`: any pair with `S ∪ T = U` and both coefficients nonzero has
`|U| = |S ∪ T| ≤ |S| + |T| ≤ a + b`.  So the product of a degree-`a` and a degree-`b` multilinear polynomial has
degree `≤ a + b` — the bound the `q`-ary collection needs. -/
theorem mlConv_support {F : Type*} [CommRing F] {n a b : ℕ} (c c' : Finset (Fin n) → F)
    (hc : ∀ S, a < S.card → c S = 0) (hc' : ∀ T, b < T.card → c' T = 0)
    (U : Finset (Fin n)) (hU : a + b < U.card) : mlConv c c' U = 0 := by
  rw [mlConv]
  refine Finset.sum_eq_zero (fun p hp => ?_)
  rw [Finset.mem_filter] at hp
  by_cases h1 : a < p.1.card
  · rw [hc p.1 h1, zero_mul]
  · have hcard : U.card ≤ p.1.card + p.2.card := by
      rw [← hp.2]; exact Finset.card_union_le p.1 p.2
    rw [hc' p.2 (by omega), mul_zero]

/-! ### The `q`-ary character span (the analogue of `WalshSpan.evalW_surjective`). -/

variable {F : Type*} [Field F] {n : ℕ}

/-- The `q`-ary character `∏_{i∈S} ω^{bᵢ}` (each bit valued in `{1, ω}`). -/
noncomputable def omegaFn (ω : F) (S : Finset (Fin n)) (b : Fin n → Bool) : F :=
  ∏ i ∈ S, (if b i then ω else 1)

/-- Evaluate the `q`-ary character polynomial with coefficient vector `c`. -/
noncomputable def evalΩ (ω : F) (c : Finset (Fin n) → F) (b : Fin n → Bool) : F :=
  ∑ S, c S * omegaFn ω S b

/-- The triangular change-of-basis transform: `(Mω c) T = (ω−1)^{|T|} · Σ_{S ⊇ T} c S`. -/
noncomputable def Mω (ω : F) (c : Finset (Fin n) → F) : Finset (Fin n) → F :=
  fun T => (ω - 1) ^ T.card * ∑ S ∈ Finset.univ.filter (fun S => T ⊆ S), c S

/-- **The `q`-ary evaluation factors through the `{0,1}` one.**  `evalΩ ω c = eval0 (Mω ω c)` — substitute
`omegaProd_eq_sum_mono` into each character and swap the order of summation (Fubini over `T ⊆ S`).  The exact
`q`-ary mirror of `WalshSpan.evalW_eq_eval0_M`. -/
theorem evalΩ_eq_eval0_M (ω : F) (c : Finset (Fin n) → F) (b : Fin n → Bool) :
    evalΩ ω c b = Multilinear.eval (Mω ω c) b := by
  rw [evalΩ]
  simp_rw [omegaFn, omegaProd_eq_sum_mono, Finset.mul_sum]
  rw [Finset.sum_comm' (t' := Finset.univ)
      (s' := fun T => Finset.univ.filter (fun S => T ⊆ S))
      (by intro S T; simp [Finset.mem_powerset, Finset.mem_filter])]
  rw [Multilinear.eval]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  rw [Mω, ← Finset.sum_mul]
  ring

/-- **`Mω` is injective** when `ω ≠ 1`: the scalar `(ω−1)^{|T|}` cancels, leaving all upset sums of `c − c'` zero,
and `superset_sum_eq_zero` gives `c = c'`.  (`ω ≠ 1` holds for any primitive `q`-th root, `q ≥ 2`.) -/
theorem Mω_injective (ω : F) (hω : ω ≠ 1) : Function.Injective (Mω ω (n := n)) := by
  intro c c' hM
  have hsup : ∀ T : Finset (Fin n),
      ∑ S ∈ Finset.univ.filter (fun S => T ⊆ S), (c S - c' S) = 0 := by
    intro T
    have hT : Mω ω c T = Mω ω c' T := congrFun hM T
    simp only [Mω] at hT
    have hne : (ω - 1) ^ T.card ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hω)
    have heq := mul_left_cancel₀ hne hT
    rw [Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr heq
  funext S
  exact sub_eq_zero.mp (TriangularInv.superset_sum_eq_zero (fun S => c S - c' S) hsup S)

/-- **`Mω` is degree-preserving.**  If `aCoef` is supported on `|S| ≤ d`, so is `Mω ω aCoef`: for `|T| > d` every
superset `S ⊇ T` has `|S| ≥ |T| > d`, so the upset sum is zero.  (So the approximator's transform stays degree-`d`,
the input to the high-character degree drop.) -/
theorem Mω_support {d : ℕ} (ω : F) (aCoef : Finset (Fin n) → F)
    (hd : ∀ S, d < S.card → aCoef S = 0) (T : Finset (Fin n)) (hT : d < T.card) :
    Mω ω aCoef T = 0 := by
  rw [Mω]
  have hz : (∑ S ∈ Finset.univ.filter (fun S => T ⊆ S), aCoef S) = 0 := by
    refine Finset.sum_eq_zero (fun S hS => ?_)
    rw [Finset.mem_filter] at hS
    exact hd S (lt_of_lt_of_le hT (Finset.card_le_card hS.2))
  rw [hz, mul_zero]

/-- **`evalΩ` is injective** (`ω ≠ 1`): factor through `eval0 ∘ Mω` and compose the two injectivities. -/
theorem evalΩ_injective (ω : F) (hω : ω ≠ 1) : Function.Injective (evalΩ ω (n := n)) := by
  intro c c' h
  apply Mω_injective ω hω
  apply Multilinear.eval_injective
  funext b
  rw [← evalΩ_eq_eval0_M ω c b, ← evalΩ_eq_eval0_M ω c' b]
  exact congrFun h b

/-- **The `q`-ary character span.**  For `ω ≠ 1`, `evalΩ ω` is surjective (indeed bijective): every function on the
`{0,1}` cube is a `q`-ary character polynomial.  The `q`-ary analogue of `WalshSpan.evalW_surjective` — the span
foundation the `q`-ary boosting/dimension argument consumes. -/
theorem evalΩ_surjective [Fintype F] [DecidableEq F] (ω : F) (hω : ω ≠ 1) :
    Function.Surjective (evalΩ ω (n := n)) := by
  have hcard : Fintype.card (Finset (Fin n) → F) = Fintype.card ((Fin n → Bool) → F) := by
    simp [Fintype.card_finset, Fintype.card_bool]
  exact ((Fintype.bijective_iff_injective_and_card (evalΩ ω)).mpr
    ⟨evalΩ_injective ω hω, hcard⟩).surjective

/-- **The `q`-ary folding identity (the structurally novel step).**  Where the binary boosting folds a high-degree
monomial using `xᵢ² = 1` (`∏_S = (∏ all)·∏_{Sᶜ}`), the `q`-ary case uses `ω^q = 1`: a character `omegaFn ω S`
equals the *full product* `omegaFn ω univ` times the **complementary character in `ω^{q-1}` (`= ω⁻¹`)**,
`omegaFn (ω^{q-1}) Sᶜ` — because on `Sᶜ` the two factors multiply coordinatewise to `ω^q = 1`.  For `|S| > n/2` the
complement `Sᶜ` has degree `n−|S| < n/2`, so replacing the full product by its degree-`d` approximator drops a
degree-`|S|` character to degree `d + (n−|S|) < d + n/2` — the `q`-ary boosting handle. -/
theorem omegaFn_fold (ω : F) {q : ℕ} (hq1 : 1 ≤ q) (hq : ω ^ q = 1) (S : Finset (Fin n)) (b : Fin n → Bool) :
    omegaFn ω S b = omegaFn ω Finset.univ b * omegaFn (ω ^ (q - 1)) Sᶜ b := by
  have hone : (∏ i ∈ Sᶜ, ((if b i then ω else 1) * (if b i then ω ^ (q - 1) else 1))) = 1 := by
    refine Finset.prod_eq_one (fun i _ => ?_)
    cases b i
    · simp
    · simp only [if_true]
      rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hq1]; exact hq
  simp only [omegaFn]
  rw [← Finset.prod_mul_prod_compl S (fun i => if b i then ω else 1), mul_assoc,
    ← Finset.prod_mul_distrib, hone, mul_one]

/-- **A `q`-ary character is a multilinear polynomial of its own degree.**  `omegaFn ω S = Multilinear.eval c`
with `c T = (ω−1)^{|T|}` for `T ⊆ S` and `0` otherwise — directly from `omegaProd_eq_sum_mono`.  The coefficients
are supported on `T ⊆ S`, hence on `|T| ≤ |S|`: a `|S|`-degree multilinear polynomial.  (Used for the low-degree
characters `|S| ≤ n/2` in the collection.) -/
theorem omegaFn_eq_eval (ω : F) (S : Finset (Fin n)) (b : Fin n → Bool) :
    omegaFn ω S b = Multilinear.eval (fun T => if T ⊆ S then (ω - 1) ^ T.card else 0) b := by
  rw [omegaFn, omegaProd_eq_sum_mono, Multilinear.eval]
  have hzero : ∀ T ∈ (Finset.univ : Finset (Finset (Fin n))), T ∉ S.powerset →
      (if T ⊆ S then (ω - 1) ^ T.card else 0) * Multilinear.monomialFn T b = 0 := by
    intro T _ hT
    rw [Finset.mem_powerset] at hT
    rw [if_neg hT, zero_mul]
  rw [← Finset.sum_subset (Finset.subset_univ S.powerset) hzero]
  refine Finset.sum_congr rfl (fun T hT => ?_)
  rw [Finset.mem_powerset] at hT
  rw [if_pos hT]

/-- **The fold on the agreement set (first step of the `q`-ary boosting collection).**  At a point `b` where the
degree-`d` approximator `aCoef` agrees with the full product (`evalΩ ω aCoef b = omegaFn ω univ b`), *every*
character folds as `omegaFn ω S b = (evalΩ ω aCoef b) · omegaFn (ω^{q-1}) Sᶜ b` — the full product replaced by its
approximator.  For `|S| > n/2` the right side has degree `≤ d + (n−|S|) < d + n/2`, so on the agreement set every
character is low degree.  The `q`-ary analogue of `WalshSpan.evalW_fold_on_G`. -/
theorem omegaFn_fold_on_G (ω : F) {q : ℕ} (hq1 : 1 ≤ q) (hq : ω ^ q = 1)
    (aCoef : Finset (Fin n) → F) (b : Fin n → Bool)
    (hb : evalΩ ω aCoef b = omegaFn ω Finset.univ b) (S : Finset (Fin n)) :
    omegaFn ω S b = evalΩ ω aCoef b * omegaFn (ω ^ (q - 1)) Sᶜ b := by
  rw [omegaFn_fold ω hq1 hq, ← hb]

/-- **The high-character degree drop (the heart of the `q`-ary collection).**  On the agreement set, a *high*-degree
character `omegaFn ω S` (`|S| > n/2`) equals a multilinear polynomial `Multilinear.eval (mlConv (Mω ω aCoef) …)`:
the fold (`omegaFn_fold_on_G`) replaces the full product by the degree-`d` approximator (`evalΩ_eq_eval0_M`), the
complementary character is degree-`|Sᶜ|` (`omegaFn_eq_eval`), and their product is multilinear (`eval_mul`).  By
`Mω_support` + `mlConv_support` the result has degree `≤ d + |Sᶜ| = d + (n − |S|) < d + n/2` — every character is a
degree-`≤ n/2 + d` multilinear polynomial on `G`, exactly what the dimension argument consumes. -/
theorem omegaFn_high_eq_eval_on_G (ω : F) {q : ℕ} (hq1 : 1 ≤ q) (hq : ω ^ q = 1)
    (aCoef : Finset (Fin n) → F) (b : Fin n → Bool)
    (hb : evalΩ ω aCoef b = omegaFn ω Finset.univ b) (S : Finset (Fin n)) :
    omegaFn ω S b = Multilinear.eval
      (mlConv (Mω ω aCoef) (fun T => if T ⊆ Sᶜ then (ω ^ (q - 1) - 1) ^ T.card else 0)) b := by
  rw [omegaFn_fold_on_G ω hq1 hq aCoef b hb S, evalΩ_eq_eval0_M, omegaFn_eq_eval, eval_mul]

end PallLean.Paper93.DeepMath.PathB.ModQReduction

#print axioms PallLean.Paper93.DeepMath.PathB.ModQReduction.omegaFn_fold_on_G
#print axioms PallLean.Paper93.DeepMath.PathB.ModQReduction.omegaFn_fold
#print axioms PallLean.Paper93.DeepMath.PathB.ModQReduction.evalΩ_eq_eval0_M
#print axioms PallLean.Paper93.DeepMath.PathB.ModQReduction.evalΩ_surjective
#print axioms PallLean.Paper93.DeepMath.PathB.ModQReduction.omegaProd_eq_sum_mono
#print axioms PallLean.Paper93.DeepMath.PathB.ModQReduction.rootsOfUnity_filter
#print axioms PallLean.Paper93.DeepMath.PathB.ModQReduction.modq_indicator_eq
