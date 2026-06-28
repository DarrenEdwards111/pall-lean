import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMultilinear
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRepUnify
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTriangularInv
import Mathlib

/-!
# The `{-1,+1}` multilinear (Walsh) span (PROVED) — M-injectivity assembly

This completes the representation-unification: **every function on `{-1,+1}ⁿ` is a Walsh polynomial**, over a
field with `2 ≠ 0` (`char 𝔽 ≠ 2`).  It assembles the proved pieces:

* the change-of-basis bridge (`RepUnify.walshFn_eq_sum_mono0`),
* the `{0,1}` multilinear span (`Multilinear.eval_injective` / `eval_surjective`),
* the downward Möbius inversion (`TriangularInv.superset_sum_eq_zero`).

  `evalW_eq_eval0_M` — the Walsh evaluation factors through the `{0,1}` one: `evalW c = eval0 (M c)`, where
        `(M c) T = (-2)^{|T|} · Σ_{S ⊇ T} c S` (the triangular change-of-basis transform, via Fubini over `⊆`).
  `M_injective` — `M` is injective: `M c = 0` forces every upset sum to vanish (cancelling `(-2)^{|T|} ≠ 0`),
        hence `c = 0` by `superset_sum_eq_zero`.
  `evalW_injective` / `evalW_surjective` — therefore `evalW` is injective, and (by the cardinality count)
        **surjective**: the `{-1,+1}` monomials span every function on the cube.

So the folding/product-law cube `{-1,+1}` now carries a full multilinear span, matching the `{0,1}` one — the
representation gap is closed for the boosting surjection.
-/

open scoped BigOperators

namespace PallLean.Paper93.DeepMath.PathB.WalshSpan

variable {n : ℕ} {F : Type*} [Field F]

/-- The `{-1,+1}` monomial `∏_{i∈S} (-1)^{bᵢ}`. -/
noncomputable def walshFn (S : Finset (Fin n)) (b : Fin n → Bool) : F :=
  ∏ i ∈ S, (if b i then (-1 : F) else 1)

/-- Evaluate the Walsh polynomial with coefficient vector `c` at a `{-1,+1}` point. -/
noncomputable def evalW (c : Finset (Fin n) → F) (b : Fin n → Bool) : F := ∑ S, c S * walshFn S b

/-- The triangular change-of-basis transform: `(M c) T = (-2)^{|T|} · Σ_{S ⊇ T} c S`. -/
noncomputable def M (c : Finset (Fin n) → F) : Finset (Fin n) → F :=
  fun T => (-2) ^ T.card * ∑ S ∈ Finset.univ.filter (fun S => T ⊆ S), c S

/-- **The Walsh evaluation factors through the `{0,1}` one.**  `evalW c = eval0 (M c)`: substitute the
change-of-basis bridge into each monomial and swap the order of summation (Fubini over `T ⊆ S`). -/
theorem evalW_eq_eval0_M (c : Finset (Fin n) → F) (b : Fin n → Bool) :
    evalW c b = Multilinear.eval (M c) b := by
  rw [evalW]
  simp_rw [walshFn, RepUnify.walshFn_eq_sum_mono0, Finset.mul_sum]
  rw [Finset.sum_comm' (t' := Finset.univ)
      (s' := fun T => Finset.univ.filter (fun S => T ⊆ S))
      (by intro S T; simp [Finset.mem_powerset, Finset.mem_filter])]
  rw [Multilinear.eval]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  rw [M, ← Finset.sum_mul]
  ring

/-- **`M` is injective.**  If `M c = M c'`, then for every `T` the scalars `(-2)^{|T|}` cancel (`2 ≠ 0`), leaving
all upset sums of `c - c'` zero; `superset_sum_eq_zero` then gives `c = c'`. -/
theorem M_injective (h2 : (2 : F) ≠ 0) : Function.Injective (M (n := n) (F := F)) := by
  intro c c' hM
  have hsup : ∀ T : Finset (Fin n),
      ∑ S ∈ Finset.univ.filter (fun S => T ⊆ S), (c S - c' S) = 0 := by
    intro T
    have hT : M c T = M c' T := congrFun hM T
    simp only [M] at hT
    have hne : (-2 : F) ^ T.card ≠ 0 := by
      apply pow_ne_zero
      rw [neg_ne_zero]
      exact h2
    have heq := mul_left_cancel₀ hne hT
    rw [Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr heq
  funext S
  exact sub_eq_zero.mp (TriangularInv.superset_sum_eq_zero (fun S => c S - c' S) hsup S)

/-- **`evalW` is injective.**  `evalW c = evalW c'` gives `eval0 (M c) = eval0 (M c')` (factoring), so `M c = M c'`
(`eval0` injective), so `c = c'` (`M` injective). -/
theorem evalW_injective (h2 : (2 : F) ≠ 0) : Function.Injective (evalW (n := n) (F := F)) := by
  intro c c' h
  apply M_injective h2
  apply Multilinear.eval_injective
  funext b
  rw [← evalW_eq_eval0_M c b, ← evalW_eq_eval0_M c' b]
  exact congrFun h b

/-- **The `{-1,+1}` multilinear span.**  `evalW` is surjective (indeed bijective): every function on `{-1,+1}ⁿ`
is a Walsh polynomial.  Injective plus equal cardinality `|𝔽|^{2ⁿ}` forces bijectivity. -/
theorem evalW_surjective [Fintype F] [DecidableEq F] (h2 : (2 : F) ≠ 0) :
    Function.Surjective (evalW (n := n) (F := F)) := by
  have hcard : Fintype.card (Finset (Fin n) → F) = Fintype.card ((Fin n → Bool) → F) := by
    simp [Fintype.card_finset, Fintype.card_bool]
  exact ((Fintype.bijective_iff_injective_and_card evalW).mpr ⟨evalW_injective h2, hcard⟩).surjective

/-- **Forward change-of-basis: a `{0,1}` monomial in the Walsh basis.**  The dual of
`RepUnify.walshFn_eq_sum_mono0`: each `{0,1}` monomial `∏_{i∈S} (bᵢ as 0/1)` expands as a Walsh combination
supported on subsets `T ⊆ S` — total Walsh-degree `≤ |S|`, via `(bᵢ as 0/1) = 2⁻¹·(1 − (−1)^{bᵢ})`.  Because the
support is contained in `S.powerset`, this is **degree-preserving**: a degree-`d` `{0,1}` polynomial is a degree-`d`
Walsh polynomial — the representation transfer that lets the `{0,1}`-circuit approximation feed the `{−1,+1}`
`boosting_surjection`. -/
theorem monomialFn_eq_sum_walsh (h2 : (2 : F) ≠ 0) (b : Fin n → Bool) (S : Finset (Fin n)) :
    Multilinear.monomialFn (F := F) S b
      = ∑ T ∈ S.powerset, ((-(2⁻¹ : F)) ^ T.card * (2⁻¹ : F) ^ (S \ T).card) * walshFn T b := by
  have h2' : (2⁻¹ : F) + 2⁻¹ = 1 := by rw [← two_mul, mul_inv_cancel₀ h2]
  have hterm : ∀ i, (if b i then (1 : F) else 0)
      = -(2⁻¹ : F) * (if b i then (-1 : F) else 1) + 2⁻¹ := by
    intro i
    cases b i <;> simp [h2']
  unfold Multilinear.monomialFn
  simp_rw [hterm]
  rw [Finset.prod_add]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const, walshFn]
  ring

/-- The Walsh coefficients of a `{0,1}` multilinear polynomial: `(walshCoef c) T` collects, over all supersets
`S ⊇ T`, the contribution of `c S`'s monomial to the Walsh monomial `T` (the transpose of `monomialFn_eq_sum_walsh`). -/
noncomputable def walshCoef (c : Finset (Fin n) → F) : Finset (Fin n) → F :=
  fun T => ∑ S ∈ Finset.univ.filter (fun S => T ⊆ S),
    c S * ((-(2⁻¹ : F)) ^ T.card * (2⁻¹ : F) ^ (S \ T).card)

/-- **The `{0,1}` evaluation factors through the Walsh one.**  `eval0 c = evalW (walshCoef c)`: substitute the
forward change of basis into each `{0,1}` monomial and swap the order of summation (Fubini over `T ⊆ S`).  The
exact mirror of `evalW_eq_eval0_M`. -/
theorem eval_eq_evalW (h2 : (2 : F) ≠ 0) (c : Finset (Fin n) → F) (b : Fin n → Bool) :
    Multilinear.eval c b = evalW (walshCoef c) b := by
  rw [Multilinear.eval]
  simp_rw [monomialFn_eq_sum_walsh h2 b, Finset.mul_sum]
  rw [Finset.sum_comm' (t' := Finset.univ)
      (s' := fun T => Finset.univ.filter (fun S => T ⊆ S))
      (by intro S T; simp [Finset.mem_powerset, Finset.mem_filter])]
  rw [evalW]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  rw [walshCoef, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  ring

/-- **The transfer is degree-preserving.**  If `c` is supported on subsets of size `≤ d` (a degree-`d` `{0,1}`
polynomial), then so is `walshCoef c`: for `|T| > d`, every superset `S ⊇ T` has `|S| ≥ |T| > d`, so `c S = 0`. -/
theorem walshCoef_support {d : ℕ} (c : Finset (Fin n) → F) (hc : ∀ S, d < S.card → c S = 0)
    (T : Finset (Fin n)) (hT : d < T.card) : walshCoef c T = 0 := by
  rw [walshCoef]
  refine Finset.sum_eq_zero (fun S hS => ?_)
  rw [Finset.mem_filter] at hS
  rw [hc S (lt_of_lt_of_le hT (Finset.card_le_card hS.2)), zero_mul]

end PallLean.Paper93.DeepMath.PathB.WalshSpan

#print axioms PallLean.Paper93.DeepMath.PathB.WalshSpan.evalW_eq_eval0_M
#print axioms PallLean.Paper93.DeepMath.PathB.WalshSpan.monomialFn_eq_sum_walsh
#print axioms PallLean.Paper93.DeepMath.PathB.WalshSpan.eval_eq_evalW
#print axioms PallLean.Paper93.DeepMath.PathB.WalshSpan.walshCoef_support
#print axioms PallLean.Paper93.DeepMath.PathB.WalshSpan.M_injective
#print axioms PallLean.Paper93.DeepMath.PathB.WalshSpan.evalW_surjective
