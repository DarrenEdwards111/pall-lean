import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0BTSizeRecurrence

/-!
# The `MOD₆` probabilistic polynomial — and the genuine Razborov–Smolensky core it reduces to

This file attacks the `MOD₆` probabilistic polynomial honestly, and the analysis splits cleanly:

**The `MOD` gates need *no* probabilism — they are *exactly* low-degree over their prime field.**  Over `F₂` the
`MOD₂` (residue-`0`) indicator is `1 + a` (degree `1`); over `F₃` the `MOD₃` indicator is `1 - a²` (degree `2`, by
Fermat).  So the `MOD₆ = MOD₂ ∧ MOD₃` predicate is an *exact* low-degree polynomial over the product `F₂ × F₃` (no
approximation, contrary to a naive reading).  The probabilistic polynomial of Razborov–Smolensky is needed for the
**`AND`/`OR` layer**, not the `MOD` gate.

**The genuine probabilistic ingredient is the `OR` polynomial**, and its whole content is one counting fact: a
*uniformly random `F_p`-linear form vanishes on a fixed nonzero vector with probability exactly `1/p`*.  We prove this
(`linear_form_balance`) by additive equidistribution (all fibres of the dot-product hom are equicardinal), and use it
to prove the `OR` probabilistic polynomial `(∑ rᵢ vᵢ)^{p-1}` has degree `p-1` and agrees with `OR` on all but a `1/p`
fraction of `r` (`orPoly_error`), and is *exactly* correct on the all-zero input (`orPoly_zero`).

## What is proved (clean axioms, no `sorry`)

* **`mod2_indicator`** / **`mod3_indicator`** — the exact low-degree `MOD` indicators over `F₂` / `F₃`.
* **`mod6_indicator_product`** — `MOD₆` is the exact low-degree pair over `F₂ × F₃`.
* **`linear_form_balance`** — `p · #{r : ⟨r,v⟩ = 0} = p^m` for `v ≠ 0`: the random linear form vanishes with
  probability exactly `1/p` (the Razborov–Smolensky probabilistic core).
* **`orPoly_eq`**, **`orPoly_zero`**, **`orPoly_error`** — the `OR` probabilistic polynomial: value `0/1`, exact on
  `0`, and error exactly `1/p` on nonzero inputs.

## The open content (socketed honestly)

* **`AmplifiedErrorSocket`** — boosting the single-form error `1/p` to `ε` by `t` independent forms (error `(1/p)^t`,
  degree `t(p-1)`); the independence/product bound is the remaining bookkeeping, left as the named socket feeding
  `…ACC0BTSizeRecurrence.QuasipolyApproxCompression`.

## Honest scope

The exact `MOD` polynomials and the full single-form `OR` probabilistic polynomial (with its `1/p` error proved from
the linear-form count) are *proved*.  The degree-boosting amplification to sub-constant error and the assembly into a
constant-depth quasipolynomial representation remain the named socket.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0Mod6ProbabilisticPolynomial

open scoped Classical BigOperators
open Finset

/-! ## 1. The `MOD` gates are exactly low-degree (no probabilism) -/

/-- **`MOD₂` indicator (proved, exact degree 1): `1 + a = [a = 0]` over `F₂`.** -/
theorem mod2_indicator : ∀ a : ZMod 2, 1 + a = if a = 0 then 1 else 0 := by decide

/-- **`MOD₃` indicator (proved, exact degree 2): `1 - a² = [a = 0]` over `F₃`** (Fermat). -/
theorem mod3_indicator : ∀ a : ZMod 3, 1 - a ^ 2 = if a = 0 then 1 else 0 := by decide

/-- **`MOD₆` indicator over the product `F₂ × F₃` (proved, exact low degree).**  The `MOD₆` residue-`0` predicate of a
pair `(a, b)` is detected by *both* exact indicators firing: `1 + a = 1` over `F₂` (degree 1) *and* `1 - b² = 1` over
`F₃` (degree 2).  No approximation — the two live in different fields and are combined as a pair, not a product. -/
theorem mod6_indicator_product : ∀ (a : ZMod 2) (b : ZMod 3),
    ((1 + a = 1) ∧ (1 - b ^ 2 = 1)) ↔ (a = 0 ∧ b = 0) := by decide

/-! ## 2. The random-linear-form balance — the Razborov–Smolensky probabilistic core -/

variable {p m : ℕ} [Fact p.Prime]

/-- The dot product `r ↦ ∑ᵢ rᵢ vᵢ` as an additive hom (so translation arguments apply). -/
def dotHom (v : Fin m → ZMod p) : (Fin m → ZMod p) →+ ZMod p where
  toFun r := ∑ i, r i * v i
  map_zero' := by simp
  map_add' a b := by simp [Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem dotHom_apply (v r : Fin m → ZMod p) : dotHom v r = ∑ i, r i * v i := rfl

/-- The dot-product hom is surjective when `v ≠ 0`. -/
theorem dotHom_surjective (v : Fin m → ZMod p) (hv : v ≠ 0) :
    Function.Surjective (dotHom v) := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
  rw [Pi.zero_apply] at hj
  intro c
  refine ⟨fun i => if i = j then c * (v j)⁻¹ else 0, ?_⟩
  rw [dotHom_apply, Finset.sum_eq_single j]
  · rw [if_pos rfl, mul_assoc, inv_mul_cancel₀ hj, mul_one]
  · intro i _ hij; rw [if_neg hij, zero_mul]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- **The random linear form vanishes with probability exactly `1/p` (proved).**  For `v ≠ 0`,
`p · #{r : ∑ᵢ rᵢ vᵢ = 0} = p^m` — i.e. the vanishing set is an exact `1/p` fraction of all `r`.  This is the
Razborov–Smolensky probabilistic core, proved by additive equidistribution of the dot-product hom's fibres. -/
theorem linear_form_balance (v : Fin m → ZMod p) (hv : v ≠ 0) :
    p * (Finset.univ.filter (fun r : Fin m → ZMod p => (∑ i, r i * v i) = 0)).card = p ^ m := by
  have hsurj := dotHom_surjective v hv
  -- all fibres of `dotHom v` have the same cardinality as the fibre over `0`
  have heq : ∀ c : ZMod p,
      (Finset.univ.filter (fun r => dotHom v r = c)).card
        = (Finset.univ.filter (fun r => dotHom v r = 0)).card := by
    intro c
    obtain ⟨r0, hr0⟩ := hsurj c
    apply Finset.card_bij' (fun r _ => r - r0) (fun r _ => r + r0) <;>
      intro r hr <;> simp_all [Finset.mem_filter, map_sub, map_add]
  -- partition all `r` by their dot-product value
  have hfib : (Finset.univ : Finset (Fin m → ZMod p)).card
      = ∑ _c : ZMod p, (Finset.univ.filter (fun r => dotHom v r = 0)).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := dotHom v) (t := Finset.univ)
      (fun x _ => Finset.mem_univ _)]
    exact Finset.sum_congr rfl (fun c _ => heq c)
  have hdom : (Finset.univ : Finset (Fin m → ZMod p)).card = p ^ m := by
    rw [Finset.card_univ, Fintype.card_pi]
    simp [ZMod.card]
  rw [hdom] at hfib
  rw [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul] at hfib
  -- `hfib : p^m = p * card(fibre 0)`; the goal's filter is that same fibre (defeq)
  exact hfib.symm

/-! ## 3. The `OR` probabilistic polynomial -/

/-- The Razborov–Smolensky `OR` polynomial: `(∑ᵢ rᵢ vᵢ)^{p-1}` (degree `p-1`). -/
def orPoly (v r : Fin m → ZMod p) : ZMod p := (∑ i, r i * v i) ^ (p - 1)

/-- **The `OR` polynomial is a `0/1` indicator of the linear form (proved, Fermat).** -/
theorem orPoly_eq (v r : Fin m → ZMod p) :
    orPoly v r = if (∑ i, r i * v i) = 0 then 0 else 1 := by
  unfold orPoly
  split
  · rename_i h
    rw [h]
    exact zero_pow (by have := (Fact.out : p.Prime).two_le; omega)
  · rename_i h
    exact ZMod.pow_card_sub_one_eq_one h

/-- **Exact on the all-zero input (proved): `orPoly 0 r = 0 = OR(0)`.** -/
theorem orPoly_zero (r : Fin m → ZMod p) : orPoly (0 : Fin m → ZMod p) r = 0 := by
  rw [orPoly_eq]; simp

/-- **The `OR` probabilistic polynomial has error exactly `1/p` (proved).**  For `v ≠ 0` (so `OR(v) = 1`), the
polynomial `orPoly v r` equals `1` except on an exact `1/p` fraction of `r`:
`p · #{r : orPoly v r ≠ 1} = p^m`.  Together with `orPoly_zero` this is the degree-`(p-1)` `OR` probabilistic
polynomial of Razborov–Smolensky. -/
theorem orPoly_error (v : Fin m → ZMod p) (hv : v ≠ 0) :
    p * (Finset.univ.filter (fun r => orPoly v r ≠ 1)).card = p ^ m := by
  have hset : (Finset.univ.filter (fun r => orPoly v r ≠ 1))
      = Finset.univ.filter (fun r : Fin m → ZMod p => (∑ i, r i * v i) = 0) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h : (∑ i, r i * v i) = 0 <;> simp [orPoly_eq, h]
  rw [hset]
  exact linear_form_balance v hv

/-! ## 4. The amplification socket (boosting `1/p` to `ε`) -/

/-- **The amplification socket (open).**  Boosting the single-form error `1/p` to a target `ε` by `t` independent
linear forms — error `(1/p)^t`, degree `t·(p-1)` — and assembling the resulting probabilistic polynomial into a
constant-depth quasipolynomial `SYM∘AND` representation.  The independence/product error bound is the remaining
bookkeeping (cf. `…ACC0BTSizeRecurrence.error_union_bound`); left as the named hypothesis feeding
`QuasipolyApproxCompression`. -/
def AmplifiedErrorSocket (qpoly : ℕ → ℕ) (eps : ℝ) : Prop :=
  ACC0BTSizeRecurrence.QuasipolyApproxCompression qpoly eps

end PallLean.Paper93.DeepMath.PathB.ACC0Mod6ProbabilisticPolynomial

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Mod6ProbabilisticPolynomial.mod3_indicator
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Mod6ProbabilisticPolynomial.mod6_indicator_product
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Mod6ProbabilisticPolynomial.linear_form_balance
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Mod6ProbabilisticPolynomial.orPoly_eq
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Mod6ProbabilisticPolynomial.orPoly_zero
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Mod6ProbabilisticPolynomial.orPoly_error
