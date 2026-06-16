import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0Mod6ProbabilisticPolynomial

/-!
# Razborov–Smolensky amplification — the product error bound `(1/p)^t`

The single-form `OR` probabilistic polynomial (`…ACC0Mod6ProbabilisticPolynomial.orPoly_error`) has a *constant* error
`1/p`.  To make the error sub-constant we amplify with `t` **independent** linear forms `R : Fin t → (Fin m → ZMod p)`
and take their `OR`:
\[ \mathrm{amplifiedOrPoly}\,v\,R \;=\; 1 - \prod_{s} \bigl(1 - \mathrm{orPoly}\,v\,(R\,s)\bigr), \]
a polynomial of degree `t·(p-1)`.  For a fixed nonzero `v` (so `OR(v) = 1`) the amplified polynomial is `0` (an error)
*only* when **all** `t` forms vanish on `v` — which, the forms being independent, happens for an exact `(1/p)^t`
fraction of `R`.

This file proves that **product bound**, the genuine amplification step, directly from the single-form balance.

## What is proved (clean axioms, no `sorry`)

* **`amplified_form_balance`** — `p^t · #{R : ∀ s, ∑ᵢ R s i vᵢ = 0} = p^{m·t}` for `v ≠ 0`: all `t` independent forms
  vanish on `v` for an exact `(1/p)^t` fraction of `R`.  (Proof: the joint vanishing set is the `t`-fold product
  `Fintype.piFinset` of the single-form set, so its card is `(single)^t`; then `p^t·(single)^t = (p·single)^t =
  (p^m)^t = p^{m·t}` by `linear_form_balance`.)
* **`amplifiedOrPoly`, `amplifiedOrPoly_eq_zero_iff`** — the amplified polynomial vanishes iff *all* forms vanish.
* **`amplifiedOrPoly_zero`** — exact on the all-zero input (`= 0 = OR(0)`).
* **`amplifiedOrPoly_error`** — `p^t · #{R : amplifiedOrPoly v R = 0} = p^{m·t}`: the amplified `OR` polynomial of
  degree `t·(p-1)` has error exactly `(1/p)^t` on nonzero inputs.

## Honest scope

This is the exact amplification of the error from `1/p` to `(1/p)^t`.  Choosing `t = O(log_p s)` drives the per-gate
error below `1/(10s)` (cf. `…ACC0BTSizeRecurrence.error_choice`), and the union bound `error_union_bound` then keeps a
size-`s` constant-depth circuit's total error `< 1/10`.  The remaining step — substituting these probabilistic
polynomials through the whole circuit and reading off the quasipolynomial `SYM∘AND` representation — is the named
socket `…ACC0BTSizeRecurrence.QuasipolyApproxCompression`.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ProbabilisticAmplification

open scoped Classical BigOperators
open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0Mod6ProbabilisticPolynomial

variable {p m : ℕ} [Fact p.Prime]

/-! ## 1. The product error bound -/

/-- **The amplification product bound (proved): all `t` independent forms vanish on `v ≠ 0` with probability exactly
`(1/p)^t`.**  `p^t · #{R : ∀ s, ∑ᵢ R s i vᵢ = 0} = p^{m·t}`.  The joint vanishing set is the `t`-fold product of the
single-form set, whose `(1/p)`-balance is `linear_form_balance`. -/
theorem amplified_form_balance (v : Fin m → ZMod p) (hv : v ≠ 0) (t : ℕ) :
    p ^ t *
        (Finset.univ.filter
          (fun R : Fin t → (Fin m → ZMod p) => ∀ s, (∑ i, R s i * v i) = 0)).card
      = p ^ (m * t) := by
  have hjoint :
      (Finset.univ.filter (fun R : Fin t → (Fin m → ZMod p) => ∀ s, (∑ i, R s i * v i) = 0))
        = Fintype.piFinset
            (fun _ : Fin t => Finset.univ.filter (fun r : Fin m → ZMod p => (∑ i, r i * v i) = 0)) := by
    ext R
    simp [Fintype.mem_piFinset, Finset.mem_filter]
  rw [hjoint, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← mul_pow, linear_form_balance v hv, ← pow_mul]

/-! ## 2. The amplified `OR` probabilistic polynomial -/

/-- The amplified `OR` polynomial: the `OR` of `t` independent single-form polynomials,
`1 - ∏ₛ (1 - orPoly v (R s))` — degree `t·(p-1)`. -/
def amplifiedOrPoly {t : ℕ} (v : Fin m → ZMod p) (R : Fin t → (Fin m → ZMod p)) : ZMod p :=
  1 - ∏ s, (1 - orPoly v (R s))

/-- **The amplified polynomial vanishes iff every form vanishes (proved).** -/
theorem amplifiedOrPoly_eq_zero_iff {t : ℕ} (v : Fin m → ZMod p)
    (R : Fin t → (Fin m → ZMod p)) :
    amplifiedOrPoly v R = 0 ↔ ∀ s, (∑ i, R s i * v i) = 0 := by
  unfold amplifiedOrPoly
  rw [sub_eq_zero]
  constructor
  · intro h s
    by_contra hs
    have hfac : (1 : ZMod p) - orPoly v (R s) = 0 := by
      rw [orPoly_eq, if_neg hs]; ring
    have hzero : ∏ s', (1 - orPoly v (R s')) = 0 := Finset.prod_eq_zero (Finset.mem_univ s) hfac
    rw [← h] at hzero
    exact one_ne_zero hzero
  · intro h
    rw [eq_comm]
    exact Finset.prod_eq_one (fun s _ => by rw [orPoly_eq, if_pos (h s), sub_zero])

/-- **Exact on the all-zero input (proved): `amplifiedOrPoly 0 R = 0 = OR(0)`.** -/
theorem amplifiedOrPoly_zero {t : ℕ} (R : Fin t → (Fin m → ZMod p)) :
    amplifiedOrPoly (0 : Fin m → ZMod p) R = 0 := by
  rw [amplifiedOrPoly_eq_zero_iff]
  intro s; simp

/-- **The amplified `OR` polynomial has error exactly `(1/p)^t` (proved).**  For `v ≠ 0` (so `OR(v) = 1`), the
degree-`t·(p-1)` polynomial `amplifiedOrPoly v R` equals `1` except on an exact `(1/p)^t` fraction of `R`:
`p^t · #{R : amplifiedOrPoly v R = 0} = p^{m·t}`. -/
theorem amplifiedOrPoly_error (v : Fin m → ZMod p) (hv : v ≠ 0) (t : ℕ) :
    p ^ t * (Finset.univ.filter
        (fun R : Fin t → (Fin m → ZMod p) => amplifiedOrPoly v R = 0)).card
      = p ^ (m * t) := by
  have hset :
      (Finset.univ.filter (fun R : Fin t → (Fin m → ZMod p) => amplifiedOrPoly v R = 0))
        = Finset.univ.filter (fun R : Fin t → (Fin m → ZMod p) => ∀ s, (∑ i, R s i * v i) = 0) := by
    ext R
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, amplifiedOrPoly_eq_zero_iff]
  rw [hset]
  exact amplified_form_balance v hv t

end PallLean.Paper93.DeepMath.PathB.ACC0ProbabilisticAmplification

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ProbabilisticAmplification.amplified_form_balance
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ProbabilisticAmplification.amplifiedOrPoly_eq_zero_iff
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ProbabilisticAmplification.amplifiedOrPoly_zero
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ProbabilisticAmplification.amplifiedOrPoly_error
