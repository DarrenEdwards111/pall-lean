import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3AC0pFoundations
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.ZMod.Basic

/-!
# Layer 3 — Razborov–Smolensky low-degree approximation: the single-form test (degree atom)

The exact representation (`…AC0pPoly*`) is high-degree (`∧`/`∨` have degree = fan-in).  The lower bound
comes from the **low-degree approximation** (`SCOPE_LAYER3_RS_APPROXIMATION.md`): replace each `∨`/`∧`
gate by a *probabilistic* polynomial of degree `O((p-1)·log(1/ε))` agreeing on a `1-ε` fraction.

This file builds the **atom** of that construction — a single random-linear-form "zero test" — and its
**total-degree bound**:

* `linFormTest p r` — `1 - (∑_i r_i · X_i)^(p-1)`, the Fermat indicator of "the random linear form
  `∑ r_i x_i` is zero".  (For a `{0,1}` input that is *not* all-zero, the form is nonzero with
  probability `≥ 1 - 1/p` over random `r` — the *agreement* half, deferred; this file is the degree.)
* `linFormTest_totalDegree_le` — `totalDegree (linFormTest p r) ≤ p - 1`.

A product of `t` such tests has degree `≤ (p-1)·t`; that is the degree side of the OR-approximator.  No
lower bound, no capstone.  AC⁰[p] is a higher circuit-lower-bound layer; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Layer3

open MvPolynomial

variable {m : ℕ}

/-- A single random-linear-form **zero test**: `1 - (∑_i r_i · X_i)^(p-1)`.  Over a prime field this is
the Fermat indicator of "`∑ r_i x_i = 0`" (`fermat_indicator`), the atom of the OR-approximator. -/
noncomputable def linFormTest (p : ℕ) (r : Fin m → ZMod p) : MvPolynomial (Fin m) (ZMod p) :=
  1 - (∑ i, C (r i) * X i) ^ (p - 1)

/-- **Degree of the single-form test:** `totalDegree (linFormTest p r) ≤ p - 1`. -/
theorem linFormTest_totalDegree_le (p : ℕ) [Fact p.Prime] (r : Fin m → ZMod p) :
    (linFormTest p r).totalDegree ≤ p - 1 := by
  have hform : (∑ i : Fin m, C (r i) * X i).totalDegree ≤ 1 := by
    refine le_trans (totalDegree_finset_sum _ _) (Finset.sup_le fun i _ => ?_)
    refine le_trans (totalDegree_mul _ _) ?_
    rw [totalDegree_C, zero_add]
    exact le_of_eq (totalDegree_X i)
  have hpow : ((∑ i : Fin m, C (r i) * X i) ^ (p - 1)).totalDegree ≤ p - 1 := by
    refine le_trans (totalDegree_pow _ _) ?_
    calc (p - 1) * (∑ i : Fin m, C (r i) * X i).totalDegree
        ≤ (p - 1) * 1 := Nat.mul_le_mul_left _ hform
      _ = p - 1 := Nat.mul_one _
  rw [linFormTest]
  refine le_trans (totalDegree_sub _ _) ?_
  rw [totalDegree_one]
  simpa using hpow

open Finset in
/-- **OR single-form agreement.**  For a nonzero `{0,1}` input `x` (some `x i = true`), a random linear
form `∑ r_i x_i` over `ZMod p` is nonzero on all but a `1/p` fraction of `r`: the count of `r` with the
form nonzero is exactly `p^m - p^(m-1) = (p-1)·p^(m-1)`.  (The agreement half of the OR-approximator;
combine with `linFormTest_totalDegree_le` for the degree.) -/
theorem orForm_agreement (p : ℕ) [Fact p.Prime] {m : ℕ} (x : Fin m → Bool) (hx : ∃ i, x i = true) :
    (Finset.univ.filter (fun r : Fin m → ZMod p => ∑ i, r i * boolToZMod p (x i) ≠ 0)).card
      = p ^ m - p ^ (m - 1) := by
  classical
  obtain ⟨j, hj⟩ := hx
  set a : Fin m → ZMod p := fun i => boolToZMod p (x i) with ha
  have haj : a j = 1 := by rw [ha]; simp [boolToZMod, hj]
  -- the linear functional `L r = ∑ r_i a_i`
  let L : (Fin m → ZMod p) →ₗ[ZMod p] ZMod p :=
    { toFun := fun r => ∑ i, r i * a i
      map_add' := by intro r s; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c r
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring) }
  have hsurj : Function.Surjective L := fun c => by
    refine ⟨Function.update (0 : Fin m → ZMod p) j c, ?_⟩
    show ∑ i, (Function.update (0 : Fin m → ZMod p) j c) i * a i = c
    rw [Finset.sum_eq_single j]
    · rw [Function.update_self, haj, mul_one]
    · intro i _ hij
      rw [Function.update_of_ne hij, Pi.zero_apply, zero_mul]
    · intro h; exact absurd (Finset.mem_univ j) h
  -- finrank of the kernel is `m - 1`
  have hV : Module.finrank (ZMod p) (Fin m → ZMod p) = m := by
    rw [Module.finrank_pi]; simp
  have hrank : Module.finrank (ZMod p) (LinearMap.range L) = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self]
  have hker : Module.finrank (ZMod p) (LinearMap.ker L) = m - 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker L
    rw [hrank, hV] at h; omega
  -- card of the kernel set
  have hcardker : (Finset.univ.filter (fun r : Fin m → ZMod p => ∑ i, r i * a i = 0)).card
      = p ^ (m - 1) := by
    have hsub : (Finset.univ.filter (fun r : Fin m → ZMod p => ∑ i, r i * a i = 0)).card
        = Fintype.card (LinearMap.ker L) := by
      rw [← Fintype.card_subtype (fun r : Fin m → ZMod p => ∑ i, r i * a i = 0)]
      exact Fintype.card_congr (Equiv.subtypeEquivRight (fun r => Iff.rfl))
    rw [hsub, Module.card_eq_pow_finrank (K := ZMod p) (V := LinearMap.ker L), ZMod.card, hker]
  -- assemble
  have hcompl := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (Finset.univ : Finset (Fin m → ZMod p))) (p := fun r => ∑ i, r i * a i = 0)
  rw [hcardker] at hcompl
  have hcuniv : (Finset.univ : Finset (Fin m → ZMod p)).card = p ^ m := by
    rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  rw [hcuniv] at hcompl
  have : (Finset.univ.filter (fun r : Fin m → ZMod p => ∑ i, r i * boolToZMod p (x i) ≠ 0)).card
      = (Finset.univ.filter (fun r : Fin m → ZMod p => ¬ (∑ i, r i * a i = 0))).card := rfl
  rw [this]; omega

/-! ## `t`-fold OR amplification — degree composition

A single `linFormTest` is `1` exactly when its random linear form vanishes.  Taking a product of `t`
independent forms, `orApproxProd`, is `1` iff *all* `t` forms vanish; `orApprox := 1 - orApproxProd`
is then the Razborov OR-approximator: `0` on the all-zero input, and `1` unless all `t` forms vanish
(probability `p^{-t}` for a nonzero input — the error half, the next frontier).  Here we build only the
**degree composition**: the product of `t` degree-`(p-1)` atoms has degree `≤ (p-1)·t`. -/

variable {t : ℕ}

/-- The **`t`-fold product** of single-form tests: `∏_{k<t} linFormTest p (R k)`.  Equals `1` iff every
sampled linear form `∑_i R k i · x_i` vanishes. -/
noncomputable def orApproxProd (p : ℕ) {m t : ℕ} (R : Fin t → Fin m → ZMod p) :
    MvPolynomial (Fin m) (ZMod p) :=
  ∏ k : Fin t, linFormTest p (R k)

/-- The **`t`-fold OR approximator** `1 - ∏_{k<t} linFormTest p (R k)`.  It is `0` on the all-zero input
and approximates `OR` with one-sided error `≤ p^{-t}` on nonzero inputs (error bound deferred). -/
noncomputable def orApprox (p : ℕ) {m t : ℕ} (R : Fin t → Fin m → ZMod p) :
    MvPolynomial (Fin m) (ZMod p) :=
  1 - orApproxProd p R

/-- **Degree of the `t`-fold product:** `totalDegree (orApproxProd p R) ≤ (p-1)·t` — the `t` degree-`(p-1)`
atoms (`linFormTest_totalDegree_le`) compose additively under `totalDegree_finset_prod`. -/
theorem orApproxProd_totalDegree_le (p : ℕ) [Fact p.Prime] {m t : ℕ}
    (R : Fin t → Fin m → ZMod p) :
    (orApproxProd p R).totalDegree ≤ (p - 1) * t := by
  rw [orApproxProd]
  refine le_trans (totalDegree_finset_prod _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun k _ => linFormTest_totalDegree_le p (R k))) ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  exact Nat.le_of_eq (Nat.mul_comm t (p - 1))

/-- **Degree of the OR approximator:** `totalDegree (orApprox p R) ≤ (p-1)·t`.  Subtracting from the
constant `1` cannot raise the degree (`totalDegree_sub`), so the bound transfers from
`orApproxProd_totalDegree_le`. -/
theorem orApprox_totalDegree_le (p : ℕ) [Fact p.Prime] {m t : ℕ}
    (R : Fin t → Fin m → ZMod p) :
    (orApprox p R).totalDegree ≤ (p - 1) * t := by
  rw [orApprox]
  refine le_trans (totalDegree_sub _ _) ?_
  rw [totalDegree_one, Nat.zero_max]
  exact orApproxProd_totalDegree_le p R

/-- **All-false correctness:** evaluating the OR approximator on the all-zero `{0,1}` input gives `0`
exactly.  Each linear form `∑_i R k i · 0` vanishes, so each `linFormTest` evaluates to
`1 - 0^{p-1} = 1`; the product is `1` and `orApprox = 1 - 1 = 0`. -/
theorem orApprox_eval_allFalse (p : ℕ) [Fact p.Prime] {m t : ℕ}
    (R : Fin t → Fin m → ZMod p) :
    eval (fun i => boolToZMod p ((fun _ => false) i)) (orApprox p R) = 0 := by
  have hp1 : p - 1 ≠ 0 := by
    have h2 := (Fact.out (p := p.Prime)).two_le; omega
  have hatom : ∀ k, eval (fun i => boolToZMod p ((fun _ => false) i)) (linFormTest p (R k)) = 1 := by
    intro k
    rw [linFormTest]
    simp only [map_sub, map_one, map_pow, map_sum, map_mul, eval_C, eval_X,
      boolToZMod_false, mul_zero, Finset.sum_const_zero, zero_pow hp1, sub_zero]
  rw [orApprox, orApproxProd]
  simp only [map_sub, map_one, map_prod, hatom, Finset.prod_const_one, sub_self]

/-! ## `t`-fold error count — the `p^{-t}` bound

On a nonzero `{0,1}` input the OR approximator errs (`orApprox` evaluates to `0` instead of `1`) exactly
when *all* `t` sampled forms vanish, i.e. `∀ k, ∑_i R k i · x_i = 0`.  `orForm_zero_count` counts the
single-form bad set — the kernel hyperplane, `p^{m-1}` of the `p^m` samples (the complement of the
nonzero count `orForm_agreement`).  Independence across the `t` coordinates (`Fintype.piFinset`) raises
this to `(p^{m-1})^t` bad tuples out of `(p^m)^t` total, so the error rate is exactly `p^{-t}`
(`orApprox_error_rate`: bad-count · `p^t` = total). -/

/-- **Single-form bad count.**  For a nonzero `{0,1}` input the linear form `∑_i r_i · x_i` vanishes on
exactly `p^{m-1}` of the `p^m` samples — the kernel hyperplane, complement of `orForm_agreement`'s
nonzero count. -/
theorem orForm_zero_count (p : ℕ) [Fact p.Prime] {m : ℕ} (x : Fin m → Bool) (hx : ∃ i, x i = true) :
    (Finset.univ.filter (fun r : Fin m → ZMod p => ∑ i, r i * boolToZMod p (x i) = 0)).card
      = p ^ (m - 1) := by
  classical
  have hpos : 0 < p := (Fact.out (p := p.Prime)).pos
  have hle : p ^ (m - 1) ≤ p ^ m := Nat.pow_le_pow_right hpos (Nat.sub_le m 1)
  have htot : (Finset.univ : Finset (Fin m → ZMod p)).card = p ^ m := by
    rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin m → ZMod p)))
    (p := fun r => ∑ i, r i * boolToZMod p (x i) = 0)
  rw [htot] at hsplit
  have hne : (Finset.univ.filter
      (fun r : Fin m → ZMod p => ¬ (∑ i, r i * boolToZMod p (x i) = 0))).card
        = p ^ m - p ^ (m - 1) := orForm_agreement p x hx
  omega

/-- **`t`-fold error count.**  For a nonzero `{0,1}` input, *all* `t` sampled forms vanish on exactly
`(p^{m-1})^t` of the tuples `R : Fin t → Fin m → ZMod p` — the independent product of the single-form
bad set across the `t` coordinates (`Fintype.piFinset`). -/
theorem orApprox_error_count (p : ℕ) [Fact p.Prime] {m t : ℕ} (x : Fin m → Bool)
    (hx : ∃ i, x i = true) :
    (Finset.univ.filter
        (fun R : Fin t → Fin m → ZMod p => ∀ k, ∑ i, R k i * boolToZMod p (x i) = 0)).card
      = (p ^ (m - 1)) ^ t := by
  classical
  have hpi : (Finset.univ.filter
        (fun R : Fin t → Fin m → ZMod p => ∀ k, ∑ i, R k i * boolToZMod p (x i) = 0))
      = Fintype.piFinset (fun _ : Fin t =>
          Finset.univ.filter (fun r : Fin m → ZMod p => ∑ i, r i * boolToZMod p (x i) = 0)) := by
    ext R
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
  rw [hpi, Fintype.card_piFinset]
  simp_rw [orForm_zero_count p x hx]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **Total sample count:** `(p^m)^t` tuples `R : Fin t → Fin m → ZMod p`. -/
theorem orApprox_sample_count (p : ℕ) [Fact p.Prime] {m t : ℕ} :
    (Finset.univ : Finset (Fin t → Fin m → ZMod p)).card = (p ^ m) ^ t := by
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fun, ZMod.card, Fintype.card_fin,
    Fintype.card_fin]

/-- **Error rate `p^{-t}` (exact).**  The bad-tuple count times `p^t` equals the total sample count
`(p^{m-1})^t · p^t = (p^m)^t`; equivalently, the fraction of erring samples on any nonzero input is
exactly `p^{-t}`. -/
theorem orApprox_error_rate (p : ℕ) [Fact p.Prime] {m t : ℕ} (x : Fin m → Bool)
    (hx : ∃ i, x i = true) :
    (Finset.univ.filter
        (fun R : Fin t → Fin m → ZMod p => ∀ k, ∑ i, R k i * boolToZMod p (x i) = 0)).card * p ^ t
      = (Finset.univ : Finset (Fin t → Fin m → ZMod p)).card := by
  rw [orApprox_error_count p x hx, orApprox_sample_count]
  obtain ⟨i, _⟩ := hx
  have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hmm : p ^ (m - 1) * p = p ^ m := by
    rw [← pow_succ, Nat.sub_add_cancel hm]
  rw [← mul_pow, hmm]

end PallLean.Paper93.DeepMath.PathB.Layer3

#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.linFormTest_totalDegree_le
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.orForm_agreement
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.orApproxProd_totalDegree_le
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.orApprox_totalDegree_le
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.orApprox_eval_allFalse
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.orForm_zero_count
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.orApprox_error_count
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.orApprox_sample_count
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.orApprox_error_rate
