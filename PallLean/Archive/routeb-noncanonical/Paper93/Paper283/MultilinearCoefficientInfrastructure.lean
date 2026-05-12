import PallLean.CookLevinDefs
import PallLean.CompiledBoolFactorBridge
import PallLean.SymmetricPower
import PallLean.MultilinearSPDP
import PallLean.Paper93.Paper283.BridgeABoolDerivative
import PallLean.Paper93.Paper283.BridgeABlockProductRule
import PallLean.Paper93.Paper283.BridgeABlockEvalAtZero
import PallLean.Paper93.Paper283.BridgeAMlProjLinear
import PallLean.Paper93.Paper283.ListProdDerivativeConstantCoeff
import Mathlib.Tactic

/-!
# Multilinear monomial coefficient infrastructure for κ = 2 Bridge A

This file provides the missing kernel-only infrastructure for extracting
coefficients of multilinear two-variable monomials (`X_v · X_w` with
`v ≠ w`) from products of polynomial factors of the shape that arise in
the Cook-Levin compilation: the booleanity and adjacency / transition
factors `1 - c.poly`.

It is the bilinear-coefficient analogue of `BridgeABlockEvalAtZero` /
`ListProdDerivativeConstantCoeff` (which evaluate constant terms of
list-product derivatives).  At the constant term every non-constant
factor collapsed to its constant term `1`; at the `X_v · X_w` term we
pick up two non-trivial factor contributions per term, indexed by
ordered pairs of distinct factors plus single-factor `X_v · X_w`
contributions.

## Headline lemmas

* `coeff_two_mono_mul`               -- bilinear analogue of `coeff_single_mul`.
* `coeff_two_mono_list_prod_expand`  -- path expansion of
                                       `coeff (X_v · X_w) (List.prod fs)`.
* `coeff_X_a_one_sub_X_v`            -- coefficients of `X_a` in `1 - X_v`.
* `coeff_one_sub_X_v_at_X_a_X_b`     -- coefficient of `X_a X_b` in `1 - X_v`
                                       (always `0`).
* `coeff_one_sub_C_X_i_X_j_at_X_a_X_b`
                                     -- coefficient of `X_a X_b` in
                                       `1 - C c · X_i · X_j`.
* `coeff_two_mono_pderiv_boolLC_factor`
                                     -- `coeff (X_a X_b) (pderiv v (1 - boolLC.poly))`.
* `coeff_two_mono_pderiv_cadj_factor`
                                     -- `coeff (X_a X_b) (pderiv v (1 - C c · X_i · X_j))`.
* `coeff_two_mono_mlProj_eq`         -- multilinear monomial coefficient
                                       passes through `mlProj`.

All proofs are kernel-only: they reduce to
`MvPolynomial.coeff_mul`, `MvPolynomial.coeff_X'`,
`MvPolynomial.coeff_C`, `MvPolynomial.coeff_one`,
`MvPolynomial.coeff_sub`, plus the pre-existing `BridgeA*` derivative
lemmas.
-/

namespace PallLean.Paper93.Paper283

open MvPolynomial
open PaperFaithfulSeparation
open MultilinearSPDP

attribute [local instance] Classical.dec

namespace MultilinearCoefficientInfrastructure

/-! ## Two-variable monomial: helpers about `single v 1 + single w 1` -/

/-- The two-variable multilinear monomial `single v 1 + single w 1` is a
    multilinear finsupp (every coordinate is `≤ 1`) when `v ≠ w`. -/
theorem isMultilinear_single_add_single {σ : Type*} [DecidableEq σ]
    (v w : σ) (hvw : v ≠ w) :
    Finsupp.IsMultilinear
      (Finsupp.single v 1 + Finsupp.single w 1 : σ →₀ ℕ) := by
  intro i
  by_cases hiv : i = v
  · subst hiv
    simp [Finsupp.add_apply, Finsupp.single_apply, hvw.symm]
  · by_cases hiw : i = w
    · subst hiw
      simp [Finsupp.add_apply, Finsupp.single_apply, hiv]
    · simp [Finsupp.add_apply, Finsupp.single_apply, hiv, hiw]

/-- The two-variable monomial `single v 1 + single w 1` is nonzero. -/
theorem two_mono_ne_zero {σ : Type*} [DecidableEq σ]
    (v w : σ) :
    (0 : σ →₀ ℕ) ≠ Finsupp.single v 1 + Finsupp.single w 1 := by
  intro h
  have hv := DFunLike.congr_fun h v
  rw [Finsupp.coe_zero, Pi.zero_apply, Finsupp.add_apply,
    Finsupp.single_apply, if_pos rfl] at hv
  -- hv : 0 = 1 + (single w 1) v.  Even if (single w 1) v = 0, contradiction.
  by_cases hwv : w = v
  · rw [Finsupp.single_apply, if_pos hwv] at hv; omega
  · rw [Finsupp.single_apply, if_neg hwv] at hv; omega

/-! ## Coefficient of `X_v · X_w` in basic polynomials

We establish coefficients of the two-variable monomial in the
fundamental polynomials `X i`, `X i * X j`, `1`, and `C c`.
-/

/-- The coefficient of `X v * X w` (v ≠ w) in `X i` is `0` (degree mismatch). -/
theorem coeff_two_mono_X {σ : Type*} [DecidableEq σ] {R : Type*} [CommRing R]
    (v w i : σ) (hvw : v ≠ w) :
    MvPolynomial.coeff (Finsupp.single v 1 + Finsupp.single w 1)
      (MvPolynomial.X i : MvPolynomial σ R) = 0 := by
  rw [MvPolynomial.coeff_X']
  rw [if_neg]
  intro h
  -- single i 1 = single v 1 + single w 1.  Sum of values is 1 on LHS, 2 on RHS.
  have hsum : (Finsupp.single i 1 : σ →₀ ℕ).sum (fun _ n => n) =
      ((Finsupp.single v 1 + Finsupp.single w 1 : σ →₀ ℕ)).sum (fun _ n => n) := by
    rw [h]
  rw [Finsupp.sum_add_index (by simp) (by intros; ring)] at hsum
  rw [Finsupp.sum_single_index (by rfl), Finsupp.sum_single_index (by rfl),
    Finsupp.sum_single_index (by rfl)] at hsum
  -- hsum : 1 = 1 + 1 = 2.  Contradiction.
  omega

/-- The coefficient of `X_v · X_w` (v ≠ w) in `1` is `0`. -/
theorem coeff_two_mono_one {σ : Type*} [DecidableEq σ] {R : Type*} [CommRing R]
    (v w : σ) :
    MvPolynomial.coeff (Finsupp.single v 1 + Finsupp.single w 1)
      (1 : MvPolynomial σ R) = 0 := by
  rw [MvPolynomial.coeff_one]
  exact if_neg (two_mono_ne_zero v w)

/-- The coefficient of `X_v · X_w` (v ≠ w) in `C c` is `0`. -/
theorem coeff_two_mono_C {σ : Type*} [DecidableEq σ] {R : Type*} [CommRing R]
    (v w : σ) (c : R) :
    MvPolynomial.coeff (Finsupp.single v 1 + Finsupp.single w 1)
      (MvPolynomial.C c : MvPolynomial σ R) = 0 := by
  rw [MvPolynomial.coeff_C]
  exact if_neg (two_mono_ne_zero v w)

/-- The coefficient of `X_v · X_w` (v ≠ w) in `X i * X j` (with i ≠ j):
    equals `1` iff `{i, j} = {v, w}` (as multisets), else `0`. -/
theorem coeff_two_mono_X_mul_X {σ : Type*} [DecidableEq σ] {R : Type*} [CommRing R]
    (v w i j : σ) (hvw : v ≠ w) (hij : i ≠ j) :
    MvPolynomial.coeff (Finsupp.single v 1 + Finsupp.single w 1)
      (MvPolynomial.X i * MvPolynomial.X j : MvPolynomial σ R) =
    if (Finsupp.single i 1 + Finsupp.single j 1 : σ →₀ ℕ) =
       Finsupp.single v 1 + Finsupp.single w 1 then 1 else 0 := by
  -- X i * X j = monomial (single i 1 + single j 1) 1
  have hmono : (MvPolynomial.X i * MvPolynomial.X j : MvPolynomial σ R) =
      MvPolynomial.monomial (Finsupp.single i 1 + Finsupp.single j 1) 1 := by
    show (MvPolynomial.monomial (Finsupp.single i 1) 1 *
          MvPolynomial.monomial (Finsupp.single j 1) 1 :
          MvPolynomial σ R) = _
    rw [MvPolynomial.monomial_mul, mul_one]
  rw [hmono, MvPolynomial.coeff_monomial]

/-! ## Bilinear coefficient extraction (analogue of `coeff_single_mul`) -/

/-- The fundamental bilinear-coefficient identity:
    `coeff (single v 1 + single w 1) (p * q) =
       coeff (single v 1) p · coeff (single w 1) q
       + coeff (single w 1) p · coeff (single v 1) q
       + coeff (single v 1 + single w 1) p · coeff 0 q
       + coeff 0 p · coeff (single v 1 + single w 1) q.`

    This is the bilinear analogue of `coeff_single_mul` from
    `SATDeciderGaugeKeepFirstMoves`.  The four terms come from the four
    splits of `single v 1 + single w 1` in the antidiagonal:
    `(0, vw)`, `(vw, 0)`, `(v, w)`, `(w, v)`. -/
theorem coeff_two_mono_mul {σ : Type*} [DecidableEq σ]
    {R : Type*} [CommRing R] (v w : σ) (hvw : v ≠ w)
    (p q : MvPolynomial σ R) :
    MvPolynomial.coeff (Finsupp.single v 1 + Finsupp.single w 1) (p * q) =
      MvPolynomial.coeff (Finsupp.single v 1) p *
        MvPolynomial.coeff (Finsupp.single w 1) q
      + MvPolynomial.coeff (Finsupp.single w 1) p *
        MvPolynomial.coeff (Finsupp.single v 1) q
      + MvPolynomial.coeff (Finsupp.single v 1 + Finsupp.single w 1) p *
        MvPolynomial.coeff 0 q
      + MvPolynomial.coeff 0 p *
        MvPolynomial.coeff (Finsupp.single v 1 + Finsupp.single w 1) q := by
  classical
  -- Use coeff_mul and enumerate the antidiagonal of `single v 1 + single w 1`.
  rw [MvPolynomial.coeff_mul]
  set m : σ →₀ ℕ := Finsupp.single v 1 + Finsupp.single w 1 with hm
  -- Helper: `m v = 1` and `m w = 1` and `m x = 0` for `x ≠ v, w`.
  have hmv : m v = 1 := by
    rw [hm, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply,
      if_pos rfl, if_neg hvw.symm, add_zero]
  have hmw : m w = 1 := by
    rw [hm, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply,
      if_neg hvw, if_pos rfl, zero_add]
  have hmx : ∀ x, x ≠ v → x ≠ w → m x = 0 := by
    intro x hxv hxw
    rw [hm, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply,
      if_neg (Ne.symm hxv), if_neg (Ne.symm hxw), zero_add]
  -- The antidiagonal has exactly 4 elements: (0, m), (m, 0), (sv, sw), (sw, sv).
  have hsplit :
      Finset.antidiagonal m =
        ({((0 : σ →₀ ℕ), m), (m, (0 : σ →₀ ℕ)),
          (Finsupp.single v 1, Finsupp.single w 1),
          (Finsupp.single w 1, Finsupp.single v 1)} :
            Finset ((σ →₀ ℕ) × (σ →₀ ℕ))) := by
    apply Finset.ext
    intro ⟨a, b⟩
    rw [Finset.mem_antidiagonal]
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · intro hab
      -- Pointwise: a + b = m, so a v + b v = m v = 1; a w + b w = 1;
      -- and a x + b x = 0 for x ∉ {v, w}, forcing a x = 0 = b x.
      have hav : a v + b v = 1 := by
        have := DFunLike.congr_fun hab v
        rw [Finsupp.add_apply, hmv] at this
        exact this
      have haw : a w + b w = 1 := by
        have := DFunLike.congr_fun hab w
        rw [Finsupp.add_apply, hmw] at this
        exact this
      have hax_zero : ∀ x, x ≠ v → x ≠ w → a x = 0 ∧ b x = 0 := by
        intro x hxv hxw
        have hsumx : a x + b x = 0 := by
          have := DFunLike.congr_fun hab x
          rw [Finsupp.add_apply, hmx x hxv hxw] at this
          exact this
        exact ⟨Nat.eq_zero_of_add_eq_zero_right hsumx,
          Nat.eq_zero_of_add_eq_zero_left hsumx⟩
      -- Helper: a x ≤ 1 at x = v, x = w (since a v + b v = 1 and similarly).
      have hav_le : a v ≤ 1 := by omega
      have haw_le : a w ≤ 1 := by omega
      -- Pointwise comparison helper for `Finsupp.single`.
      have hsv_v : (Finsupp.single v 1 : σ →₀ ℕ) v = 1 := by
        rw [Finsupp.single_apply, if_pos rfl]
      have hsv_w : (Finsupp.single v 1 : σ →₀ ℕ) w = 0 := by
        rw [Finsupp.single_apply, if_neg hvw]
      have hsw_v : (Finsupp.single w 1 : σ →₀ ℕ) v = 0 := by
        rw [Finsupp.single_apply, if_neg hvw.symm]
      have hsw_w : (Finsupp.single w 1 : σ →₀ ℕ) w = 1 := by
        rw [Finsupp.single_apply, if_pos rfl]
      have hsv_x : ∀ x, x ≠ v → (Finsupp.single v 1 : σ →₀ ℕ) x = 0 := by
        intro x hxv; rw [Finsupp.single_apply, if_neg (Ne.symm hxv)]
      have hsw_x : ∀ x, x ≠ w → (Finsupp.single w 1 : σ →₀ ℕ) x = 0 := by
        intro x hxw; rw [Finsupp.single_apply, if_neg (Ne.symm hxw)]
      -- Determine a v and a w.  Since a v ≤ 1, a v ∈ {0, 1}.
      rcases (show a v = 0 ∨ a v = 1 from by omega) with hav0 | hav1
      · rcases (show a w = 0 ∨ a w = 1 from by omega) with haw0 | haw1
        · -- case (0, 0): a = 0, b = m
          have hbv : b v = 1 := by omega
          have hbw : b w = 1 := by omega
          have ha0 : a = 0 := by
            ext x
            by_cases hxv : x = v
            · subst hxv; rw [Finsupp.coe_zero, Pi.zero_apply]; exact hav0
            by_cases hxw : x = w
            · subst hxw; rw [Finsupp.coe_zero, Pi.zero_apply]; exact haw0
            rw [Finsupp.coe_zero, Pi.zero_apply]
            exact (hax_zero x hxv hxw).1
          have hbm : b = m := by
            ext x
            have hsum := DFunLike.congr_fun hab x
            rw [Finsupp.add_apply, ha0] at hsum
            simpa using hsum
          left; exact ⟨ha0, hbm⟩
        · -- case (0, 1): a = single w 1, b = single v 1
          have hbv : b v = 1 := by omega
          have hbw : b w = 0 := by omega
          have ha_eq : a = Finsupp.single w 1 := by
            ext x
            by_cases hxv : x = v
            · subst hxv; rw [hsw_v]; exact hav0
            by_cases hxw : x = w
            · subst hxw; rw [hsw_w]; exact haw1
            rw [hsw_x x hxw]; exact (hax_zero x hxv hxw).1
          have hb_eq : b = Finsupp.single v 1 := by
            ext x
            by_cases hxv : x = v
            · subst hxv; rw [hsv_v]; exact hbv
            by_cases hxw : x = w
            · subst hxw; rw [hsv_w]; exact hbw
            rw [hsv_x x hxv]; exact (hax_zero x hxv hxw).2
          right; right; right; exact ⟨ha_eq, hb_eq⟩
      · rcases (show a w = 0 ∨ a w = 1 from by omega) with haw0 | haw1
        · -- case (1, 0): a = single v 1, b = single w 1
          have hbv : b v = 0 := by omega
          have hbw : b w = 1 := by omega
          have ha_eq : a = Finsupp.single v 1 := by
            ext x
            by_cases hxv : x = v
            · subst hxv; rw [hsv_v]; exact hav1
            by_cases hxw : x = w
            · subst hxw; rw [hsv_w]; exact haw0
            rw [hsv_x x hxv]; exact (hax_zero x hxv hxw).1
          have hb_eq : b = Finsupp.single w 1 := by
            ext x
            by_cases hxv : x = v
            · subst hxv; rw [hsw_v]; exact hbv
            by_cases hxw : x = w
            · subst hxw; rw [hsw_w]; exact hbw
            rw [hsw_x x hxw]; exact (hax_zero x hxv hxw).2
          right; right; left; exact ⟨ha_eq, hb_eq⟩
        · -- case (1, 1): a = m, b = 0
          have hbv : b v = 0 := by omega
          have hbw : b w = 0 := by omega
          have hb0 : b = 0 := by
            ext x
            by_cases hxv : x = v
            · subst hxv; rw [Finsupp.coe_zero, Pi.zero_apply]; exact hbv
            by_cases hxw : x = w
            · subst hxw; rw [Finsupp.coe_zero, Pi.zero_apply]; exact hbw
            rw [Finsupp.coe_zero, Pi.zero_apply]
            exact (hax_zero x hxv hxw).2
          have ha_eq : a = m := by
            ext x
            have hsum := DFunLike.congr_fun hab x
            rw [Finsupp.add_apply, hb0] at hsum
            simpa using hsum
          right; left; exact ⟨ha_eq, hb0⟩
    · -- One of the 4 cases → a + b = m
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · rw [zero_add]
      · rw [add_zero]
      · rfl
      · rw [add_comm]
  rw [hsplit]
  -- The 4 elements are pairwise distinct, so the sum has exactly 4 terms.
  have hsv_ne_zero : (Finsupp.single v 1 : σ →₀ ℕ) ≠ 0 := by
    intro h
    have := DFunLike.congr_fun h v
    rw [Finsupp.single_apply, if_pos rfl] at this
    exact one_ne_zero this
  have hsw_ne_zero : (Finsupp.single w 1 : σ →₀ ℕ) ≠ 0 := by
    intro h
    have := DFunLike.congr_fun h w
    rw [Finsupp.single_apply, if_pos rfl] at this
    exact one_ne_zero this
  have hm_ne_zero : (m : σ →₀ ℕ) ≠ 0 := by
    intro h
    have := DFunLike.congr_fun h v
    rw [hmv] at this
    exact one_ne_zero this
  have h0vw : ((0 : σ →₀ ℕ), m) ≠ (m, (0 : σ →₀ ℕ)) := by
    intro h
    exact hm_ne_zero ((Prod.mk.injEq _ _ _ _).mp h).1.symm
  have h0_sv : ((0 : σ →₀ ℕ), m) ≠ (Finsupp.single v 1, Finsupp.single w 1) := by
    intro h
    exact hsv_ne_zero ((Prod.mk.injEq _ _ _ _).mp h).1.symm
  have h0_sw : ((0 : σ →₀ ℕ), m) ≠ (Finsupp.single w 1, Finsupp.single v 1) := by
    intro h
    exact hsw_ne_zero ((Prod.mk.injEq _ _ _ _).mp h).1.symm
  have hm_sv : (m, (0 : σ →₀ ℕ)) ≠ (Finsupp.single v 1, Finsupp.single w 1) := by
    intro h
    exact hsw_ne_zero ((Prod.mk.injEq _ _ _ _).mp h).2.symm
  have hm_sw : (m, (0 : σ →₀ ℕ)) ≠ (Finsupp.single w 1, Finsupp.single v 1) := by
    intro h
    exact hsv_ne_zero ((Prod.mk.injEq _ _ _ _).mp h).2.symm
  have hvw_wv : (Finsupp.single v 1, Finsupp.single w 1) ≠
      (Finsupp.single w 1, Finsupp.single v 1) := by
    intro h
    have heq : Finsupp.single v 1 = (Finsupp.single w 1 : σ →₀ ℕ) :=
      ((Prod.mk.injEq _ _ _ _).mp h).1
    have := DFunLike.congr_fun heq v
    rw [Finsupp.single_apply, Finsupp.single_apply, if_pos rfl,
      if_neg hvw.symm] at this
    exact one_ne_zero this
  rw [show
      ({((0 : σ →₀ ℕ), m), (m, (0 : σ →₀ ℕ)),
          (Finsupp.single v 1, Finsupp.single w 1),
          (Finsupp.single w 1, Finsupp.single v 1)} :
              Finset ((σ →₀ ℕ) × (σ →₀ ℕ)))
      = insert ((0 : σ →₀ ℕ), m)
          (insert (m, (0 : σ →₀ ℕ))
            (insert (Finsupp.single v 1, Finsupp.single w 1)
              ({(Finsupp.single w 1, Finsupp.single v 1)} :
                Finset ((σ →₀ ℕ) × (σ →₀ ℕ))))) from rfl]
  rw [Finset.sum_insert (by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push_neg
    exact ⟨h0vw, h0_sv, h0_sw⟩)]
  rw [Finset.sum_insert (by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push_neg
    exact ⟨hm_sv, hm_sw⟩)]
  rw [Finset.sum_insert (by
    simp only [Finset.mem_singleton]
    exact hvw_wv)]
  rw [Finset.sum_singleton]
  ring

/-! ## Coefficient of `X_v · X_w` in `1 - X_a` and `1 - C c · X_i · X_j` -/

/-- The coefficient of `X_v · X_w` in `1 - X_a` is `0` (degree mismatch). -/
theorem coeff_two_mono_one_sub_X {σ : Type*} [DecidableEq σ]
    {R : Type*} [CommRing R] (v w a : σ) (hvw : v ≠ w) :
    MvPolynomial.coeff (Finsupp.single v 1 + Finsupp.single w 1)
      ((1 : MvPolynomial σ R) - MvPolynomial.X a) = 0 := by
  rw [MvPolynomial.coeff_sub, coeff_two_mono_one v w, coeff_two_mono_X v w a hvw,
    sub_self]

/-- Coefficient of the multilinear monomial `X_v · X_w` in `1 - C c · X_i · X_j`:
    equals `-c` if `{i, j} = {v, w}` (as the multilinear monomial), else `0`. -/
theorem coeff_two_mono_one_sub_C_X_mul_X {σ : Type*} [DecidableEq σ]
    {R : Type*} [CommRing R] (v w i j : σ) (hvw : v ≠ w) (hij : i ≠ j) (c : R) :
    MvPolynomial.coeff (Finsupp.single v 1 + Finsupp.single w 1)
      ((1 : MvPolynomial σ R) -
        MvPolynomial.C c * (MvPolynomial.X i * MvPolynomial.X j)) =
      - (if (Finsupp.single i 1 + Finsupp.single j 1 : σ →₀ ℕ) =
           Finsupp.single v 1 + Finsupp.single w 1 then c else 0) := by
  rw [MvPolynomial.coeff_sub, coeff_two_mono_one v w]
  rw [MvPolynomial.coeff_C_mul, coeff_two_mono_X_mul_X v w i j hvw hij]
  split_ifs with h
  · simp
  · simp

/-! ## Boolean factor `1 - X_v(1 - X_v) = boolFactor` coefficients -/

/-- The two-variable monomial coefficient `coeff (X_a X_b) (1 - boolLC.poly) = 0`,
    since `1 - X_v(1 - X_v) = 1 - X_v + X_v^2` only contributes constant,
    linear, and degree-2 self-monomials, never `X_a X_b` for distinct vars. -/
theorem coeff_two_mono_boolLC_factor {n : ℕ} (a b w : Fin n) (hab : a ≠ b) :
    MvPolynomial.coeff (Finsupp.single a 1 + Finsupp.single b 1)
      ((1 : MvPolynomial (Fin n) ℚ) - (boolLC n w).poly) = 0 := by
  rw [CompiledBoolFactorBridge.boolConstraint_factor_eq_boolFactor]
  -- boolFactor n w = 1 - X w * (1 - X w) = 1 - X w + X w * X w
  unfold SymmetricPower.boolFactor
  -- 1 - X_w(1 - X_w) = 1 - X_w + X_w^2.
  -- The monomials are `0`, `single w 1`, `single w 2`.  None equals
  -- `single a 1 + single b 1` because that has nonzero values at *both*
  -- `a` and `b`, while a power of `single w` only has nonzero values at
  -- one variable.
  have hexpand :
      (1 : MvPolynomial (Fin n) ℚ) - MvPolynomial.X w * (1 - MvPolynomial.X w) =
        (1 : MvPolynomial (Fin n) ℚ) - MvPolynomial.X w +
          MvPolynomial.X w * MvPolynomial.X w := by ring
  rw [hexpand, MvPolynomial.coeff_add]
  rw [MvPolynomial.coeff_sub, coeff_two_mono_one a b, coeff_two_mono_X a b w hab,
    sub_self, zero_add]
  -- Remaining: coeff (single a 1 + single b 1) (X w * X w) = 0
  -- X w * X w = monomial (single w 2) 1.
  have hsq : (MvPolynomial.X w * MvPolynomial.X w : MvPolynomial (Fin n) ℚ) =
      MvPolynomial.monomial (Finsupp.single w 2) 1 := by
    show (MvPolynomial.monomial (Finsupp.single w 1) 1 *
          MvPolynomial.monomial (Finsupp.single w 1) 1 :
          MvPolynomial (Fin n) ℚ) = _
    rw [MvPolynomial.monomial_mul, mul_one]
    have : Finsupp.single w 1 + Finsupp.single w 1 = (Finsupp.single w 2 : Fin n →₀ ℕ) := by
      ext i; by_cases hi : i = w
      · subst hi; simp
      · simp [Finsupp.single_apply, Ne.symm hi]
    rw [this]
  rw [hsq, MvPolynomial.coeff_monomial]
  rw [if_neg]
  -- Show single w 2 ≠ single a 1 + single b 1.  At i = a, the value
  -- `single w 2 a` is either 2 (if w = a) or 0 (if w ≠ a), but
  -- `(single a 1 + single b 1) a = 1`.  Either way, a contradiction.
  intro h
  have ha := DFunLike.congr_fun h a
  rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply,
    Finsupp.single_apply, if_pos rfl, if_neg hab.symm, add_zero] at ha
  -- ha : (if w = a then 2 else 0) = 1
  by_cases hwa : w = a
  · rw [if_pos hwa] at ha; omega
  · rw [if_neg hwa] at ha; omega

/-- Coefficient of `X_a · X_b` in `pderiv v (1 - boolLC.poly)`.
    `pderiv v (1 - X_v(1 - X_v)) = 2 X_v - 1` (a degree-1 polynomial), so
    coefficient at any 2-variable multilinear monomial is `0`.  When
    `pderiv v` is on a different variable `w ≠ v`, the result is
    `(1 - boolLC w.poly)`'s pderiv evaluated at `v`, which is 0 if
    `w ≠ v`. -/
theorem coeff_two_mono_pderiv_boolLC_factor {n : ℕ} (a b v w : Fin n) (hab : a ≠ b) :
    MvPolynomial.coeff (Finsupp.single a 1 + Finsupp.single b 1)
      (MvPolynomial.pderiv v
        ((1 : MvPolynomial (Fin n) ℚ) - (boolLC n w).poly)) = 0 := by
  rw [CompiledBoolFactorBridge.boolConstraint_factor_eq_boolFactor]
  by_cases hvw : v = w
  · subst hvw
    -- pderiv v (boolFactor n v) = -1 + 2 X v.
    rw [SymmetricPower.pderiv_boolFactor_self n v]
    rw [MvPolynomial.coeff_add, MvPolynomial.coeff_neg, MvPolynomial.coeff_one,
      if_neg (two_mono_ne_zero a b)]
    -- Now: 0 + coeff (single a 1 + single b 1) (2 * X v) = 0
    have h2X : (2 * MvPolynomial.X v : MvPolynomial (Fin n) ℚ) =
        MvPolynomial.C 2 * MvPolynomial.X v := by
      rw [show ((2 : MvPolynomial (Fin n) ℚ)) = MvPolynomial.C ((2 : ℚ)) from by
            simp [map_ofNat]]
    rw [h2X, MvPolynomial.coeff_C_mul, coeff_two_mono_X a b v hab]
    simp
  · rw [SymmetricPower.pderiv_boolFactor_of_ne n v w hvw]
    simp

/-! ## Adjacency factor `1 - C c · X_i · X_j` derivative coefficients -/

/-- The Leibniz expansion of `pderiv s (C c * (X i * X j))` (reused from
    `BridgeABlockEvalAtZero`). -/
private theorem pderiv_C_mul_X_mul_X {n : ℕ} (c : ℚ) (i j s : Fin n) :
    MvPolynomial.pderiv s
        (MvPolynomial.C c * (MvPolynomial.X i * MvPolynomial.X j) :
          MvPolynomial (Fin n) ℚ) =
      MvPolynomial.C c *
        (((if s = i then (1 : MvPolynomial (Fin n) ℚ) else 0) *
            MvPolynomial.X j) +
          (MvPolynomial.X i * (if s = j then 1 else 0))) := by
  rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C, zero_mul, zero_add,
    MvPolynomial.pderiv_mul]
  simp only [MvPolynomial.pderiv_X, Pi.single_apply, @eq_comm _ s]

/-- Coefficient of `X_a · X_b` in `pderiv v (1 - C c · X_i · X_j)`.
    Since the inner polynomial after `pderiv v` is at most degree 1 in
    each remaining variable (one of `X i` or `X j` survives), the
    coefficient at a 2-variable multilinear monomial is `0`. -/
theorem coeff_two_mono_pderiv_cadj_factor {n : ℕ}
    (a b v i j : Fin n) (hab : a ≠ b) (c : ℚ) :
    MvPolynomial.coeff (Finsupp.single a 1 + Finsupp.single b 1)
      (MvPolynomial.pderiv v
        ((1 : MvPolynomial (Fin n) ℚ) -
          MvPolynomial.C c * (MvPolynomial.X i * MvPolynomial.X j))) = 0 := by
  rw [map_sub, MvPolynomial.pderiv_one, zero_sub]
  rw [pderiv_C_mul_X_mul_X]
  rw [MvPolynomial.coeff_neg, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_add]
  -- Both summands are products of the form `(if · then 1 else 0) * X _` whose
  -- multilinear two-variable coefficient is 0.
  have h1 :
      MvPolynomial.coeff (Finsupp.single a 1 + Finsupp.single b 1)
        (((if v = i then (1 : MvPolynomial (Fin n) ℚ) else 0) *
            MvPolynomial.X j) :
          MvPolynomial (Fin n) ℚ) = 0 := by
    by_cases hvi : v = i
    · simp only [if_pos hvi, one_mul]
      exact coeff_two_mono_X a b j hab
    · simp [if_neg hvi]
  have h2 :
      MvPolynomial.coeff (Finsupp.single a 1 + Finsupp.single b 1)
        ((MvPolynomial.X i * (if v = j then (1 : MvPolynomial (Fin n) ℚ) else 0)) :
          MvPolynomial (Fin n) ℚ) = 0 := by
    by_cases hvj : v = j
    · simp only [if_pos hvj, mul_one]
      exact coeff_two_mono_X a b i hab
    · simp [if_neg hvj]
  rw [h1, h2, add_zero, mul_zero, neg_zero]

/-! ## Path expansion of `coeff (X_v · X_w) (List.prod fs)`

This is the bilinear analog of
`ListProdDerivativeConstantCoeff.coeff_zero_pderiv_list_prod_eq_sum_deriv_coeff`.
-/

/--
Kernel-only path expansion of `coeff (X_v X_w) fs.prod` by
induction on `fs` (no aggregate index sums needed at this layer).

For a cons `p :: ps` with `coeff 0 p = 1` and all factors of `ps` having
constant term `1`,

  `coeff (X_v X_w) ((p :: ps).prod)
    = coeff (X_v) p · coeff (X_w) ps.prod
      + coeff (X_w) p · coeff (X_v) ps.prod
      + coeff (X_v X_w) p
      + coeff (X_v X_w) ps.prod.`

This is the bilinear analogue of `coeff_zero_pderiv_list_prod_eq_sum_deriv_coeff`'s
inductive step. -/
theorem coeff_two_mono_list_prod_cons {N : ℕ} (v w : Fin N) (hvw : v ≠ w)
    (p : MvPolynomial (Fin N) ℚ) (ps : List (MvPolynomial (Fin N) ℚ))
    (hp_const : MvPolynomial.coeff 0 p = 1)
    (hps_const : ∀ q, q ∈ ps → MvPolynomial.coeff 0 q = 1) :
    MvPolynomial.coeff (Finsupp.single v 1 + Finsupp.single w 1) (p :: ps).prod =
      MvPolynomial.coeff (Finsupp.single v 1) p *
        MvPolynomial.coeff (Finsupp.single w 1) ps.prod
      + MvPolynomial.coeff (Finsupp.single w 1) p *
        MvPolynomial.coeff (Finsupp.single v 1) ps.prod
      + MvPolynomial.coeff (Finsupp.single v 1 + Finsupp.single w 1) p
      + MvPolynomial.coeff (Finsupp.single v 1 + Finsupp.single w 1) ps.prod := by
  rw [List.prod_cons, coeff_two_mono_mul v w hvw]
  -- coeff 0 ps.prod = 1 since each factor has coeff 0 = 1
  have hpsprod :
      MvPolynomial.coeff 0 ps.prod = 1 :=
    ListProdDerivativeConstantCoeff.coeff_zero_list_prod_eq_one_of_forall ps hps_const
  rw [hpsprod, hp_const, mul_one, one_mul]

/-! ## Multilinear projection compatibility -/

/-- The coefficient at a multilinear monomial passes through `mlProj`. -/
theorem coeff_two_mono_mlProj_eq {N : ℕ} (v w : Fin N) (hvw : v ≠ w)
    (p : MvPolynomial (Fin N) ℚ) :
    MvPolynomial.coeff (Finsupp.single v 1 + Finsupp.single w 1) (mlProj p) =
      MvPolynomial.coeff (Finsupp.single v 1 + Finsupp.single w 1) p :=
  coeff_mlProj_of_isMultilinear_mono p _
    (isMultilinear_single_add_single v w hvw)

/-! ## Cook-Levin specialisation: every constraint factor's `X_a X_b` coefficient -/

/-- For *every* factor in the Cook-Levin compilation list (booleanity,
    adjacency, transition-skeleton), the coefficient of any multilinear
    two-variable monomial `X_a · X_b` in `1 - lc.poly` equals what we
    compute via `coeff_two_mono_one_sub_C_X_mul_X` (for non-bool factors)
    and is `0` for booleanity factors. -/
theorem coeff_two_mono_cookLevin_factor {n : ℕ} (M : TuringMachine.DTM)
    (a b : Fin n) (hab : a ≠ b) (lc : LocalConstraint n)
    (hn : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hlc : lc ∈ (cook_levin_compilation M n hn htb hns).constraints) :
    -- Either it is a booleanity factor (coeff = 0) or
    -- it is an adjacency / transition factor with the cadj form.
    MvPolynomial.coeff (Finsupp.single a 1 + Finsupp.single b 1)
      ((1 : MvPolynomial (Fin n) ℚ) - lc.poly) = 0 ∨
    ∃ (c : ℚ) (i : Fin n) (hi : i.val + 1 < n),
      MvPolynomial.coeff (Finsupp.single a 1 + Finsupp.single b 1)
        ((1 : MvPolynomial (Fin n) ℚ) - lc.poly) =
      - (if (Finsupp.single i 1 + Finsupp.single ⟨i.val + 1, hi⟩ 1 :
              Fin n →₀ ℕ) =
            Finsupp.single a 1 + Finsupp.single b 1 then c else 0) := by
  rw [cook_levin_constraints_split M n hn htb hns] at hlc
  rw [List.mem_append] at hlc
  rcases hlc with hlc | hlc
  · rw [List.mem_append] at hlc
    rcases hlc with hlc | hlc
    · -- Booleanity factor case: coefficient is `0`.
      left
      unfold boolConstraintList at hlc
      rw [List.mem_map] at hlc
      obtain ⟨w, _hw, rfl⟩ := hlc
      exact coeff_two_mono_boolLC_factor a b w hab
    · -- Adjacency factor case
      right
      obtain ⟨c, i, hi, hpoly⟩ := rest_constraint_cadj_form M n lc
        (List.mem_append.mpr (Or.inl hlc))
      -- need i.val + 1 ≠ i for hij (since adjacency is between i and i+1)
      have hij : i ≠ ⟨i.val + 1, hi⟩ := by
        intro h
        have := congr_arg Fin.val h
        simp at this
      refine ⟨c, i, hi, ?_⟩
      rw [hpoly]
      exact coeff_two_mono_one_sub_C_X_mul_X a b i ⟨i.val + 1, hi⟩ hab hij c
  · -- Transition-skeleton factor case
    right
    obtain ⟨c, i, hi, hpoly⟩ := rest_constraint_cadj_form M n lc
      (List.mem_append.mpr (Or.inr hlc))
    have hij : i ≠ ⟨i.val + 1, hi⟩ := by
      intro h
      have := congr_arg Fin.val h
      simp at this
    refine ⟨c, i, hi, ?_⟩
    rw [hpoly]
    exact coeff_two_mono_one_sub_C_X_mul_X a b i ⟨i.val + 1, hi⟩ hab hij c

/-! ## Single-variable coefficient of `1 - boolLC.poly` and `1 - C c · X_i · X_j` -/

/-- The single-variable coefficient `coeff (X_a) (1 - boolLC w.poly)`:
    `-1` if `a = w`, else `0`.  Used as building block for the bilinear
    expansion when one factor is the booleanity factor. -/
theorem coeff_X_a_one_sub_boolLC {n : ℕ} (a w : Fin n) :
    MvPolynomial.coeff (Finsupp.single a 1)
      ((1 : MvPolynomial (Fin n) ℚ) - (boolLC n w).poly) =
      (if a = w then (-1 : ℚ) else 0) := by
  rw [CompiledBoolFactorBridge.boolConstraint_factor_eq_boolFactor]
  unfold SymmetricPower.boolFactor
  -- 1 - X w * (1 - X w) = 1 - X w + X w^2
  have hexpand :
      (1 : MvPolynomial (Fin n) ℚ) - MvPolynomial.X w * (1 - MvPolynomial.X w) =
        (1 : MvPolynomial (Fin n) ℚ) - MvPolynomial.X w +
          MvPolynomial.X w * MvPolynomial.X w := by ring
  rw [hexpand]
  rw [MvPolynomial.coeff_add, MvPolynomial.coeff_sub, MvPolynomial.coeff_one,
    MvPolynomial.coeff_X']
  -- coeff (single a 1) of (1 - X w + X w^2):
  -- coeff (single a 1) 1 = 0 (since single a 1 ≠ 0)
  -- coeff (single a 1) (X w) = if single w 1 = single a 1 then 1 else 0
  -- coeff (single a 1) (X w * X w) = 0 (degree 2 monomial is single w 2)
  have hne0 : (0 : Fin n →₀ ℕ) ≠ Finsupp.single a 1 := by
    intro h
    have := DFunLike.congr_fun h a
    simp at this
  rw [if_neg hne0]
  have hsq : (MvPolynomial.X w * MvPolynomial.X w : MvPolynomial (Fin n) ℚ) =
      MvPolynomial.monomial (Finsupp.single w 2) 1 := by
    show (MvPolynomial.monomial (Finsupp.single w 1) 1 *
          MvPolynomial.monomial (Finsupp.single w 1) 1 :
          MvPolynomial (Fin n) ℚ) = _
    rw [MvPolynomial.monomial_mul, mul_one]
    have : Finsupp.single w 1 + Finsupp.single w 1 = (Finsupp.single w 2 : Fin n →₀ ℕ) := by
      ext i; by_cases hi : i = w
      · subst hi; simp
      · simp [Finsupp.single_apply, Ne.symm hi]
    rw [this]
  rw [hsq, MvPolynomial.coeff_monomial]
  -- Goal:  0 - (if single w 1 = single a 1 then 1 else 0)
  --        + (if single w 2 = single a 1 then 1 else 0)
  --      = if a = w then -1 else 0
  -- The (single w 2 = single a 1) branch is always false.
  rw [if_neg (show (Finsupp.single w 2 : Fin n →₀ ℕ) ≠ Finsupp.single a 1 by
    intro h
    have := DFunLike.congr_fun h w
    rw [Finsupp.single_apply, Finsupp.single_apply, if_pos rfl] at this
    -- this : 2 = if a = w then 1 else 0; impossible
    by_cases haw : a = w
    · rw [if_pos haw] at this; omega
    · rw [if_neg haw] at this; omega), add_zero]
  -- Now: 0 - (if single w 1 = single a 1 then 1 else 0) = if a = w then -1 else 0
  by_cases haw : a = w
  · subst haw
    -- single w 1 = single w 1 is true, so coeff = 1, then 0 - 1 = -1, RHS = -1.
    rw [if_pos rfl, if_pos rfl]; ring
  · -- single w 1 ≠ single a 1, so coeff = 0; LHS = 0, RHS = 0.
    have hne : (Finsupp.single w 1 : Fin n →₀ ℕ) ≠ Finsupp.single a 1 := by
      intro h
      have := DFunLike.congr_fun h a
      rw [Finsupp.single_apply, Finsupp.single_apply, if_pos rfl,
        if_neg (fun heq => haw heq.symm)] at this
      exact zero_ne_one this
    rw [if_neg hne, if_neg haw]; ring

/-- The single-variable coefficient `coeff (X_a) (1 - C c · X_i · X_j) = 0`,
    since the polynomial is `1` minus a degree-2 monomial. -/
theorem coeff_X_a_one_sub_C_X_mul_X {n : ℕ} (a i j : Fin n) (hij : i ≠ j) (c : ℚ) :
    MvPolynomial.coeff (Finsupp.single a 1)
      ((1 : MvPolynomial (Fin n) ℚ) -
        MvPolynomial.C c * (MvPolynomial.X i * MvPolynomial.X j)) = 0 := by
  rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_one]
  have hne0 : (0 : Fin n →₀ ℕ) ≠ Finsupp.single a 1 := by
    intro h
    have := DFunLike.congr_fun h a
    simp at this
  rw [if_neg hne0, zero_sub, MvPolynomial.coeff_C_mul]
  -- coeff (single a 1) (X i * X j) = 0 since X i * X j is the
  -- monomial single i 1 + single j 1 ≠ single a 1.
  have hmono : (MvPolynomial.X i * MvPolynomial.X j : MvPolynomial (Fin n) ℚ) =
      MvPolynomial.monomial (Finsupp.single i 1 + Finsupp.single j 1) 1 := by
    show (MvPolynomial.monomial (Finsupp.single i 1) 1 *
          MvPolynomial.monomial (Finsupp.single j 1) 1 :
          MvPolynomial (Fin n) ℚ) = _
    rw [MvPolynomial.monomial_mul, mul_one]
  rw [hmono, MvPolynomial.coeff_monomial]
  rw [if_neg]
  · simp
  · -- single i 1 + single j 1 ≠ single a 1
    intro h
    have hi_eq := DFunLike.congr_fun h i
    have hj_eq := DFunLike.congr_fun h j
    simp [Finsupp.single_apply, Finsupp.add_apply, hij, hij.symm] at hi_eq hj_eq
    by_cases hai : a = i
    · subst hai
      -- hj : 1 = if a = j then 1 else 0... no wait we need to read carefully.
      -- hi_eq says (1 + (if j = i then 1 else 0)) = (if a = i then 1 else 0)
      -- with hij and hai = (a=i):  LHS = 1, RHS = 1 OK
      -- hj_eq says (if i = j then 1 else 0) + 1 = (if a = j then 1 else 0)
      -- with hij: LHS = 1, hai means a = i, so a = j iff i = j iff false. RHS = 0.
      simp [hij] at hj_eq
    · -- hi_eq says 1 + 0 = 0, contradiction
      simp [hij.symm, hai] at hi_eq

/-! ## Single-variable derivative coefficients of factors -/

/-- Coefficient of `X_a` in `pderiv v (1 - boolLC.poly)`:
    The derivative `pderiv v (1 - boolFactor v) = 2 X_v - 1` (when `v = w`)
    or `0` (when `v ≠ w`).  At the multilinear monomial `single a 1`:
    `2` if `v = w = a`, else `0` (when `v = w` and `a ≠ v`),
    or `0` (when `v ≠ w`). -/
theorem coeff_X_a_pderiv_v_boolLC_factor {n : ℕ} (a v w : Fin n) :
    MvPolynomial.coeff (Finsupp.single a 1)
      (MvPolynomial.pderiv v
        ((1 : MvPolynomial (Fin n) ℚ) - (boolLC n w).poly)) =
      (if v = w ∧ a = v then (2 : ℚ) else 0) := by
  rw [CompiledBoolFactorBridge.boolConstraint_factor_eq_boolFactor]
  by_cases hvw : v = w
  · subst hvw
    rw [SymmetricPower.pderiv_boolFactor_self n v]
    -- coeff (single a 1) (-1 + 2 * X v)
    rw [MvPolynomial.coeff_add, MvPolynomial.coeff_neg, MvPolynomial.coeff_one]
    have hne0 : (0 : Fin n →₀ ℕ) ≠ Finsupp.single a 1 := by
      intro h
      have := DFunLike.congr_fun h a
      simp at this
    rw [if_neg hne0]
    rw [show (2 * MvPolynomial.X v : MvPolynomial (Fin n) ℚ) =
        MvPolynomial.C 2 * MvPolynomial.X v from by
          rw [show ((2 : MvPolynomial (Fin n) ℚ)) = MvPolynomial.C ((2 : ℚ)) from by
                simp [map_ofNat]]]
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X']
    by_cases hav : a = v
    · subst hav; simp [Finsupp.single_apply]
    · have hsv_ne : (Finsupp.single v 1 : Fin n →₀ ℕ) ≠ Finsupp.single a 1 := by
        intro h
        have := DFunLike.congr_fun h a
        simp [Finsupp.single_apply, Ne.symm hav] at this
      rw [if_neg hsv_ne]
      simp [hav]
  · rw [SymmetricPower.pderiv_boolFactor_of_ne n v w hvw]
    simp [hvw]

/-- Coefficient of `X_a` in `pderiv v (1 - C c · X_i · X_j)`:
    Since `pderiv v (X i · X j) = δ_{vi} X_j + δ_{vj} X_i`, we pick up
    `-c` if `v = i` and `a = j`, or `v = j` and `a = i` (and 0 otherwise). -/
theorem coeff_X_a_pderiv_v_cadj_factor {n : ℕ}
    (a v i j : Fin n) (hij : i ≠ j) (c : ℚ) :
    MvPolynomial.coeff (Finsupp.single a 1)
      (MvPolynomial.pderiv v
        ((1 : MvPolynomial (Fin n) ℚ) -
          MvPolynomial.C c * (MvPolynomial.X i * MvPolynomial.X j))) =
      - c * ((if v = i ∧ a = j then (1 : ℚ) else 0) +
             (if v = j ∧ a = i then (1 : ℚ) else 0)) := by
  rw [map_sub, MvPolynomial.pderiv_one, zero_sub]
  rw [pderiv_C_mul_X_mul_X]
  rw [MvPolynomial.coeff_neg, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_add]
  -- Goal: -(c * (coeff (sa1) ((if v=i then 1 else 0) * X j) +
  --             coeff (sa1) (X i * (if v=j then 1 else 0))))
  --    = -c * ((if v=i ∧ a=j then 1 else 0) + (if v=j ∧ a=i then 1 else 0))
  rw [show ((if v = i then (1 : MvPolynomial (Fin n) ℚ) else 0) * MvPolynomial.X j)
        = if v = i then MvPolynomial.X j else 0 by split_ifs <;> simp]
  rw [show (MvPolynomial.X i * (if v = j then (1 : MvPolynomial (Fin n) ℚ) else 0))
        = if v = j then MvPolynomial.X i else 0 by split_ifs <;> simp]
  -- Compute the two summand coefficients explicitly.
  have hX_aj : MvPolynomial.coeff (Finsupp.single a 1)
      ((if v = i then MvPolynomial.X j else 0 : MvPolynomial (Fin n) ℚ)) =
        if v = i ∧ a = j then (1 : ℚ) else 0 := by
    by_cases hvi : v = i
    · rw [if_pos hvi, MvPolynomial.coeff_X']
      by_cases haj : a = j
      · subst haj
        rw [if_pos rfl, if_pos ⟨hvi, rfl⟩]
      · have hne : (Finsupp.single j 1 : Fin n →₀ ℕ) ≠ Finsupp.single a 1 := by
          intro h
          have := DFunLike.congr_fun h a
          rw [Finsupp.single_apply, Finsupp.single_apply, if_neg (Ne.symm haj),
            if_pos rfl] at this
          exact zero_ne_one this
        rw [if_neg hne, if_neg]
        rintro ⟨_, hh⟩; exact haj hh
    · rw [if_neg hvi, MvPolynomial.coeff_zero, if_neg]
      rintro ⟨hh, _⟩; exact hvi hh
  have hX_ai : MvPolynomial.coeff (Finsupp.single a 1)
      ((if v = j then MvPolynomial.X i else 0 : MvPolynomial (Fin n) ℚ)) =
        if v = j ∧ a = i then (1 : ℚ) else 0 := by
    by_cases hvj : v = j
    · rw [if_pos hvj, MvPolynomial.coeff_X']
      by_cases hai : a = i
      · subst hai
        rw [if_pos rfl, if_pos ⟨hvj, rfl⟩]
      · have hne : (Finsupp.single i 1 : Fin n →₀ ℕ) ≠ Finsupp.single a 1 := by
          intro h
          have := DFunLike.congr_fun h a
          rw [Finsupp.single_apply, Finsupp.single_apply, if_neg (Ne.symm hai),
            if_pos rfl] at this
          exact zero_ne_one this
        rw [if_neg hne, if_neg]
        rintro ⟨_, hh⟩; exact hai hh
    · rw [if_neg hvj, MvPolynomial.coeff_zero, if_neg]
      rintro ⟨hh, _⟩; exact hvj hh
  rw [hX_aj, hX_ai]
  ring

/-! ## Axiom audit anchors -/

#print axioms isMultilinear_single_add_single
#print axioms two_mono_ne_zero
#print axioms coeff_two_mono_X
#print axioms coeff_two_mono_one
#print axioms coeff_two_mono_C
#print axioms coeff_two_mono_X_mul_X
#print axioms coeff_two_mono_mul
#print axioms coeff_two_mono_one_sub_X
#print axioms coeff_two_mono_one_sub_C_X_mul_X
#print axioms coeff_two_mono_boolLC_factor
#print axioms coeff_two_mono_pderiv_boolLC_factor
#print axioms coeff_two_mono_pderiv_cadj_factor
#print axioms coeff_two_mono_list_prod_cons
#print axioms coeff_two_mono_mlProj_eq
#print axioms coeff_two_mono_cookLevin_factor
#print axioms coeff_X_a_one_sub_boolLC
#print axioms coeff_X_a_one_sub_C_X_mul_X
#print axioms coeff_X_a_pderiv_v_boolLC_factor
#print axioms coeff_X_a_pderiv_v_cadj_factor

end MultilinearCoefficientInfrastructure

end PallLean.Paper93.Paper283
