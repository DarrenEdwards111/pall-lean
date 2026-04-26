import PallLean.MultilinearSPDP
import PallLean.SymmetricPower
import Mathlib.Tactic

/-!
# Multilinear projection of a degree-1 polynomial is nonzero

This file is a Bridge A κ=1 supporting lemma.

For each `n : ℕ` with `0 < n` and each variable `v : Fin n`, the polynomial
`2 * X_v - 1 : MvPolynomial (Fin n) ℚ` is multilinear (every variable has
degree at most 1). Hence `mlProj` (the multilinear projection from
`PallLean.MultilinearSPDP`) acts as the identity on it. Since the coefficient
of `X_v` (i.e. of the monomial `Finsupp.single v 1`) is `2 ≠ 0`, the
projection is nonzero.

We prove three layers:

* `mlProj_X` is reused from `PallLean.SymmetricPower` (`mlProj` fixes `X v`),
* `mlProj_one` shows `mlProj` fixes the constant polynomial `1`,
* `mlProj_two_X_sub_one` and `mlProj_two_X_sub_one_ne_zero` give the headline
  lemmas used in the Bridge A κ=1 chain.

The proofs are constructive computations using `mlProj_add`, `mlProj_smul`,
`mlProj_neg_helper`-style negation (here built from the additive hom
`mlProjHom`), and the existing `mlProj_X` lemma.
-/

namespace PallLean.Paper93.Paper283

open MvPolynomial MultilinearSPDP SymmetricPower

attribute [local instance] Classical.dec

/-- `Finsupp.IsMultilinear` holds for the zero finsupp. -/
private theorem isMultilinear_zero_finsupp {σ : Type*} :
    Finsupp.IsMultilinear (0 : σ →₀ ℕ) := by
  intro i; simp

/-- `mlProj` fixes the constant polynomial `1`.
    Since `1 = monomial 0 1` and `0` is the multilinear zero finsupp. -/
theorem mlProj_one (n : ℕ) :
    mlProj (1 : MvPolynomial (Fin n) ℚ) = (1 : MvPolynomial (Fin n) ℚ) := by
  -- Rewrite `1` as `monomial 0 1` and use `mlProj_monomial`
  have h1 : (1 : MvPolynomial (Fin n) ℚ) =
      MvPolynomial.monomial (0 : Fin n →₀ ℕ) (1 : ℚ) := by
    rw [MvPolynomial.monomial_zero']; rfl
  rw [h1, mlProj_monomial]
  exact if_pos isMultilinear_zero_finsupp

/-- `mlProj` fixes constants `C c`.
    Since `C c = monomial 0 c` and `0` is multilinear. -/
theorem mlProj_C (n : ℕ) (c : ℚ) :
    mlProj (MvPolynomial.C c : MvPolynomial (Fin n) ℚ) =
      MvPolynomial.C c := by
  have hC : (MvPolynomial.C c : MvPolynomial (Fin n) ℚ) =
      MvPolynomial.monomial (0 : Fin n →₀ ℕ) c := by
    rw [← MvPolynomial.monomial_zero']
  rw [hC, mlProj_monomial]
  exact if_pos isMultilinear_zero_finsupp

/-- `mlProj` is compatible with subtraction (it is an additive hom). -/
private theorem mlProj_sub_helper (n : ℕ)
    (p q : MvPolynomial (Fin n) ℚ) :
    mlProj (p - q) = mlProj p - mlProj q := by
  change (mlProjHom ℚ) (p - q) = (mlProjHom ℚ) p - (mlProjHom ℚ) q
  exact map_sub _ p q

/-- `mlProj` fixes the polynomial `2 * X_v - 1`.
    Since `2 * X_v - 1` is multilinear (linear in `X_v` and constant otherwise).

    We compute it concretely using `mlProj_add` / `mlProj_sub_helper` and the
    existing `mlProj_X` lemma, plus `mlProj_one`. -/
theorem mlProj_two_X_sub_one (n : ℕ) (v : Fin n) :
    mlProj ((2 : MvPolynomial (Fin n) ℚ) * MvPolynomial.X v - 1) =
      (2 : MvPolynomial (Fin n) ℚ) * MvPolynomial.X v - 1 := by
  -- mlProj is an additive hom; rewrite 2 * X v as (2 : ℚ) • X v
  have h2X : (2 : MvPolynomial (Fin n) ℚ) * MvPolynomial.X v =
      (2 : ℚ) • (MvPolynomial.X v : MvPolynomial (Fin n) ℚ) := by
    -- 2 in MvPolynomial = C 2; C c * p = c • p
    rw [show ((2 : MvPolynomial (Fin n) ℚ)) = MvPolynomial.C ((2 : ℚ)) from by
          simp [map_ofNat]]
    rw [MvPolynomial.C_mul']
  rw [h2X]
  -- mlProj((2 : ℚ) • X v - 1) = (2 : ℚ) • mlProj(X v) - mlProj(1)
  rw [mlProj_sub_helper, mlProj_smul, SymmetricPower.mlProj_X v, mlProj_one]

/-- The headline lemma:
    `mlProj (2 * X_v - 1) ≠ 0` for any positive arity `n` and variable `v`.

    This is the supporting lemma for the Bridge A κ=1 chain: at each compiled
    vertex `v`, the booleanity-factor derivative is `2 * X_v - 1`, and its
    multilinear projection is itself, which is nonzero (it has the monomial
    `X_v` with coefficient `2`). -/
theorem mlProj_two_X_sub_one_ne_zero (n : ℕ) (v : Fin n) (_hn : 0 < n) :
    mlProj ((2 : MvPolynomial (Fin n) ℚ) * MvPolynomial.X v - 1) ≠ 0 := by
  -- mlProj fixes 2 * X v - 1; reduce to: 2 * X v - 1 ≠ 0.
  rw [mlProj_two_X_sub_one n v]
  -- Show coefficient at α = single v 1 of (2*X_v - 1) is 2 ≠ 0.
  intro h0
  have hcoeff : MvPolynomial.coeff (Finsupp.single v 1)
      ((2 : MvPolynomial (Fin n) ℚ) * MvPolynomial.X v - 1) = 0 := by
    rw [h0]; simp
  -- But the coefficient should be 2.
  have hval : MvPolynomial.coeff (Finsupp.single v 1)
      ((2 : MvPolynomial (Fin n) ℚ) * MvPolynomial.X v - 1) = (2 : ℚ) := by
    -- 2 * X v = monomial (single v 1) 2; (1) has coeff 0 at single v 1.
    rw [MvPolynomial.coeff_sub]
    have h2X : (2 : MvPolynomial (Fin n) ℚ) * MvPolynomial.X v =
        MvPolynomial.monomial (Finsupp.single v 1) (2 : ℚ) := by
      rw [show ((2 : MvPolynomial (Fin n) ℚ)) = MvPolynomial.C ((2 : ℚ)) from by
            simp [map_ofNat]]
      rw [MvPolynomial.C_mul_X_eq_monomial]
    rw [h2X, MvPolynomial.coeff_monomial, if_pos rfl]
    -- coeff (single v 1) (1 : MvPolynomial) = 0 since 0 ≠ single v 1
    have hne : (0 : Fin n →₀ ℕ) ≠ Finsupp.single v 1 := by
      intro he
      have := congr_arg (fun f => f v) he
      simp at this
    rw [MvPolynomial.coeff_one, if_neg hne, sub_zero]
  -- 2 = 0 contradiction
  rw [hval] at hcoeff
  norm_num at hcoeff

end PallLean.Paper93.Paper283
