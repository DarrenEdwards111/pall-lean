import PallLean.MultilinearSPDP
import PallLean.SymmetricPower
import Mathlib.Tactic

/-!
# MlProjFar — Spanning set for mlProj generators (locality argument)

Key theorem: if `mlProj(m * ∂^S p)` has vars ⊆ V, then it lies in
the span of multilinear monomials on V. The set of such monomials
has cardinality ≤ 2^|V|.

Combined with `near_vars_bounded` (each admissible S gives |V| ≤ 155κ),
this gives ≤ 2^{155κ} independent generators per window.
-/

namespace MlProjFar

open SPDP MultilinearSPDP NPWitness Tseitin MvPolynomial

/-- Multilinear monomial basis on a variable set V.
    Each subset T ⊆ V gives a monomial ∏_{i∈T} X_i.
    There are 2^|V| such monomials. -/
noncomputable def mlMonomialBasis {n : ℕ}
    (V : Finset (Fin n)) :
    Finset (MvPolynomial (Fin n) ℚ) :=
  V.powerset.image (fun T => T.prod (fun i => MvPolynomial.X i))

theorem mlMonomialBasis_card {n : ℕ} (V : Finset (Fin n)) :
    (mlMonomialBasis V).card ≤ 2 ^ V.card := by
  calc (mlMonomialBasis V).card
      ≤ V.powerset.card := Finset.card_image_le
    _ = 2 ^ V.card := by rw [Finset.card_powerset]

/-- The product of coordinate variables over a finite set is the standard
monomial whose exponent vector is the `0/1` tag of that set. -/
theorem prod_X_eq_monomial_tag {n : ℕ} (T : Finset (Fin n)) :
    T.prod (fun i => (MvPolynomial.X i : MvPolynomial (Fin n) ℚ)) =
      MvPolynomial.monomial (SymmetricPower.tagMonomial T) (1 : ℚ) := by
  rw [SymmetricPower.tagMonomial, MvPolynomial.monomial_sum_one]
  simp [MvPolynomial.X]

/-- The multilinear monomial basis, indexed by its finset enumeration, is
linearly independent.  This is just `MvPolynomial.basisMonomials` restricted
to the `0/1` exponent vectors coming from subsets of `V`. -/
theorem mlMonomialBasis_linearIndependent {n : ℕ} (V : Finset (Fin n)) :
    LinearIndependent ℚ
      (fun p : (mlMonomialBasis V) =>
        (p : MvPolynomial (Fin n) ℚ)) := by
  classical
  let preimage : (mlMonomialBasis V) → Finset (Fin n) := fun p =>
    Classical.choose (by
      have hp :
          (p : MvPolynomial (Fin n) ℚ) ∈
            V.powerset.image
              (fun T => T.prod (fun i => MvPolynomial.X i)) := p.property
      exact Finset.mem_image.mp hp)
  have hpreimage_spec :
      ∀ p : (mlMonomialBasis V),
        preimage p ∈ V.powerset ∧
          (preimage p).prod
              (fun i => (MvPolynomial.X i : MvPolynomial (Fin n) ℚ)) =
            (p : MvPolynomial (Fin n) ℚ) := by
    intro p
    exact Classical.choose_spec (by
      have hp :
          (p : MvPolynomial (Fin n) ℚ) ∈
            V.powerset.image
              (fun T => T.prod (fun i => MvPolynomial.X i)) := p.property
      exact Finset.mem_image.mp hp)
  have hpreimage_inj : Function.Injective preimage := by
    intro p q hpq
    apply Subtype.ext
    calc
      (p : MvPolynomial (Fin n) ℚ)
          = (preimage p).prod
              (fun i => (MvPolynomial.X i : MvPolynomial (Fin n) ℚ)) :=
            (hpreimage_spec p).2.symm
      _ = (preimage q).prod
              (fun i => (MvPolynomial.X i : MvPolynomial (Fin n) ℚ)) := by
            rw [hpq]
      _ = (q : MvPolynomial (Fin n) ℚ) := (hpreimage_spec q).2
  have hli_monomial :
      LinearIndependent ℚ
        (fun T : Finset (Fin n) =>
          MvPolynomial.monomial (SymmetricPower.tagMonomial T) (1 : ℚ)) :=
    (MvPolynomial.basisMonomials (Fin n) ℚ).linearIndependent.comp
      (fun T : Finset (Fin n) => SymmetricPower.tagMonomial T)
      SymmetricPower.tagMonomial_injective
  have hli_prod :
      LinearIndependent ℚ
        (fun T : Finset (Fin n) =>
          T.prod (fun i => (MvPolynomial.X i : MvPolynomial (Fin n) ℚ))) := by
    have hfun :
        (fun T : Finset (Fin n) =>
          T.prod (fun i => (MvPolynomial.X i : MvPolynomial (Fin n) ℚ))) =
        (fun T : Finset (Fin n) =>
          MvPolynomial.monomial (SymmetricPower.tagMonomial T) (1 : ℚ)) := by
      funext T
      exact prod_X_eq_monomial_tag T
    simpa [hfun] using hli_monomial
  have hli_preimage := hli_prod.comp preimage hpreimage_inj
  have hfun :
      (fun p : (mlMonomialBasis V) =>
        (p : MvPolynomial (Fin n) ℚ)) =
      (fun p : (mlMonomialBasis V) =>
        (preimage p).prod
          (fun i => (MvPolynomial.X i : MvPolynomial (Fin n) ℚ))) := by
    funext p
    exact (hpreimage_spec p).2.symm
  simpa [hfun, Function.comp_def] using hli_preimage

/-- Any multilinear polynomial whose vars ⊆ V lies in span(mlMonomialBasis V).

This is the KEY connecting lemma for the locality argument.
Proof: decompose p into its monomial sum; each multilinear monomial with
support ⊆ V is a scalar multiple of ∏_{i∈support} X_i ∈ mlMonomialBasis V. -/
theorem mlProj_in_span_of_vars_subset {n : ℕ}
    (p : MvPolynomial (Fin n) ℚ)
    (V : Finset (Fin n))
    (hp_ml : ∀ α ∈ p.support, Finsupp.IsMultilinear α)
    (hp_vars : p.vars ⊆ V) :
    p ∈ Submodule.span ℚ (↑(mlMonomialBasis V) : Set _) := by
  rw [show p = ∑ v ∈ p.support, MvPolynomial.monomial v (MvPolynomial.coeff v p) from p.as_sum]
  apply Submodule.sum_mem
  intro α hα
  rw [show MvPolynomial.monomial α (MvPolynomial.coeff α p) =
      MvPolynomial.coeff α p • MvPolynomial.monomial α (1 : ℚ) by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]]
  apply Submodule.smul_mem
  have hα_ml := hp_ml α hα
  have hα_vars : α.support ⊆ V := by
    intro x hx
    apply hp_vars
    exact (MvPolynomial.mem_vars x).mpr ⟨α, hα, hx⟩
  have hmon : MvPolynomial.monomial α (1 : ℚ) =
      α.support.prod (fun i => MvPolynomial.X i) := by
    rw [← MvPolynomial.prod_X_pow_eq_monomial]
    apply Finset.prod_congr rfl
    intro x hx
    have hne : α x ≠ 0 := Finsupp.mem_support_iff.mp hx
    have : α x = 1 := by have := hα_ml x; omega
    rw [this, pow_one]
  rw [hmon]
  apply Submodule.subset_span
  simp only [mlMonomialBasis, Finset.coe_image, Set.mem_image]
  exact ⟨α.support, Finset.mem_powerset.mpr hα_vars, rfl⟩

-- Corollary: if a submodule ≤ span(mlMonomialBasis V), finrank ≤ 2^|V|.
set_option maxHeartbeats 400000 in
theorem finrank_le_of_vars_bounded {n : ℕ}
    (W : Submodule ℚ (MvPolynomial (Fin n) ℚ)) [Module.Finite ℚ W]
    (V : Finset (Fin n))
    (hW : W ≤ Submodule.span ℚ (↑(mlMonomialBasis V) : Set _)) :
    Module.finrank ℚ W ≤ 2 ^ V.card := by
  have hfin : Module.Finite ℚ
      (Submodule.span ℚ (↑(mlMonomialBasis V) : Set (MvPolynomial (Fin n) ℚ))) :=
    Module.Finite.span_of_finite ℚ (Finset.finite_toSet _)
  have h1 : Module.finrank ℚ W ≤
      Module.finrank ℚ (Submodule.span ℚ (↑(mlMonomialBasis V) : Set _)) :=
    Submodule.finrank_mono hW
  have h2 : Module.finrank ℚ
      (Submodule.span ℚ (↑(mlMonomialBasis V) : Set (MvPolynomial (Fin n) ℚ))) ≤
      (mlMonomialBasis V).card :=
    finrank_span_finset_le_card (mlMonomialBasis V)
  linarith [mlMonomialBasis_card V]

end MlProjFar
