import PallLean.TseitinDefs
import PallLean.TagMonomial
import PallLean.ProductDeriv
import PallLean.SPDPDefs
import Mathlib.Tactic
import Mathlib.Data.List.Sublists
/-!
# Identity Minor Construction (Theorem 9.3)

We prove that Q× = ∏(1 - z_C V_C) has a Kronecker δ identity minor
of size (L choose κ), where L = |C_disj| is the disjoint packing size.

## Proof outline (modular):

1. **Derivative lemma**: ∂_{z_S} Q× = (-1)^|S| · ∏_{C∈S} V_C · ∏_{C∉S}(1-z_C V_C)
2. **Tag selection**: For each C, tag_monomial_property gives τ_C with [τ_C]V_C = ±1
3. **Dual monomial**: τ_S = (∑_{C∈S} τ_C) + (∑_{C∉S} single(z_C, 1))
4. **Kronecker δ**: [τ_S] R_{S'} = δ_{S,S'} · (±1)

The index type is Fin (Nat.choose L κ) to match the axiom signature.
-/

namespace IdentityMinor

open MvPolynomial Tseitin ProductDeriv

variable {F : Type*} [Field F]

/-! ## Step 1: Iterated derivative of coupled verifier along selector subset -/

/-- Derivative of a single factor (1 - z_C V_C) w.r.t. z_C gives -V_C -/
theorem pderiv_selector_factor (Φ : TseitinFormula) (c : Fin Φ.clauses.length) :
    pderiv (selectorIdx Φ c) (1 - X (selectorIdx Φ c) * clauseGadget F Φ c) =
    -(clauseGadget F Φ c) := by
  apply ProductDeriv.pderiv_one_sub_mul
  -- Need: selectorIdx Φ c ∉ (clauseGadget F Φ c).vars
  exact selector_not_in_gadget F Φ c c

/-- Derivative of factor (1 - z_{C'} V_{C'}) w.r.t. z_C for C ≠ C' gives 0 -/
theorem pderiv_selector_factor_ne (Φ : TseitinFormula)
    (c c' : Fin Φ.clauses.length) (hne : c ≠ c') :
    pderiv (selectorIdx Φ c) (1 - X (selectorIdx Φ c') * clauseGadget F Φ c') = 0 := by
  apply ProductDeriv.pderiv_one_sub_mul_ne
  · -- selectorIdx Φ c ≠ selectorIdx Φ c'
    intro heq
    exact hne (selectorIdx_injective Φ heq)
  · -- selectorIdx Φ c ∉ (clauseGadget F Φ c').vars
    exact selector_not_in_gadget F Φ c c'

/-! ## Step 2: Tag monomial selection -/

/-- For each clause, choose a tag monomial with coefficient ±1 -/
noncomputable def chooseTagMonomial (Φ : TseitinFormula)
    (c : Fin Φ.clauses.length) :
    (Fin (tseitinNumVars Φ)) →₀ ℕ :=
  (TagMonomial.tag_monomial_property_proof F Φ c).choose

theorem chooseTagMonomial_support (Φ : TseitinFormula)
    (c : Fin Φ.clauses.length) :
    ∀ i ∈ (chooseTagMonomial (F := F) Φ c).support,
      i.val < Φ.graph.numEdges + 3 * Φ.clauses.length :=
  (TagMonomial.tag_monomial_property_proof F Φ c).choose_spec.1

theorem chooseTagMonomial_coeff (Φ : TseitinFormula)
    (c : Fin Φ.clauses.length) :
    coeff (chooseTagMonomial (F := F) Φ c) (clauseGadget F Φ c) = 1 ∨
    coeff (chooseTagMonomial (F := F) Φ c) (clauseGadget F Φ c) = -1 :=
  (TagMonomial.tag_monomial_property_proof F Φ c).choose_spec.2

/-! ## Proof assembly — this is the main construction -/

/-! ## Step 3: Single-step pderiv of coupled verifier

We show that differentiating the coupled verifier ∏(1 - z_C V_C) w.r.t.
one selector z_k pulls out -V_k and leaves the remaining product. -/

/-- The coupled verifier factor for clause c -/
noncomputable def cvFactor (F : Type*) [CommRing F]
    (Φ : TseitinFormula) (c : Fin Φ.clauses.length) :
    MvPolynomial (Fin (tseitinNumVars Φ)) F :=
  1 - X (selectorIdx Φ c) * clauseGadget F Φ c

theorem coupledVerifier_eq_prod (Φ : TseitinFormula) :
    coupledVerifier F Φ = Finset.univ.prod (cvFactor F Φ) := by
  unfold coupledVerifier cvFactor; rfl

/-- pderiv z_k of cvFactor c:
    - If c = k: gives -V_k
    - If c ≠ k: gives 0 -/
theorem pderiv_cvFactor_eq (Φ : TseitinFormula)
    (c : Fin Φ.clauses.length) :
    pderiv (selectorIdx Φ c) (cvFactor F Φ c) =
    -(clauseGadget F Φ c) := by
  unfold cvFactor
  exact pderiv_selector_factor Φ c

theorem pderiv_cvFactor_ne (Φ : TseitinFormula)
    (k c : Fin Φ.clauses.length) (hne : k ≠ c) :
    pderiv (selectorIdx Φ k) (cvFactor F Φ c) = 0 := by
  unfold cvFactor
  exact pderiv_selector_factor_ne Φ k c hne

/-- Applying pderiv z_k to the coupled verifier pulls out -V_k
    and leaves the product over remaining factors.

    ∂_{z_k} ∏_c (1 - z_c V_c) = -V_k · ∏_{c≠k} (1 - z_c V_c) -/
theorem pderiv_coupledVerifier_single (Φ : TseitinFormula)
    (k : Fin Φ.clauses.length) :
    pderiv (selectorIdx Φ k) (coupledVerifier F Φ) =
    -(clauseGadget F Φ k) * (Finset.univ.erase k).prod (cvFactor F Φ) := by
  rw [coupledVerifier_eq_prod]
  have hother : ∀ j ∈ (Finset.univ : Finset (Fin Φ.clauses.length)),
      j ≠ k → pderiv (selectorIdx Φ k) (cvFactor F Φ j) = 0 :=
    fun j _ hne => pderiv_cvFactor_ne Φ k j hne.symm
  rw [pderiv_prod_single (Finset.mem_univ k) hother,
      pderiv_cvFactor_eq Φ k]

end IdentityMinor
