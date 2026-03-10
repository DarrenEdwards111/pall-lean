/-
  ProfileAssembly.lean — Assembly proof for profile_finrank_bound

  Connects all proved components:
  - DisjointLeibniz (derivatives factor per block)
  - LocalBasis (per-factor derivatives in finite span)
  - SpanProduct (products of span elements in product span)
  - tensor_dim_pow_bound (combinatorial bound)

  The key insight: for a product polynomial p = ∏ f_c with disjoint
  variables, the profileSubspace generators m_poly * iterDerivList S p
  factor as products of per-block contributions, each in a bounded
  local space. The product of local spaces has bounded dimension.
-/
-- import PallLean.ProfileDimBound  -- archived (off-path)
import PallLean.Profile
import PallLean.LocalBasis
import PallLean.SpanProduct
import PallLean.ProfileBridge
import PallLean.DisjointLeibniz
import Mathlib.Tactic

namespace ProfileAssembly

open MvPolynomial SPDP Profile

/-! ## Product structure hypothesis

    The compiled polynomial has product structure:
    p = ∏_{c ∈ T} f_c where each f_c has variables in block c only,
    and blocks have disjoint variables. -/

/-- A polynomial has product structure with respect to a block partition
    if it equals a product of per-block factors with disjoint variables. -/
structure HasProductStructure {n : ℕ} {F : Type*} [CommRing F]
    (B : BlockPartition n) (p : MvPolynomial (Fin n) F) where
  /-- The per-block factors -/
  factor : Fin B.numBlocks → MvPolynomial (Fin n) F
  /-- p equals the product of factors -/
  eq_prod : p = Finset.univ.prod factor
  /-- Each factor's variables are contained in its block -/
  vars_in_block : ∀ c, ∀ v ∈ (factor c).vars, B.assign v = c
  /-- Maximum number of variables per factor -/
  localVarBound : ℕ
  /-- Each factor has bounded variables -/
  factor_vars_le : ∀ c, (factor c).vars.card ≤ localVarBound

/-! ## Assembly theorem

    For a polynomial with product structure, all iterDerivList outputs
    lie in a finite-dimensional span with bounded cardinality. -/

/-- All iterDerivList S p lie in span of a finite set when p has
    product structure. Uses:
    - DisjointLeibniz.iterDeriv_prod_disjoint
    - LocalBasis.iterDerivList_mem_span_monomialFinset
    - SpanProduct.prod_mem_span_finsetProd -/
theorem iterDerivList_in_product_span {n : ℕ} {F : Type*} [CommRing F] [DecidableEq F]
    (B : BlockPartition n)
    (p : MvPolynomial (Fin n) F)
    (hp : HasProductStructure B p)
    (S : List (Fin n))
    (hS : ∀ x ∈ S, ∃ c, B.assign x = c) :
    iterDerivList S p ∈
      Submodule.span F ↑(SpanProduct.finsetProd B.numBlocks
        (fun c => LocalBasis.monomialSpanFinset (hp.factor c))) := by
  classical
  -- Combine all steps: p = ∏ factor, factor by disjoint Leibniz, apply span product
  have hfact : iterDerivList S p =
      Finset.univ.prod (fun c =>
        iterDerivList (S.filter (fun v => decide (B.assign v = c))) (hp.factor c)) := by
    conv_lhs => rw [hp.eq_prod]
    exact ProfileBridge.iterDerivList_prod_disjoint B hp.factor
      (fun c v => B.assign v = c)
      (fun c => hp.vars_in_block c)
      (fun c₁ c₂ hne v h1 h2 => hne (h1.symm.trans h2))
      S (fun x _ => ⟨B.assign x, rfl⟩)
  rw [hfact]
  apply SpanProduct.prod_mem_span_finsetProd
  intro c
  exact LocalBasis.iterDerivList_mem_span_monomialFinset _ _

end ProfileAssembly
