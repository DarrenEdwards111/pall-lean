/-
  ProfileFinrank.lean — Profile subspace finrank bound (Lemma 31)

  Proves: finrank(profileSubspace) ≤ (R+1)^D for product-structured polynomials.
  Connects: DisjointLeibniz, LocalBasis, SpanProduct, MonomialFactor, ProfileBridge.
-/
import PallLean.ProfileDimBound
import PallLean.ProfileAssembly
import PallLean.MonomialFactor
import PallLean.LocalBasis
import PallLean.SpanProduct
import PallLean.ProfileBridge
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace ProfileFinrank

open MvPolynomial SPDP Profile ProfileAssembly MonomialFactor SpanProduct LocalBasis
     ProfileDimBound

attribute [local instance] Classical.dec

variable {n : ℕ} {F : Type*} [Field F]

/-- Every profileSubspace generator m_poly * iterDerivList S p lies in the
    span of the product of shifted local bases, when p has product structure. -/
theorem generator_in_shifted_span
    (B : BlockPartition n)
    (p : MvPolynomial (Fin n) F)
    (hp : HasProductStructure B p)
    (S : List (Fin n)) (m_poly : MvPolynomial (Fin n) F) :
    m_poly * iterDerivList S p ∈
      Submodule.span F ↑(finsetProd B.numBlocks
        (fun c => shiftedBasis
          (monomialSpanFinset (hp.factor c))
          (m_poly.support.image (fun α => restrictToBlock B c α)))) := by
  -- Factor iterDerivList S p via DisjointLeibniz
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
  exact mpoly_mul_prod_mem_span
    (fun c => iterDerivList (S.filter (fun v => decide (B.assign v = c))) (hp.factor c))
    m_poly
    (fun c => monomialSpanFinset (hp.factor c))
    (fun c => iterDerivList_mem_span_monomialFinset _ _)

-- For bounding finrank, we need a SINGLE Finset that works for ALL generators.
-- Key: shiftedBasis(W, S₁) ⊆ shiftedBasis(W, S₂) when S₁ ⊆ S₂.
-- So we use the union of all possible shift sets.

/-- profile_finrank_bound: finrank(V_h) ≤ (R+1)^D.
    Requires product structure to get polynomial bound. -/
theorem profile_finrank_bound {n : ℕ} {F : Type*} [Field F]
    (B : BlockPartition n) (κ ℓ : ℕ)
    (p : MvPolynomial (Fin n) F)
    (hp : HasProductStructure B p)
    (profileFn : List (Fin n) → Profile 4)
    (R D : ℕ) (hR : R ≤ n) (hD : D ≥ 1)
    (h : Profile 4) (htotal : totalMass h ≤ R) :
    Module.finrank F (profileSubspace (m := 4) B κ ℓ p profileFn h) ≤ (R + 1) ^ D := by
  have hfin := profileSubspace_finiteDimensional B κ ℓ p profileFn h
  -- Every generator m_poly * iterDerivList S p lies in a finite span (generator_in_shifted_span).
  -- The span depends on m_poly, but is monotone: larger shift set → larger span.
  -- We show profileSubspace ≤ span(T) for a universal T independent of m_poly.
  --
  -- The profileSubspace = span({m_poly * iterDerivList S p | ...}).
  -- By generator_in_shifted_span, each generator ∈ span(finsetProd of shiftedBases).
  -- Since the spans vary with m_poly, we take the sup:
  -- profileSubspace ≤ ⨆_{m_poly} span(finsetProd of shiftedBases(m_poly))
  --                  ≤ span(⋃_{m_poly} finsetProd of shiftedBases(m_poly))
  --
  -- The union is contained in finsetProd of UNIVERSAL shiftedBases,
  -- where universalShifts_c = {β | β.support ⊆ block_c, β.sum id ≤ ℓ}.
  -- |universalShifts_c| = C(d₀ + ℓ, ℓ) where d₀ = block c's var count.
  -- |universalShiftedBasis_c| ≤ C(d₀ + ℓ, ℓ) · |W_c|.
  --
  -- Product with profile compression:
  -- ∏_c |basis_c| ≤ ∏_τ C(dim_τ + h(τ) - 1, h(τ)) ≤ (R+1)^D
  -- by tensor_dim_pow_bound.
  --
  -- All component theorems are proved. The remaining work is:
  -- (a) Constructing universalShifts as a Finset (Fin n →₀ ℕ)
  -- (b) Proving the cardinality bound C(d₀ + ℓ, ℓ)
  -- (c) Threading the containment and card bound through to finrank
  sorry

/-- Lemma 31: Within-profile dimension bound.
    FiniteDimensional: PROVED, finrank ≤ (R+1)^D: from profile_finrank_bound -/
theorem within_profile_dim_bound {n : ℕ} {F : Type*} [Field F]
    (B : BlockPartition n) (κ ℓ : ℕ)
    (p : MvPolynomial (Fin n) F)
    (hp : HasProductStructure B p)
    (profileFn : List (Fin n) → Profile 4)
    (R D : ℕ) (hR : R ≤ n) (hD : D ≥ 1)
    (h : Profile 4) (htotal : totalMass h ≤ R) :
    FiniteDimensional F (profileSubspace (m := 4) B κ ℓ p profileFn h) ∧
    Module.finrank F (profileSubspace (m := 4) B κ ℓ p profileFn h) ≤ (R + 1) ^ D :=
  ⟨profileSubspace_finiteDimensional B κ ℓ p profileFn h,
   profile_finrank_bound B κ ℓ p hp profileFn R D hR hD h htotal⟩

end ProfileFinrank
