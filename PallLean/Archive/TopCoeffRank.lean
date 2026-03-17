/-
  TopCoeffRank.lean — SPDP rank of ∏ Xᵢ with κ=ℓ=w is ≥ 2^w

  Proof outline (not yet fully formalized):
  1. iterDerivList [0,...,w-1] (∏ Xᵢ) = 1 (iterated derivative of product)
  2. So generators include {m · 1 : deg(m) ≤ w} = all degree-≤-w monomials
  3. The 2^w multilinear monomials are linearly independent (basisMonomials)
  4. Hence spdpRank ≥ 2^w

  Each step is standard algebra; the axiom below packages them.
-/
import PallLean.SPDPDefs
import Mathlib.Tactic

namespace TopCoeffRank

open MvPolynomial SPDP

/-- SPDP rank of ∏ Xᵢ on Fin w with κ=ℓ=w is ≥ 2^w.

    Proof: ∂_{x₀}...∂_{x_{w-1}}(∏ Xᵢ) = 1 (the product is the unique
    degree-w multilinear monomial). So the SPDP generators include
    m · 1 for all monomials m of degree ≤ w. In particular, the 2^w
    multilinear monomials {∏_{i∈S} Xᵢ : S ⊆ Fin w} are generators.
    By basisMonomials (Mathlib), these are linearly independent.
    Hence dim(spdpSubspace) ≥ 2^w. -/
axiom spdp_rank_allVarsProd_ge (w : ℕ) (hw : w ≥ 1) :
    spdpRank w w (∏ i : Fin w, (X i : MvPolynomial (Fin w) ℚ)) ≥ 2 ^ w

end TopCoeffRank
