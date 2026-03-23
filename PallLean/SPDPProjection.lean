/-
  SPDPProjection.lean — SPDP rank monotonicity under projection/restriction

  Key lemma: evaluating some variables at constants cannot increase SPDP rank.
  This is because aeval is a ring homomorphism that maps generators to generators.

  Specifically: if σ : Fin N → MvPolynomial (Fin N) R maps some variables
  to constants and others to themselves, then:
    spdpRank(aeval σ p) ≤ spdpRank(p)

  This is Step (B) of the cook_levin_spdp_bridge decomposition.
-/
import PallLean.SPDPDefs
import PallLean.RestrictedSPDP
import PallLean.Restriction
import Mathlib.Tactic

namespace SPDPProjection

open MvPolynomial SPDP

/-! ## Partial evaluation maps generators to generators

  If g = m · ∂^S(p) is an SPDP generator of p, then
  aeval(g) = aeval(m) · aeval(∂^S(p)).

  For partial evaluation (identity on free vars, constant on fixed vars):
  - aeval(m) has totalDegree ≤ totalDegree(m)
  - aeval(∂^S(p)) = ∂^S'(aeval(p)) where S' = S restricted to free vars
    (derivatives w.r.t. fixed vars give 0 after evaluation)

  Wait — ∂ and aeval don't commute in general. But for partial evaluation
  where fixed vars map to constants:
  - ∂_v(aeval σ p) = aeval σ (∂_v p) when v is a FREE variable
  - ∂_v(aeval σ p) = 0 when v is a FIXED variable (since aeval σ p
    doesn't depend on v)

  So the generators of aeval(p) are a SUBSET of the images of generators of p.
  Therefore: spdpRank(aeval σ p) ≤ spdpRank(p).
-/

-- The derivative of a restricted polynomial w.r.t. a live variable
-- equals the restriction of the derivative.
-- pderiv v (restrictPoly ρ p) = restrictPoly ρ (pderiv v p) when v is live.
-- This is the key commutation lemma.

theorem pderiv_restrictPoly_comm {n : ℕ} (ρ : Restriction.Restriction n)
    (v : Fin n) (hv : v ∈ Restriction.liveVars ρ)
    (p : MvPolynomial (Fin n) ℚ) :
    pderiv v (Restriction.restrictPoly ρ p) =
    Restriction.restrictPoly ρ (pderiv v p) := by
  -- pderiv is a derivation, aeval is an algebra hom.
  -- When the algebra hom fixes X v (i.e., σ(v) = X v for live v),
  -- they commute on that variable's derivative.
  -- Both sides are ℚ-algebra derivations/homomorphisms, agree on generators.
  -- Use the fact that pderiv is a derivation and aeval is an AlgHom.
  -- Key: σ(v) = X v (since v is live), so pderiv v (σ(v)) = 1.
  -- For any algebra hom φ with φ(X v) = X v:
  --   pderiv v (φ p) = φ (pderiv v p)
  -- because pderiv v is the unique derivation with pderiv v (X i) = δ_{vi},
  -- and φ ∘ pderiv v ∘ φ⁻¹ is also a derivation with the same value on X i
  -- (when φ fixes X v).
  -- Formally: use MvPolynomial.derivation_ext or induction_on.
  -- Both sides are linear in p and agree on monomials.
  -- The key: aeval σ commutes with pderiv v when σ(v) = X v.
  -- This follows from: pderiv is a derivation, aeval is an algebra hom,
  -- and pderiv v (σ(i)) = δ_{vi} = pderiv v (X i) when σ(v) = X v.
  -- The monomial case uses: pderiv v (∏ σ(iⱼ)) via Leibniz rule.
  sorry

-- The key monotonicity: restricted SPDP rank ≤ SPDP rank
-- (restriction can only reduce rank)
theorem restrictedSpdpRank_le_spdpRank {n : ℕ}
    (κ ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ)
    (ρ : Restriction.Restriction n) :
    RestrictedSPDP.restrictedSpdpRank κ ℓ p ρ ≤ spdpRank κ ℓ p := by
  -- The restricted generators (S from live vars, m vars from live vars)
  -- are a SUBSET of all generators (S from all vars, m vars from all vars).
  -- The restricted polynomial restrictPoly ρ p has the same generators
  -- as the subset applied to the original p.
  -- By pderiv_restrictPoly_comm, derivatives commute with restriction
  -- for live variables, so restricted generators map into full generators.
  sorry

/-! ## Bridge from blockedSpdpRankQ to restrictedSpdpRank

  When the block partition is compatible with the restriction:
  restrictedSpdpRank ≤ blockedSpdpRankQ

  The blocked variant has ADDITIONAL constraints (S-coupling, transversal)
  beyond the restricted variant (S from live vars). But the blocked variant
  uses a LARGER polynomial space (compiledVarCount vs n variables).

  The bridge requires embedding the function's polynomial space into
  the compiled polynomial's space, which IS the Cook-Levin step.
-/

end SPDPProjection
