/-
  RestrictionRank.lean — Restriction/evaluation preserves SPDP rank inequality

  Key lemma: if p = eval(V, assignment) for some partial assignment,
  then rank(p) ≤ rank(V).

  More precisely: if we set some variables of V to constants and get p,
  then the SPDP generators of p are restrictions of SPDP generators of V,
  so rank(p) ≤ rank(V).

  This is the algebraic core of cookLevin_rank_bound:
  1. M decides hardNPFamily → M computes permanent
  2. Cook-Levin encodes M's computation into violation polynomial V
  3. The permanent appears as a restriction of V
     (set all non-permanent variables to their computation-trace values)
  4. rank(perm) ≤ rank(V)
-/
import PallLean.CompiledPoly
import PallLean.SPDPDefs
import Mathlib.Tactic

namespace RestrictionRank

open MvPolynomial CompiledPoly SPDP

/-! ## Partial evaluation preserves SPDP rank

  If we evaluate some variables of V at constants, the resulting
  polynomial has SPDP rank ≤ the original.

  Formally: let σ : Fin N → ℚ be a partial assignment (fixing some
  variables). Let eval_σ(V) be V with those variables substituted.
  Then blockedSpdpRankQ κ ℓ (eval_σ V) bp' ≤ blockedSpdpRankQ κ ℓ V bp
  for an appropriate partition bp' that is the restriction of bp.
-/

-- aeval maps a polynomial to its evaluation at a point.
-- For partial evaluation, we use aeval with an assignment that
-- is identity on free variables and constant on fixed variables.

-- The key: aeval is an algebra homomorphism, so it preserves
-- the linear structure of SPDP generators.

-- If g = ms * ∂^S(V) is an SPDP generator of V,
-- then aeval(g) = aeval(ms) * ∂^S(aeval(V)) = aeval(ms) * aeval(∂^S(V))
-- Wait — ∂ and aeval don't generally commute.

-- Actually, for partial evaluation (identity on free vars):
-- Let f : Fin N → MvPolynomial (Fin N) ℚ be:
--   f(v) = X v     if v is free
--   f(v) = C(σ v)  if v is fixed
-- Then aeval f : MvPolynomial (Fin N) ℚ →ₐ[ℚ] MvPolynomial (Fin N) ℚ
-- is the partial evaluation.

-- For ∂_v and aeval f:
-- If v is fixed: aeval f (∂_v p) = 0 (the derivative w.r.t. a constant is 0)
-- Wait no — ∂_v of aeval f p ≠ aeval f of ∂_v p in general.

-- This approach is getting complicated. Let me use a different strategy.

/-! ## Alternative: subpolynomial rank bound

  Instead of restriction, use the fact that if p ∈ Submodule.span(gens(V)),
  then rank(p) ≤ rank(V).

  The SPDP rank of V is the dimension of span{ms · ∂^S(V)}.
  If p = ms₀ · ∂^S₀(V) for some specific (ms₀, S₀), then p is in this span.

  More generally, if p is any linear combination of SPDP generators of V,
  then rank(p) ≤ rank(V).
-/

-- The permanent appears in the violation polynomial because:
-- V = Σ clausePoly(c)² where the clauses encode M's computation.
-- When we evaluate V at the accepting computation trace of M on
-- a permanent input, all clause violations vanish (V = 0).
-- But NEAR the computation trace (perturbing input bits),
-- V captures the permanent's structure.

-- The precise statement: the SPDP generators of V, when restricted
-- to the permanent variable subspace, span all SPDP generators of
-- the renamed permanent.

-- This is what cookLevin_rank_bound asserts.

-- For the formalization, this requires:
-- 1. Identifying which SPDP generators of V correspond to permanent generators
-- 2. Showing the map is surjective onto the permanent's SPDP span

-- This is the deep Cook-Levin content that requires understanding
-- how the transition clauses encode the permanent computation.

-- STATE THE KEY INTERMEDIATE:

-- Key reduction: cookLevin_rank_bound follows from span containment
-- via Submodule.finrank_mono. The deep content is proving the containment.

-- The span containment (the real Cook-Levin content) requires:
-- 1. Real DTM transition clauses (built in RealTransition.lean)
-- 2. Permanent embedding into the computation tableau
-- 3. Showing each permanent SPDP generator maps to a violation SPDP generator

-- This is left as the main open proof obligation.

end RestrictionRank
