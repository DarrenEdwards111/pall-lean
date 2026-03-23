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
  -- Both sides are linear, so induction on p suffices.
  -- σ = restrictPoly assignment: σ(i) = X i for live i, constant for fixed i
  let σ : Fin n → MvPolynomial (Fin n) ℚ := fun i =>
    match ρ i with | none => X i | some false => 0 | some true => 1
  -- Key fact: σ(v) = X v since v is live
  have hσv : σ v = X v := by
    simp only [σ, Restriction.liveVars, Set.mem_setOf_eq] at hv ⊢
    have hρ : ρ v = none := (Finset.mem_filter.mp hv).2; simp [hρ]
  change pderiv v (aeval σ p) = aeval σ (pderiv v p)
  apply MvPolynomial.induction_on p
  · -- Constant: pderiv v (aeval σ (C r)) = pderiv v (C r) = 0
    intro r; simp [MvPolynomial.pderiv_C]
  · -- Addition
    intro f g hf hg
    simp only [map_add, (pderiv v).map_add]
    rw [hf, hg]
  · -- Multiplication by X i
    intro f i hf
    -- Leibniz rule helper
    have pderiv_mul' : ∀ (a b : MvPolynomial (Fin n) ℚ),
        pderiv v (a * b) = pderiv v a * b + a * pderiv v b := by
      intro a b
      have h := (pderiv v).leibniz a b; simp only [smul_eq_mul] at h; rw [h]; ring
    -- Note: MvPolynomial.induction_on gives f * X i (not X i * f)
    -- LHS: pderiv v (aeval σ (f * X i)) = pderiv v (aeval σ f * σ(i))
    rw [map_mul, pderiv_mul' (aeval σ f) (aeval σ (X i))]
    -- RHS: aeval σ (pderiv v (f * X i))
    rw [pderiv_mul' f (X i), map_add, map_mul, map_mul]
    -- pderiv v (aeval σ f) * σ(i) + aeval σ f * pderiv v (σ(i))
    -- = aeval σ (pderiv v f) * σ(i) + aeval σ f * aeval σ (pderiv v (X i))
    rw [hf]
    congr 1
    -- pderiv v (σ(i)) = aeval σ (pderiv v (X i))
    rw [aeval_X]
    by_cases hvi : v = i
    · subst hvi
      have hσv' : σ v = X v := by
        have hρ := (Finset.mem_filter.mp hv).2; simp [σ, hρ]
      rw [hσv', pderiv_X_self]; simp [map_one]
    · -- v ≠ i: both sides multiply by 0
      -- pderiv v (σ i) = 0 (σ(i) doesn't depend on v)
      have h2 : (pderiv v) (σ i) = 0 := by
        simp only [σ]
        cases hρi : ρ i
        · simp [hρi, pderiv_X, hvi]
        · rename_i b; cases b <;> simp [hρi, MvPolynomial.pderiv_C]
      -- aeval σ (pderiv v (X i)) = aeval σ 0 = 0 since pderiv v (X i) = 0 for v ≠ i
      -- Both sides = 0
      rw [h2, mul_zero]
      -- RHS: aeval σ f * aeval σ (pderiv v (X i))
      -- pderiv v (X i) = Pi.single v 1 i = 0 (since v ≠ i)
      -- pderiv v (X i) = 0 for v ≠ i
      have h3 : (pderiv v) (X i : MvPolynomial (Fin n) ℚ) = 0 := by
        simp [pderiv_X, Pi.single_apply, hvi]
      rw [h3, map_zero, mul_zero]

-- iterDerivList commutes with restrictPoly when all vars are live
theorem iterDerivList_restrictPoly_comm {n : ℕ} (ρ : Restriction.Restriction n)
    (S : List (Fin n)) (hS : ∀ v ∈ S, v ∈ Restriction.liveVars ρ)
    (p : MvPolynomial (Fin n) ℚ) :
    iterDerivList S (Restriction.restrictPoly ρ p) =
    Restriction.restrictPoly ρ (iterDerivList S p) := by
  induction S generalizing p with
  | nil => rfl
  | cons v S' ih =>
    unfold iterDerivList
    simp only [List.foldl_cons]
    have hv : v ∈ Restriction.liveVars ρ := hS v (List.Mem.head S')
    have hS' : ∀ w ∈ S', w ∈ Restriction.liveVars ρ :=
      fun w hw => hS w (List.Mem.tail v hw)
    rw [pderiv_restrictPoly_comm ρ v hv]
    exact ih hS' _

-- restrictPoly preserves a polynomial m when m.vars ⊆ live vars
theorem restrictPoly_eq_self_of_live {n : ℕ} (ρ : Restriction.Restriction n)
    (m : MvPolynomial (Fin n) ℚ) (hm : ∀ v ∈ m.vars, v ∈ Restriction.liveVars ρ) :
    Restriction.restrictPoly ρ m = m := by
  -- restrictPoly ρ = aeval σ where σ(v) = X v for live v.
  -- If all vars of m are live, then aeval σ m = m.
  sorry

-- The key monotonicity: restricted SPDP rank ≤ SPDP rank
-- (restriction can only reduce rank)
theorem restrictedSpdpRank_le_spdpRank {n : ℕ}
    (κ ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ)
    (ρ : Restriction.Restriction n) :
    RestrictedSPDP.restrictedSpdpRank κ ℓ p ρ ≤ spdpRank κ ℓ p := by
  -- Strategy: the restricted span is the image of a subset of the full span
  -- under restrictPoly ρ (a linear map). So dim(restricted) ≤ dim(full).
  unfold RestrictedSPDP.restrictedSpdpRank spdpRank spdpSubspace
  -- The restricted generators use restrictPoly ρ p and S/m from live vars.
  -- By pderiv_restrictPoly_comm: m · ∂^S(restrictPoly ρ p) = restrictPoly ρ (m' · ∂^S p)
  -- where m' = restrictPoly ρ m (approximately).
  -- So the restricted span ⊆ image of full span under (aeval σ).
  -- finrank of image ≤ finrank of source.
  --
  -- More precisely: every restricted generator
  --   g = m · iterDerivList S (restrictPoly ρ p)
  -- can be rewritten using pderiv_restrictPoly_comm as
  --   g = m · restrictPoly ρ (iterDerivList S p)
  -- And m (with vars in live set) satisfies m = restrictPoly ρ m.
  -- So g = restrictPoly ρ (m · iterDerivList S p), which is the image
  -- of a full generator under restrictPoly ρ.
  -- Therefore: restricted span ⊆ (restrictPoly ρ).toLinearMap '' full span.
  -- finrank ≤ finrank via Submodule.finrank_map_le.
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
