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
  unfold Restriction.restrictPoly
  -- aeval σ m = m when σ(v) = X v for all v ∈ vars(m).
  rw [m.as_sum]
  simp only [map_sum, aeval_monomial]
  apply Finset.sum_congr rfl
  intro d hd
  rw [monomial_eq]
  congr 1
  apply Finsupp.prod_congr
  intro v hv
  -- Need: σ(v) = X v. We know v ∈ m.vars (from hd + hv) and m.vars ⊆ live.
  have hv_in_vars : v ∈ m.vars := (mem_vars v).mpr ⟨d, hd, hv⟩
  have hv_live := hm v hv_in_vars
  have hρv : ρ v = none := (Finset.mem_filter.mp hv_live).2
  simp [hρv]

-- The key monotonicity: restricted SPDP rank ≤ SPDP rank
theorem restrictedSpdpRank_le_spdpRank {n : ℕ}
    (κ ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ)
    (ρ : Restriction.Restriction n) :
    RestrictedSPDP.restrictedSpdpRank κ ℓ p ρ ≤ spdpRank κ ℓ p := by
  -- The restricted span is contained in the image of the full span
  -- under the linear map (aeval σ) = restrictPoly ρ.
  -- Therefore finrank(restricted) ≤ finrank(full).
  unfold RestrictedSPDP.restrictedSpdpRank spdpRank spdpSubspace
  -- Show restricted span ≤ image of full span under restrictPoly
  set σ := (aeval (fun i : Fin n => match ρ i with
    | none => (X i : MvPolynomial (Fin n) ℚ)
    | some false => 0
    | some true => 1) : MvPolynomial (Fin n) ℚ →ₐ[ℚ] MvPolynomial (Fin n) ℚ)
  set full_span := Submodule.span ℚ
    { q | ∃ S m, S.length = κ ∧ m.totalDegree ≤ ℓ ∧ q = m * iterDerivList S p }
  -- Every restricted generator is σ(full generator)
  have h_sub : Submodule.span ℚ
      { q | ∃ S m, S.length = κ ∧ m.totalDegree ≤ ℓ ∧
        (∀ i ∈ S, i ∈ Restriction.liveVars ρ) ∧
        (∀ v ∈ m.vars, v ∈ Restriction.liveVars ρ) ∧
        q = m * iterDerivList S (Restriction.restrictPoly ρ p) }
    ≤ full_span.map σ.toLinearMap := by
    apply Submodule.span_le.mpr
    intro g ⟨S, m, hlen, hdeg, hSlive, hmlive, hg_eq⟩
    rw [hg_eq, iterDerivList_restrictPoly_comm ρ S hSlive,
        ← restrictPoly_eq_self_of_live ρ m hmlive]
    change σ m * σ (iterDerivList S p) ∈ _
    rw [← map_mul σ]
    exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨S, m, hlen, hdeg, rfl⟩) 
  -- h_sub: restricted span ≤ full_span.map σ (PROVED above)
  -- Need: finrank(LHS) ≤ finrank(full_span)
  -- Step 1: full_span ≤ restrictTotalDegree (bounded degree)
  have h_deg : full_span ≤ MvPolynomial.restrictTotalDegree (Fin n) ℚ (ℓ + p.totalDegree) := by
    apply Submodule.span_le.mpr
    intro q ⟨S, m, hlen, hdeg, hq_eq⟩
    subst hq_eq
    intro mono hmono
    exact le_trans (MvPolynomial.le_totalDegree hmono) (by
      calc (m * iterDerivList S p).totalDegree
          ≤ m.totalDegree + (iterDerivList S p).totalDegree :=
            MvPolynomial.totalDegree_mul m (iterDerivList S p)
        _ ≤ ℓ + p.totalDegree := by
            linarith [SPDP.totalDegree_iterDerivList_le S p])
  -- Step 2: Module.Finite for full_span (submodule of finite-dim space)
  haveI : Module.Finite ℚ (MvPolynomial.restrictTotalDegree (Fin n) ℚ (ℓ + p.totalDegree)) :=
    MvPolynomial.instFiniteSubtypeMemSubmoduleRestrictTotalDegreeOfFinite _ _ _
  haveI h_finite : Module.Finite ℚ full_span :=
    Module.Finite.of_injective (Submodule.inclusion h_deg) (Submodule.inclusion_injective _)
  -- Step 3: finrank chain
  haveI h_finite_map : Module.Finite ℚ (full_span.map σ.toLinearMap) :=
    inferInstance
  calc Module.finrank ℚ (Submodule.span ℚ _)
      ≤ Module.finrank ℚ (full_span.map σ.toLinearMap) :=
        Submodule.finrank_mono h_sub
    _ ≤ Module.finrank ℚ full_span :=
        Submodule.finrank_map_le σ.toLinearMap full_span

end SPDPProjection
