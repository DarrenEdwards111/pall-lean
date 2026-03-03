/-
  SpdpRemaining.lean — Interfaces for remaining sorry clusters (Q1-Q9)
  Based on Darren's specification.
-/
import Mathlib

open scoped BigOperators

namespace SpdpRemaining

/-! ## Q1: mkTransitionConstraint width_bound -/

section TransitionWidth
variable {σ F : Type*} [CommRing F]

structure TransitionWidthSpec (Var : Type*) (mkTrans : ℕ → ℕ → MvPolynomial Var F)
    (polyVars : MvPolynomial Var F → Finset Var) : Prop where
  width_bound : ∀ t i, (polyVars (mkTrans t i)).card ≤ 6

end TransitionWidth

/-! ## Q2: gate_count — cs.length ≤ n^(2t+2) -/

section GateCount
variable {α : Type*}

-- Template: split into length ≤ formula and formula ≤ n^(2t+2)
theorem gate_count_of_bounds
    (constraints : List α) (count : ℕ) (bound : ℕ)
    (h1 : constraints.length ≤ count) (h2 : count ≤ bound) :
    constraints.length ≤ bound := le_trans h1 h2

end GateCount

/-! ## Q3-Q4: Leibniz/pderiv product rule for padding -/

section Leibniz
variable {σ F : Type*} [CommRing F]

/-- pderiv Leibniz rule for MvPolynomial (single variable).
    pderiv i (p * q) = pderiv i p * q + p * pderiv i q -/
theorem pderiv_mul' (i : σ) (p q : MvPolynomial σ F) :
    MvPolynomial.pderiv i (p * q) =
    MvPolynomial.pderiv i p * q + p * MvPolynomial.pderiv i q :=
  MvPolynomial.pderiv_mul

/-- Padding subspace containment via Leibniz:
    For any S with |S|=κ, writing S = Sy ⊔ Sx where Sy hits padding vars
    and Sx hits content vars:
    ∂_S(Y·V) = ±(∏_{j∉Sy} yj) · ∂_{Sx}(V)
    This means each generator of blockedSpdpSubspace(Y·V) lies in
    ⨆ r, blockedSpdpSubspace r ℓ V (up to scalar multiples).

    The containment follows from span_mono once you show each generator
    maps into the target span. -/
theorem padding_subspace_containment
    {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (W_padded W_target : Submodule R V)
    (h : ∀ w ∈ (W_padded : Set V), w ∈ W_target) :
    W_padded ≤ W_target := h

end Leibniz

/-! ## Q5: width_to_rank_bound — connect abstract to HasLocalityStructure -/

-- Already proved in SpdpPaperKeyLemmas.lean:
-- width_to_rank_bound : span(Rows) ≤ H.sup Vh → finrank ≤ |H|·d
-- The connection to HasLocalityStructure needs:
-- (a) Rows = row polynomials from the SPDP matrix
-- (b) H = profiles, |H| ≤ (G·w)^2
-- (c) Vh = per-profile subspace, dim ≤ G·w
-- These come from §5.1-5.15 infrastructure.

/-! ## Q6: extraction_rank_monotone — generator inclusion -/

section ExtractionGenerators
variable {F W : Type*} [Field F] [AddCommGroup W] [Module F W] [FiniteDimensional F W]

/-- Each extraction stage maps generators into generators.
    Restriction (v:=0) acts via MvPolynomial.eval₂ (setting witness vars to 0).
    Projection restricts to verifier block indices.
    Relabeling applies an injective variable rename.
    Gauge normalization is block-local linear transformation.

    All four can be expressed as: generators(output) ⊆ generators(input),
    which gives Submodule.span_mono → finrank_le_finrank_of_le. -/
theorem extraction_from_generator_inclusion
    (bssGens : ℕ → Set W)
    (stage : ℕ → ℕ)
    (h : ∀ n, bssGens (stage n) ⊆ bssGens n) :
    ∀ n, Submodule.span F (bssGens (stage n)) ≤ Submodule.span F (bssGens n) :=
  fun n => Submodule.span_mono (h n)

end ExtractionGenerators

/-! ## Q7: buildTseitin properties — from ramanujanFamily axiom -/

-- Since ramanujanFamily is already an axiom, the 4 buildTseitin properties
-- (parity_odd, num_clauses_upper, num_clauses_lower, bounded_occurrence)
-- should follow from the axiom's properties.
-- If ramanujanFamily provides: regular graph, degree ≤ 10, connected, Ramanujan:
-- - parity_odd: only vertex 0 has bit=true → odd parity (from graph connectivity)
-- - num_clauses: numEdges ∈ [numVertices, 10·numVertices] (from d-regular)
-- - bounded_occurrence: each var in ≤ 3·degree = 30 clauses

/-! ## Q8: binomial_lower_bound -/

-- Strategy: pick n₀ = 2^60, prove C(n/30, log₂n) ≥ (n/30·log₂n)^{log₂n}
-- using C(L,k) ≥ (L/k)^k, then show (n/30·log₂n)^{log₂n} ≥ n^{log₂n/4}
-- for large n.

/-! ## Q9: identity_minor_lower_bound — coeffLin as dual functional -/

section CoeffDual
variable {σ F : Type*} [CommRing F]

/-- MvPolynomial.coeff as a linear functional. -/
noncomputable def coeffLin (m : σ →₀ ℕ) :
    MvPolynomial σ F →ₗ[F] F where
  toFun := MvPolynomial.coeff m
  map_add' := by intros; simp [map_add]
  map_smul' := by intros; simp [MvPolynomial.coeff_smul, smul_eq_mul]

/-- The Kronecker delta property for tag monomials:
    coeffLin τ_S (R_T) = δ_{S,T}
    needs: τ_S = ∏_{C∈S} τ_C where τ_C is the unique monomial of clauseGadget C
    that doesn't appear in any other clauseGadget (from disjoint variable sets).

    Once you have this, apply finrank_span_ge_card_of_dual from SpdpPaperKeyLemmas. -/
theorem coeffLin_placeholder : True := trivial

end CoeffDual

end SpdpRemaining
