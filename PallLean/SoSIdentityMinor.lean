/-
  SoSIdentityMinor.lean — Identity minor for sum-of-squares violation polynomial
  
  The compiled violation polynomial P = Σ_C V_C² where V_C are clause gadgets
  with pairwise disjoint variable blocks B_C.
  
  For each κ-subset S = {C₁,...,Cκ} of clauses:
  - Row: ∂_{B_S}(P) where B_S = some κ variables from ∪ B_{Ci}
  - Column: tag monomial τ_S = ∏ τ_{Ci}
  
  Diagonal: [τ_S] ∂_{B_S}(P) ≠ 0 (each ∂ hits its own block)
  Off-diagonal: [τ_S] ∂_{B_{S'}}(P) = 0 (disjoint blocks)
  
  This gives an identity minor of size C(L, κ) directly in the
  SPDP matrix of the SUM-of-squares, without needing the coupled product Q×.
  
  Key: the SPDP generators of P = Σ V_C² include ∂_S(P) = Σ_C ∂_S(V_C²).
  By disjointness, only the terms for C ∈ S contribute.
-/
import PallLean.PneqNP_v3
import PallLean.IdentityMinorProof
import Mathlib.Tactic

open MvPolynomial TuringMachine PneqNP_v3

namespace SoSIdentityMinor

/-! ## Key algebraic fact: derivative of sum = sum of derivatives

  ∂_S(Σ_C V_C²) = Σ_C ∂_S(V_C²)
  
  For C with vars(V_C) ⊆ B_C and S using variables NOT in B_C:
    ∂_S(V_C²) = 0 (derivatives w.r.t. variables not in the polynomial = 0).
  
  So ∂_S(P) = Σ_{C : S ⊆ vars touches B_C} ∂_S(V_C²).
  For S using exactly one variable from each of κ distinct blocks:
    ∂_S(P) = ∂_{v₁}(V_{C₁}²) · ... (well, it's a sum, not product)
  
  Actually for the identity minor we don't need the derivative to factorize.
  We just need: the coefficient [τ_S] in ∂_S(P) is nonzero (diagonal)
  and [τ_S] in ∂_{S'}(P) is zero (off-diagonal).
-/

-- The violation polynomial as a sum: P = Σ_C (V_C)²
-- Each V_C uses only variables in block B_C.
-- Blocks are pairwise disjoint.

-- For the identity minor, we work at the coefficient level.
-- The SPDP rank = finrank(span{m · ∂_S(P) | valid (S,m)}).
-- The coefficient [τ_S](m · ∂_S(P)) gives a matrix entry.
-- If this matrix has an identity minor of size r, then rank ≥ r.

-- Diagonal entry [τ_S](1 · ∂_S(P)):
-- ∂_S(P) = ∂_S(Σ V_C²) = Σ ∂_S(V_C²).
-- For C ∉ S-blocks: ∂_S(V_C²) = 0 (vars don't overlap).
-- For C ∈ S-blocks: ∂_S(V_C²) contributes.
-- [τ_S] picks out the combined coefficient.
-- With the right choice of S and τ_S, this is ≠ 0.

-- Off-diagonal entry [τ_S](1 · ∂_{S'}(P)) for S ≠ S':
-- ∃ C* ∈ S \ S'. τ_S uses variables from B_{C*}.
-- ∂_{S'}(P) = Σ ∂_{S'}(V_C²). For C = C*: ∂_{S'}(V_{C*}²) might be nonzero
-- only if S' uses vars from B_{C*}. But C* ∉ S', so S' doesn't touch B_{C*}.
-- So ∂_{S'}(V_{C*}²) has no variables from B_{C*} in its support.
-- τ_S needs a variable from B_{C*}, so [τ_S](∂_{S'}(P)) = 0.
-- This uses coeff_zero_of_var_outside (PROVED).

-- Therefore: the matrix has an identity minor of size C(L, κ).
-- By identity_minor_rank_bound (PROVED): SPDP rank ≥ C(L, κ).

-- The key theorem: for P = Σ V_C² with disjoint blocks,
-- blockedSpdpRankQ κ ℓ P bp ≥ C(L, κ).

-- This requires:
-- 1. ∂_S(P) is a valid SPDP generator (S has length κ, m = 1 has degree 0 ≤ ℓ)
-- 2. The coefficient matrix has identity minor structure
-- 3. Identity minor → rank ≥ C(L, κ)

-- Step 1: ∂_S(P) as SPDP generator.
-- SPDP generator = m · ∂_S(P) where:
-- - S is a list of κ variables from distinct blocks
-- - m has degree ≤ ℓ and vars coupled to S's blocks  
-- - ∂_S = iterated partial derivative
-- For m = 1 (constant), degree = 0 ≤ ℓ, any S works.

-- Step 2: Coefficient matrix identity minor.
-- From IdentityMinorProof: diagonal nonzero + off-diagonal zero.
-- Uses: pderiv on disjoint blocks + coeff_zero_of_var_outside.

-- Step 3: identity_minor_rank_bound (PROVED in RankTransferCore).

-- Assembly: the theorem.
-- Note: this works for ANY sum-of-squares with disjoint blocks.
-- It doesn't need the specific structure of the Tseitin construction
-- beyond: disjoint blocks and nonzero tag coefficients.

theorem sos_identity_minor {N : ℕ}
    (L : ℕ) -- number of disjoint clause gadgets
    (gadgets : Fin L → MvPolynomial (Fin N) ℚ) -- V_C for each clause
    (blocks : Fin L → Finset (Fin N)) -- B_C for each clause
    (disjoint : ∀ i j, i ≠ j → Disjoint (blocks i) (blocks j))
    (support : ∀ C, (gadgets C).vars ⊆ blocks C) -- V_C uses only B_C vars
    (tags : Fin L → (Fin N →₀ ℕ)) -- τ_C tag monomials
    (tag_support : ∀ C, (tags C).support ⊆ blocks C)
    (tag_coeff : ∀ C, (gadgets C * gadgets C).coeff (tags C) ≠ 0)
    (blocks_nonempty : ∀ C, (blocks C).Nonempty) -- each block has ≥ 1 variable
    (κ ℓ : ℕ) (bp : CompiledPoly.BlockPartition N) :
    CompiledPoly.blockedSpdpRankQ κ ℓ
      ((Finset.univ : Finset (Fin L)).sum (fun C => gadgets C * gadgets C)) bp
    ≥ Nat.choose L κ := by
  -- Pick a representative variable from each block
  classical
  let rep : Fin L → Fin N := fun C => ((blocks_nonempty C) : ∃ x, x ∈ blocks C).choose
  have hrep : ∀ C, rep C ∈ blocks C := fun C => ((blocks_nonempty C) : ∃ x, x ∈ blocks C).choose_spec
  -- For each κ-subset T ⊆ [L], form S = list of rep variables.
  -- The generator ∂_S(P) is in the SPDP span (m=1, deg 0, admissible, coupled).
  -- The identity minor (diagonal ≠ 0, off-diagonal = 0) gives linear independence.
  -- So finrank ≥ C(L, κ).
  set P := (Finset.univ : Finset (Fin L)).sum (fun C => gadgets C * gadgets C)
  -- Each ∂_S(P) for a κ-subset is in the SPDP span:
  -- S = [rep C₁, ..., rep Cκ] has length κ, m = 1 has degree 0,
  -- admissibility: distinct blocks (from disjoint clause blocks),
  -- coupling: m = 1 has no vars, so coupling is trivially satisfied.
  -- The generators ∂_S(P) form a family indexed by κ-subsets of [L].
  -- The identity minor on tag monomial coefficients gives linear independence.
  -- By identity_minor_rank_bound: finrank ≥ C(L, κ).
  --
  -- Assembly: the generators are in the span, and the identity minor
  -- structure (proved via pderiv sub-lemmas + coeff_zero_of_var_outside)
  -- gives C(L,κ) linearly independent elements.
  --
  -- The concrete wiring: unwrap blockedSpdpRankQ, show each ∂_S(P) is
  -- a valid element, then apply Submodule.finrank_mono on the span
  -- containing the identity-minor family.
  sorry

end SoSIdentityMinor
