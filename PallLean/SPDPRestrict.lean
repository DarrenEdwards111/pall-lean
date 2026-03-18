/-
  SPDPRestrict.lean — SPDP Evaluation Monotonicity (Paper Lemma 33)

  The paper's proof: restriction R_ρ is a ring homomorphism that maps
  SPDP generators of p to SPDP generators of p'. Therefore
  SPDP(p') ⊆ R_ρ(SPDP(p)), and dim(SPDP(p')) ≤ dim(SPDP(p)).

  Key insight: the paper works in a SMALLER polynomial ring after restriction
  (eliminated variables don't exist). Our formalization uses evalOne which
  keeps the same ring. We bridge this by showing that SPDP(φ(p)) restricted
  to generators NOT using eliminated variables has the right dimension bound.

  Formal proof:
  1. Define evalRingHom = evalOne j c, a ring homomorphism
  2. For each SPDP generator m * ∂_S(φ(p)) where j ∉ S and m free of X_j:
     m * ∂_S(φ(p)) = m * φ(∂_S(p)) = φ(m * ∂_S(p))
     So this generator is in φ(SPDP(p)).
  3. SPDP_free(φ(p)) ⊆ φ(SPDP(p))
  4. dim(SPDP_free(φ(p))) ≤ dim(φ(SPDP(p))) ≤ dim(SPDP(p))
  5. SPDP(φ(p)) = ⊕_a X_j^a · SPDP_free(φ(p), ℓ-a) [direct sum, since φ(p) is X_j-free]
  6. dim(SPDP(φ(p))) = Σ_a dim(SPDP_free(φ(p), ℓ-a))
  7. Each dim(SPDP_free(φ(p), ℓ-a)) ≤ dim(SPDP_free(p, ℓ-a)) ≤ dim(SPDP(p, ℓ-a))

  Wait — step 7 gives dim(SPDP(φ(p))) ≤ Σ_a dim(SPDP(p, ℓ-a)) which
  could exceed dim(SPDP(p, ℓ)).

  CORRECT APPROACH (matching paper exactly):
  φ(SPDP(p)) ⊇ SPDP_free(φ(p))
  AND: SPDP(φ(p)) with X_j-shifts is STILL bounded by SPDP(p) because
  X_j-shift generators equal φ applied to X_j-shift generators of p
  (since φ(X_j) = c, we get c^a times the free content).

  Actually: the paper doesn't worry about X_j shifts because in their
  formulation, X_j doesn't exist after restriction. So their SPDP(p')
  is what we call SPDP_free(φ(p)). And their inequality is just
  dim(SPDP_free(φ(p))) ≤ dim(SPDP(p)).

  For OUR definition (all variables allowed): SPDP(φ(p)) includes
  X_j-shift generators that don't exist in the paper's definition.
  These inflate the rank. But the inequality STILL holds empirically.

  SIMPLEST CORRECT PROOF for our definition:
  Show that the map φ : SPDP(p) → MvPolynomial has image containing
  all FREE-variable generators of SPDP(φ(p)). Then X_j-shift generators
  are X_j^a times free generators, adding dim = Σ_a dim(free generators
  with reduced budget). But SPDP(p) also has X_j-shift generators
  (X_j^a times derivatives of p), which contribute at least as much.

  I think the honest answer is: with our current definition of
  blockedSpdpRankQ (all variables allowed for shifts/derivs),
  the proof requires the X_j-degree grading argument which we've shown
  doesn't give a clean direct sum for SPDP(p).

  RESOLUTION: Change the axiom perm_rank_le_compiled to use
  a "free-variable SPDP" that matches the paper's definition.
  Then the proof becomes φ(SPDP(p)) ⊇ SPDP_free(φ(p)) by linearity. -/
import PallLean.SPDPDefs
import PallLean.SPDPEval
import PallLean.CoeffMatrix
import PallLean.CompiledPoly
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace SPDPRestrict

open MvPolynomial SPDP CompiledPoly

variable {N : ℕ}

/-- Free-variable SPDP generators: shifts and derivatives that avoid variable j. -/
noncomputable def freeSpdpSubspace (j : Fin N) (κ ℓ : ℕ)
    (poly : MvPolynomial (Fin N) ℚ) (bp : CompiledPoly.BlockPartition N) :
    Submodule ℚ (MvPolynomial (Fin N) ℚ) :=
  Submodule.span ℚ
    { q | ∃ (S : List (Fin N)) (m : MvPolynomial (Fin N) ℚ),
        S.length ≤ κ ∧
        m.totalDegree ≤ ℓ ∧
        (S.toFinset.image bp.blockOf).card ≤ κ ∧
        (m.vars.image bp.blockOf).card ≤ ℓ ∧
        j ∉ S ∧                                    -- no j in derivatives
        j ∉ m.vars ∧                               -- no X_j in shifts
        q = m * iterDerivList S poly }

/-- Free SPDP of φ(p) ⊆ φ-image of SPDP(p).

    Every free generator m * ∂_S(φ(p)) with j ∉ S and j ∉ vars(m)
    equals m * φ(∂_S(p)) = φ(m * ∂_S(p)) = φ(gen of SPDP(p)). -/
theorem freeSpdp_evalOne_le (j : Fin N) (c : ℚ) (κ ℓ : ℕ)
    (p : MvPolynomial (Fin N) ℚ) (bp : CompiledPoly.BlockPartition N) :
    freeSpdpSubspace j κ ℓ (SPDPEval.evalOne j c p) bp ≤
    Submodule.map (SPDPEval.evalOne j c).toLinearMap
      (Submodule.span ℚ
        { q | ∃ (S : List (Fin N)) (m : MvPolynomial (Fin N) ℚ),
            S.length ≤ κ ∧
            m.totalDegree ≤ ℓ ∧
            (S.toFinset.image bp.blockOf).card ≤ κ ∧
            (m.vars.image bp.blockOf).card ≤ ℓ ∧
            q = m * iterDerivList S p }) := by
  apply Submodule.span_le.mpr
  intro q ⟨S, m, hlen, hdeg, hSblk, hmblk, hjS, hjm, hq⟩
  rw [hq]
  -- j ∉ S, so iterDerivList S (evalOne j c p) = evalOne j c (iterDerivList S p)
  have hfree : ∀ i ∈ S, i ≠ j := fun i hi heq => hjS (heq ▸ hi)
  rw [SPDPEval.iterDerivList_evalOne_comm j c S p hfree]
  -- j ∉ vars(m), so evalOne j c m = m (m doesn't use X_j)
  -- Therefore m * evalOne j c (iterDerivList S p) = evalOne j c (m * iterDerivList S p)
  -- Because evalOne is a ring hom: evalOne(m * q) = evalOne(m) * evalOne(q) = m * evalOne(q)
  -- (when m doesn't use X_j)
  have hm_free : SPDPEval.evalOne j c m = m := by
    -- aeval f m = m when f agrees with X on vars(m)
    simp only [SPDPEval.evalOne]
    conv_rhs => rw [show m = aeval X m from by rw [aeval_X_left]; rfl]
    simp only [aeval_def]
    apply eval₂Hom_congr' rfl _ rfl
    intro i _ _
    by_cases hij : i = j
    · subst hij; exact absurd ‹i ∈ m.vars› hjm
    · simp [if_neg hij]
  rw [← hm_free, ← map_mul]
  exact Submodule.mem_map_of_mem
    (Submodule.subset_span ⟨S, m, hlen, hdeg, hSblk, hmblk, rfl⟩)

end SPDPRestrict
