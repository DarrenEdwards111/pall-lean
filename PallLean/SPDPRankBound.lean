/-
  SPDPRankBound.lean — SPDP rank lower bound for degree ≥ 2 polynomials

  Key theorem: on Fin 4 variables at κ=ℓ=2, any polynomial of
  totalDegree ≥ 2 has spdpRank ≥ 10 > 9.

  Proof:
  1. totalDegree ≥ 2 → ∃ [i,j], iterDerivList [i,j] q ≠ 0
     (derivatives of distinct monomials land at distinct exponents,
      so no cancellation in characteristic 0)
  2. d = iterDerivList [i,j] q ≠ 0 → {m * d : deg(m) ≤ 2} has
     10 linearly independent elements (integral domain: multiplication
     by d ≠ 0 is injective on polynomials)
  3. These lie in spdpSubspace → finrank ≥ 10
-/
import PallLean.SPDPDefs
import PallLean.RestrictedSPDP
import PallLean.Restriction
import Mathlib.RingTheory.MvPolynomial.Basic

namespace SPDPRankBound

open SPDP

open MvPolynomial SPDP

/-! ## Step 1: High degree implies nonzero 2nd derivative -/

/-- In characteristic 0, if a polynomial has totalDegree ≥ 2,
    then some second partial derivative is nonzero. -/
theorem exists_nonzero_second_deriv {n : ℕ}
    (q : MvPolynomial (Fin n) ℚ) (hq : 2 ≤ q.totalDegree) :
    ∃ i j : Fin n, iterDerivList [i, j] q ≠ 0 := by
  -- Key idea: pick α ∈ q.support with |α| ≥ 2. Find i,j with α_i ≥ 1,
  -- (α-e_i)_j ≥ 1. Then coeff (α-e_i-e_j) in ∂_j∂_i q equals
  -- q.coeff(α) * α_i * (α-e_i)_j ≠ 0. No cancellation because
  -- the map β ↦ β-e_i-e_j is injective.
  sorry

/-! ## Step 2: Nonzero derivative gives large SPDP subspace -/

/-- In an integral domain, multiplication by a nonzero element
    preserves linear independence. -/
theorem mul_linearIndependent {R : Type*} [CommRing R] [IsDomain R]
    {ι : Type*} {v : ι → MvPolynomial (Fin 4) R}
    (hv : LinearIndependent R v)
    (d : MvPolynomial (Fin 4) R) (hd : d ≠ 0) :
    LinearIndependent R (fun i => v i * d) := by
  sorry

/-- 10 monomials of degree ≤ 2 on Fin 4, as a list. -/
private noncomputable def tenMonomials : List (MvPolynomial (Fin 4) ℚ) :=
  [1, X 0, X 1, X 2, X 3,
   X 0 * X 1, X 0 * X 2, X 0 * X 3, X 1 * X 2, X 1 * X 3]

/-- Each of the 10 monomials has totalDegree ≤ 2. -/
private theorem tenMonomials_degree_le :
    ∀ m ∈ tenMonomials, m.totalDegree ≤ 2 := by
  simp [tenMonomials]
  sorry

/-- The 10 monomials are linearly independent. -/
private theorem tenMonomials_linearIndependent :
    LinearIndependent ℚ (fun i : Fin 10 => tenMonomials[i.val]'(by simp [tenMonomials])) := by
  sorry

/-! ## Step 3: Assembly -/

/-- If iterDerivList S q ≠ 0 with |S|=2, then spdpRank 2 2 q ≥ 10. -/
theorem spdpRank_ge_of_nonzero_deriv
    (q : MvPolynomial (Fin 4) ℚ) (i j : Fin 4)
    (hd : iterDerivList [i, j] q ≠ 0) :
    10 ≤ spdpRank 2 2 q := by
  -- The 10 elements {m * d : m ∈ tenMonomials} are in spdpSubspace
  -- and linearly independent (integral domain argument)
  sorry

/-- Main bound: totalDegree ≥ 2 → spdpRank ≥ 10 on Fin 4 at κ=ℓ=2. -/
theorem spdpRank_ge_of_high_degree
    (q : MvPolynomial (Fin 4) ℚ) (hq : 2 ≤ q.totalDegree) :
    10 ≤ spdpRank 2 2 q := by
  obtain ⟨i, j, hd⟩ := exists_nonzero_second_deriv q hq
  exact spdpRank_ge_of_nonzero_deriv q i j hd

/-- Contrapositive: spdpRank ≤ 9 → totalDegree ≤ 1. -/
theorem low_spdp_rank_implies_low_degree_general
    (q : MvPolynomial (Fin 4) ℚ) (hq : spdpRank 2 2 q ≤ 9) :
    q.totalDegree ≤ 1 := by
  by_contra h
  push_neg at h
  have hge := spdpRank_ge_of_high_degree q (by omega)
  omega

end SPDPRankBound
