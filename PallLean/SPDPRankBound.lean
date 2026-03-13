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
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.PDeriv

namespace SPDPRankBound

open SPDP

open MvPolynomial SPDP

/-! ## Step 1: High degree implies nonzero 2nd derivative -/

/-- Helper: if totalDegree ≥ 2, find a support element with degree ≥ 2. -/
private theorem exists_support_degree_ge_two {n : ℕ}
    (q : MvPolynomial (Fin n) ℚ) (hq : 2 ≤ q.totalDegree) :
    ∃ α ∈ q.support, 2 ≤ (α.sum fun _ k => k) := by
  by_contra h
  push_neg at h
  have : q.totalDegree ≤ 1 := by
    apply Finset.sup_le
    intro α hα
    have := h α hα
    omega
  omega

/-- Helper: a Finsupp with sum ≥ 2 has two (possibly equal) indices with positive values. -/
private theorem exists_two_indices {n : ℕ}
    (α : Fin n →₀ ℕ) (hα : 2 ≤ α.sum fun _ k => k) :
    ∃ i j : Fin n, 1 ≤ α i ∧ 1 ≤ (α - Finsupp.single i 1 : Fin n →₀ ℕ) j := by
  sorry

theorem exists_nonzero_second_deriv {n : ℕ}
    (q : MvPolynomial (Fin n) ℚ) (hq : 2 ≤ q.totalDegree) :
    ∃ i j : Fin n, iterDerivList [i, j] q ≠ 0 := by
  obtain ⟨α, hα_mem, hα_deg⟩ := exists_support_degree_ge_two q hq
  obtain ⟨i, j, hi, hj⟩ := exists_two_indices α hα_deg
  refine ⟨i, j, ?_⟩
  -- iterDerivList [i,j] q = pderiv j (pderiv i q)
  simp only [iterDerivList, List.foldl]
  -- Show this is nonzero by showing its coefficient at (α - e_i - e_j) is nonzero
  -- pderiv_monomial: pderiv i (monomial s a) = monomial (s - single i 1) (a * s i)
  -- The map β ↦ (β - e_i - e_j) is injective on {β : β i ≥ 1, (β-e_i) j ≥ 1}
  -- So the α-monomial's contribution can't be cancelled
  sorry

/-! ## Step 2: Nonzero derivative gives large SPDP subspace -/

/-- In an integral domain, multiplication by a nonzero element
    preserves linear independence. -/
theorem mul_linearIndependent {R : Type*} [CommRing R] [IsDomain R]
    {ι : Type*} {v : ι → MvPolynomial (Fin 4) R}
    (hv : LinearIndependent R v)
    (d : MvPolynomial (Fin 4) R) (hd : d ≠ 0) :
    LinearIndependent R (fun i => v i * d) := by
  have hinj : Function.Injective (LinearMap.mulRight R d) := by
    intro a b hab
    -- hab : (LinearMap.mulRight R d) a = (LinearMap.mulRight R d) b
    -- i.e., a * d = b * d
    have hab' : a * d = b * d := hab
    have hsub : (a - b) * d = 0 := by rw [sub_mul, hab', sub_self]
    have := (mul_eq_zero.mp hsub).resolve_right hd
    exact sub_eq_zero.mp this
  exact hv.map' (LinearMap.mulRight R d) (LinearMap.ker_eq_bot.mpr hinj)

/-- 10 monomials of degree ≤ 2 on Fin 4, as a list. -/
private noncomputable def tenMonomials : List (MvPolynomial (Fin 4) ℚ) :=
  [1, X 0, X 1, X 2, X 3,
   X 0 * X 1, X 0 * X 2, X 0 * X 3, X 1 * X 2, X 1 * X 3]

/-- Each of the 10 monomials has totalDegree ≤ 2. -/
private theorem tenMonomials_degree_le :
    ∀ m ∈ tenMonomials, m.totalDegree ≤ 2 := by
  intro m hm
  simp only [tenMonomials, List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hm
  have hX : ∀ (i : Fin 4), (X i : MvPolynomial (Fin 4) ℚ).totalDegree = 1 :=
    fun i => MvPolynomial.totalDegree_X (R := ℚ) i
  have hXX : ∀ (i j : Fin 4), (X i * X j : MvPolynomial (Fin 4) ℚ).totalDegree ≤ 2 :=
    fun i j => (MvPolynomial.totalDegree_mul (X i) (X j)).trans (by rw [hX, hX])
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact MvPolynomial.totalDegree_one.le.trans (by omega)
  all_goals (first | (rw [hX]; omega) | exact hXX _ _)

/-- The 10 monomials are linearly independent. -/
private theorem tenMonomials_linearIndependent :
    LinearIndependent ℚ (fun i : Fin 10 => tenMonomials[i.val]'(by simp [tenMonomials])) := by
  -- Each monomial is monomial dₖ 1 for distinct dₖ, hence linearly independent
  -- as basis elements of the free module MvPolynomial (Fin 4) ℚ ≃ (Fin 4 →₀ ℕ) →₀ ℚ
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
