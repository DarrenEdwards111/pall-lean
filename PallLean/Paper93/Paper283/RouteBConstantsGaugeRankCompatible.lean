import PallLean.Paper93.Paper283.RouteBGaugeCandidate
import PallLean.Paper93.Paper283.RouteBMatrixToSATGauge
import PallLean.Paper93.DeepMath.GadgetRank.RankPosOfNe

/-!
# Projection-rank compatibility for the Route B constants gauge

The selected constants N-frame gauge has one-dimensional range.  Therefore its
Route B projection-rank compatibility with a matrix-side rank `rankA` is exactly
the nonzero-rank condition `0 < rankA`.

This file stays on the Route B matrix/gauge surface: it does not use profile or
`keepFOB` machinery.
-/

namespace PallLean.Paper93.Paper283

open MvPolynomial
open TuringMachine

/-- The Route B constants candidate has concrete projection rank exactly `1`. -/
theorem routeBConstantsCandidateGauge_projectionRank_eq_one
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    PallLean.Paper93.Concrete.projectionRank
      (routeBConstantsCandidateGauge M n hn2 htb hns) = 1 := by
  unfold routeBConstantsCandidateGauge
  unfold PallLean.Paper93.Concrete.projectionRank
  let N0 := RouteBCookLevinDim M n hn2 htb hns
  change (Module.finrank ℚ
    (LinearMap.range
      (PallLean.Paper93.Substantive.nonTrivialGauge N0).projection) : ℝ) = 1
  have hrange :
      LinearMap.range
          (PallLean.Paper93.Substantive.nonTrivialGauge N0).projection =
        Submodule.span ℚ ({1} : Set (MvPolynomial (Fin N0) ℚ)) := by
    apply le_antisymm
    · change LinearMap.range
          (PallLean.Paper93.Substantive.toConstantsProjection N0) ≤
        Submodule.span ℚ ({1} : Set (MvPolynomial (Fin N0) ℚ))
      exact PallLean.Paper93.Substantive.range_toConstantsProjection_le_span_one N0
    · rw [Submodule.span_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      change (1 : MvPolynomial (Fin N0) ℚ) ∈
        LinearMap.range (PallLean.Paper93.Substantive.toConstantsProjection N0)
      exact PallLean.Paper93.Substantive.one_mem_range_toConstantsProjection N0
  rw [hrange]
  have h_one_ne_zero : (1 : MvPolynomial (Fin N0) ℚ) ≠ 0 := one_ne_zero
  rw [finrank_span_singleton h_one_ne_zero]
  norm_num

/-- For the Route B constants candidate, rank compatibility is equivalent to
positive matrix-side rank. -/
theorem routeBConstantsCandidateGauge_rankCompatible_iff_rank_pos
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (rankA : Nat) :
    RouteBProjectionRankCompatible M n hn2 htb hns rankA
        (routeBConstantsCandidateGauge M n hn2 htb hns) ↔
      0 < rankA := by
  constructor
  · intro hcompat
    unfold RouteBProjectionRankCompatible at hcompat
    rw [routeBConstantsCandidateGauge_projectionRank_eq_one
      M n hn2 htb hns] at hcompat
    have hnat : (1 : Nat) ≤ rankA := by
      exact_mod_cast hcompat
    exact hnat
  · intro hRank
    unfold RouteBProjectionRankCompatible
    rw [routeBConstantsCandidateGauge_projectionRank_eq_one
      M n hn2 htb hns]
    exact_mod_cast hRank

/-- Constructor form: a positive matrix-side rank gives Route B projection-rank
compatibility for the constants candidate. -/
theorem routeBConstantsCandidateGauge_rankCompatible_of_rank_pos
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (rankA : Nat) (hRank : 0 < rankA) :
    RouteBProjectionRankCompatible M n hn2 htb hns rankA
      (routeBConstantsCandidateGauge M n hn2 htb hns) :=
  (routeBConstantsCandidateGauge_rankCompatible_iff_rank_pos
    M n hn2 htb hns rankA).mpr hRank

/-- Matrix form using the existing concrete rank inequality:
a nonzero real matrix has positive rank. -/
theorem routeBConstantsCandidateGauge_rankCompatible_of_matrix_ne_zero
    {N : Nat}
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (A : Matrix (Fin N) (Fin N) Real) (hA : A ≠ 0) :
    RouteBProjectionRankCompatible M n hn2 htb hns A.rank
      (routeBConstantsCandidateGauge M n hn2 htb hns) :=
  routeBConstantsCandidateGauge_rankCompatible_of_rank_pos
    M n hn2 htb hns A.rank
    (PallLean.Paper93.DeepMath.GadgetRank.rank_pos_of_ne_zero A hA)

/-! ## Axiom audit anchors -/

#print axioms routeBConstantsCandidateGauge_projectionRank_eq_one
#print axioms routeBConstantsCandidateGauge_rankCompatible_iff_rank_pos
#print axioms routeBConstantsCandidateGauge_rankCompatible_of_rank_pos
#print axioms routeBConstantsCandidateGauge_rankCompatible_of_matrix_ne_zero

end PallLean.Paper93.Paper283
