import GodMoveExpanderBoundaryExamples
import GodMoveSATRuntimeFrontier

/-!
Explicit boundary materialization has a runtime cost. This is NOT a lower
bound for arbitrary SAT deciders: the coordinate-write premise is explicit.
A symbolic representation or decision-only machine need not satisfy it.
-/
namespace GodMoveBoundaryRuntimeBarrier
open GodMoveMonomialMinor GodMoveExpanderPositiveProjection
open PallLean.Paper93.DeepMath.PathB
open PvsNPSeparatingInvariant (PolyBounded)

/-- Growth already forced by preserving the paper-window minor. -/
def BoundaryGrowth (q : ℕ → ℕ) : Prop :=
  ∀ n, 2 ^ 20 ≤ n → n ^ (Nat.log 2 n / 4) ≤ q n

/-- A family of actual faithful linear boundaries has this growth. -/
theorem growth_of_faithful_boundaries (q : ℕ → ℕ)
    (B : ∀ n, Poly (n / 3) →ₗ[ℚ] (Fin (q n) → ℚ))
    (hB : ∀ n, LinearIndependent ℚ
      (fun S : KSubset (n / 3) (Nat.log 2 n) => B n (derivativeRow S.val))) :
    BoundaryGrowth q := by
  intro n hn
  exact GodMoveExpanderBoundaryExamples.paper_window_boundary_dimension n (q n) hn (B n) (hB n)

/-- The numerical growth cannot be eventually bounded by a fixed polynomial. -/
theorem no_eventual_polynomial (q : ℕ → ℕ) (hg : BoundaryGrowth q) :
    ¬ ∃ C d n0 : ℕ, ∀ n ≥ n0, q n ≤ C * n ^ d := by
  rintro ⟨C, d, n0, hb⟩
  let n := max (max C n0) (2 ^ (max 20 (4 * (d + 2))))
  have hn0 : n0 ≤ n := (le_max_right C n0).trans (le_max_left _ _)
  have hnC : C ≤ n := (le_max_left C n0).trans (le_max_left _ _)
  have hnlarge : 2 ^ (max 20 (4 * (d + 2))) ≤ n := le_max_right _ _
  have hn20 : 2 ^ 20 ≤ n :=
    (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (le_max_left _ _)).trans hnlarge
  have hnlog : 2 ^ (4 * (d + 2)) ≤ n :=
    (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (le_max_right _ _)).trans hnlarge
  have hl : 4 * (d + 2) ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by decide) hnlog
  have hn1 : 1 < n := (by norm_num : 1 < (2 : ℕ) ^ 20).trans_le hn20
  have hlow : n ^ (d + 1) < q n :=
    (Nat.pow_lt_pow_right hn1 (by omega : d + 1 < Nat.log 2 n / 4)).trans_le (hg n hn20)
  have hup : C * n ^ d ≤ n ^ (d + 1) := by
    rw [pow_succ, mul_comm (n ^ d) n]
    exact Nat.mul_le_mul_right _ hnC
  exact (not_le_of_gt hlow) ((hb n hn0).trans hup)

/-- If a machine must explicitly emit q coordinates at at most c coordinates
per step, its clock is not polynomial in n. The emission premise is NOT
asserted for unrestricted SAT machines. Includes fixed startup allowance b. -/
theorem explicit_materialization_not_polynomial (q T : ℕ → ℕ)
    (hg : BoundaryGrowth q) (c b : ℕ)
    (hwrites : ∀ n, q n ≤ c * T n + b) : ¬ PolyBounded T := by
  rintro ⟨a, d, ht⟩
  apply no_eventual_polynomial q hg
  refine ⟨(c * a + b) * 2 ^ d, d, 1, ?_⟩
  intro n hn
  have hp : (n + 1) ^ d ≤ (2 * n) ^ d := Nat.pow_le_pow_left (by omega) d
  have hpos : 1 ≤ n ^ d := Nat.one_le_pow d n hn
  have hbudget := hwrites n
  have ht' := ht n
  have hc := Nat.mul_le_mul_left c ht'
  have ha := Nat.mul_le_mul_left (c * a) hp
  rw [mul_pow] at ha
  have hb : b ≤ b * (2 ^ d * n ^ d) := by
    exact Nat.le_mul_of_pos_right b (by positivity)
  nlinarith

end GodMoveBoundaryRuntimeBarrier
#print axioms GodMoveBoundaryRuntimeBarrier.growth_of_faithful_boundaries
#print axioms GodMoveBoundaryRuntimeBarrier.no_eventual_polynomial
#print axioms GodMoveBoundaryRuntimeBarrier.explicit_materialization_not_polynomial
