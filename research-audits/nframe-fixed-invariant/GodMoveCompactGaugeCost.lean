import GodMoveBoundaryNFrameGauge
import GodMoveOperatorSubsetDAG

/-!
# Compact description cost versus actual production projection rank

The shared degree-count recurrence has 2+3m(k+1) stored nodes. At k=log₂m,
this count, even with any fixed linear input-factor overhead, is bounded by
a quadratic in m. The same production gauge has rank choose(m,log₂m), which
eventually exceeds every polynomial in that description budget.

This distinguishes construction of a compact operator description from its
application to a general implicitly represented input. It asserts no SAT
runtime lower bound and no efficient contraction algorithm.
-/

namespace GodMoveCompactGaugeCost

open GodMoveMonomialMinor GodMoveBoundaryNFrameGauge
open GodMoveOperatorSubsetDAG
open PallLean.Paper93.Concrete

/-- Computed node count of the executable shared recurrence, with a fixed linear
allowance for the coordinate factors supplied as inputs. -/
def descriptionBudget (overhead m : ℕ) : ℕ :=
  nodeCount (program m (Nat.log 2 m)) + overhead * m

/-- The size is derived from the actual generated reference arrays. -/
theorem descriptionBudget_exact (overhead m : ℕ) :
    descriptionBudget overhead m = 2 + 3 * m * (Nat.log 2 m + 1) + overhead * m := by
  rw [descriptionBudget, program_nodeCount]

theorem descriptionBudget_quadratic (overhead m : ℕ) :
    descriptionBudget overhead m ≤ (overhead + 5) * (m + 1) ^ 2 := by
  have hlog := Nat.log_le_self 2 m
  have hnode : 2 + 3 * m * (Nat.log 2 m + 1) ≤ 5 * (m + 1) ^ 2 := by
    have hmul := Nat.mul_le_mul_left (3 * m) hlog
    nlinarith
  have hextra : overhead * m ≤ overhead * (m + 1) ^ 2 :=
    Nat.mul_le_mul_left overhead (by nlinarith)
  rw [descriptionBudget_exact]
  nlinarith

theorem descriptionBudget_le_square (overhead m : ℕ) (hm : 1 ≤ m) :
    descriptionBudget overhead m ≤ (4 * (overhead + 5)) * m ^ 2 := by
  calc
    _ ≤ (overhead + 5) * (m + 1) ^ 2 := descriptionBudget_quadratic overhead m
    _ ≤ (overhead + 5) * (2 * m) ^ 2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
    _ = _ := by ring

/-- A coefficient-free asymptotic consequence of the existing concrete
binomial lower bound. -/
theorem no_eventual_polynomial_choose_bound :
    ¬ ∃ C d m0 : ℕ, ∀ m ≥ m0, Nat.choose m (Nat.log 2 m) ≤ C * m ^ d := by
  rintro ⟨C, d, m0, hbound⟩
  let m := max (max C m0) (2 ^ (max 20 (4 * (d + 1 + 1))))
  have hm0 : m0 ≤ m := (le_max_right C m0).trans (le_max_left _ _)
  have hmC : C ≤ m := (le_max_left C m0).trans (le_max_left _ _)
  have hlarge : 2 ^ (max 20 (4 * (d + 1 + 1))) ≤ m := le_max_right _ _
  have hlow := npow_lt_choose_log m (d + 1) hlarge
  have hup : C * m ^ d ≤ m ^ (d + 1) := by
    rw [pow_succ, mul_comm (m ^ d) m]
    exact Nat.mul_le_mul_right _ hmC
  exact (not_le_of_gt hlow) ((hbound m hm0).trans hup)

/-- No fixed polynomial in this quadratic descriptor budget bounds the
preserved minor, even after any fixed per-variable input overhead. -/
theorem no_eventual_polynomial_choose_in_description (overhead : ℕ) :
    ¬ ∃ C d m0 : ℕ, ∀ m ≥ m0,
      Nat.choose m (Nat.log 2 m) ≤ C * (descriptionBudget overhead m) ^ d := by
  rintro ⟨C, d, m0, hbound⟩
  apply no_eventual_polynomial_choose_bound
  refine ⟨C * (4 * (overhead + 5)) ^ d, 2 * d, max m0 1, ?_⟩
  intro m hm
  have hm0 : m0 ≤ m := (le_max_left _ _).trans hm
  have hm1 : 1 ≤ m := (le_max_right _ _).trans hm
  calc
    _ ≤ C * (descriptionBudget overhead m) ^ d := hbound m hm0
    _ ≤ C * ((4 * (overhead + 5)) * m ^ 2) ^ d :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (descriptionBudget_le_square overhead m hm1) d)
    _ = _ := by rw [mul_pow, ← pow_mul, mul_assoc]

/-- The actual unchanged production projection rank, not a newly introduced
rank field, has the same superpolynomial descriptor-cost separation. -/
theorem no_eventual_polynomial_production_rank_in_description (overhead : ℕ) :
    ¬ ∃ C d m0 : ℕ, ∀ m ≥ m0,
      Module.finrank ℚ (LinearMap.range (boundaryGauge m (Nat.log 2 m)).projection) ≤
        C * (descriptionBudget overhead m) ^ d := by
  simpa only [boundaryGauge_rank] using
    no_eventual_polynomial_choose_in_description overhead

/-- The same failure holds for the unchanged production action itself, with
unit rank/barrier weights. Zero coordinates make the graph choice irrelevant. -/
theorem no_eventual_polynomial_production_action_in_description
    (overhead : ℕ) (degree : ℕ → ℕ)
    (G : (m : ℕ) → RegularGraphFixed m (degree m)) (α : ℝ) :
    ¬ ∃ C d m0 : ℕ, ∀ m ≥ m0,
      fullLagrangianFixed α 1 1 (G m) (boundaryGauge m (Nat.log 2 m)) ≤
        ((C * (descriptionBudget overhead m) ^ d : ℕ) : ℝ) := by
  rintro ⟨C, d, m0, hbound⟩
  apply no_eventual_polynomial_choose_in_description overhead
  refine ⟨C, d, m0, ?_⟩
  intro m hm
  have hlo := boundaryGauge_action_ge_rank_term m (Nat.log 2 m) (G m)
    α 1 1 (by norm_num)
  simp only [one_mul] at hlo
  exact_mod_cast hlo.trans (hbound m hm)

end GodMoveCompactGaugeCost

#print axioms GodMoveCompactGaugeCost.descriptionBudget_quadratic
#print axioms GodMoveCompactGaugeCost.descriptionBudget_exact
#print axioms GodMoveCompactGaugeCost.descriptionBudget_le_square
#print axioms GodMoveCompactGaugeCost.no_eventual_polynomial_choose_bound
#print axioms GodMoveCompactGaugeCost.no_eventual_polynomial_choose_in_description
#print axioms GodMoveCompactGaugeCost.no_eventual_polynomial_production_rank_in_description
#print axioms GodMoveCompactGaugeCost.no_eventual_polynomial_production_action_in_description
