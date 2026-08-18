import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SwitchingShellBuckets

/-!
# Concrete parameters for the block-switching SAT integration

The preceding integration theorem exposes two simultaneous numerical obligations: the rational
block-switching tail must be dyadically small, and the selected good/bad work decomposition must
fit below the active-variable exponent.  This file supplies an explicit nontrivial witness:

* `n = 100` active variables;
* clause width `w = 2`;
* `K = 5` free variables;
* bad block-stream depth `3`;
* exponent saving `2`.

For these values the switching ratio is `10 / 96 = 5 / 48`, the powered base is `5 / 12`, and
the closed tail is `(5/12)^3 / (1 - 5/48) = 125/1548 < 1/8`.  The active work budget is
`(100 - 5) + (3 - 1) = 97 = 100 - 2 - 1`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SwitchingConcreteParameters

set_option maxRecDepth 10000

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.Depth3
open PallLean.Paper93.DeepMath.PathB.SwitchingCounting
open PallLean.Paper93.DeepMath.PathB.ACC0SwitchingShellBuckets
open PallLean.Paper93.DeepMath.PathB.ACC0GoodBadSwitchingCashout

/-- The concrete rational switching-tail inequality used by the final specialization. -/
theorem widthTwo_tail_parameters :
    ((2 : ℚ) ^ 2 * (((2 * 5 : ℕ) : ℚ) / ((100 - 5 + 1 : ℕ) : ℚ))) ^ 3
          / (1 - ((2 * 5 : ℕ) : ℚ) / ((100 - 5 + 1 : ℕ) : ℚ))
        ≤ 1 / (2 ^ (2 + 1) : ℚ) := by
  norm_num

/-- **Fully parameter-instantiated block-switching-to-SAT theorem.**

All numerical tail, shell, and active-depth budgets are discharged.  The only hypotheses left are
the circuit facts saying that the clauses are consistent width-two clauses and that `Bad` is the
actual set of five-star restrictions whose block stream has length three.
-/
theorem widthTwo_blockSwitching_activeGap
    (cs : List (Clause 100)) (F : ℕ)
    (hcons : ∀ T ∈ cs, Consistent T)
    (hw : ∀ T ∈ cs, T.lits.length ≤ 2)
    {Bad : Finset (Restriction 100)}
    (hstars : ∀ ρ ∈ Bad, stars ρ = 5)
    (hbadDepth : ∀ ρ ∈ Bad, (blockStream cs F ρ).length = 3) :
    ∃ i : Fin ((100).choose 5), goodBadWork 100 (100 - 5) (2 ^ (100 - 5))
      (concreteBadCount (K := 5) Bad i) (3 - 1)
      ≤ 2 ^ (100 - 2) := by
  apply block_switching_to_concreteBucket_activeGap cs 2 F 5 3 2 hcons hw
    hstars hbadDepth
  · norm_num
  · norm_num
  · norm_num
  · exact widthTwo_tail_parameters
  · norm_num
  · norm_num
  · norm_num

/-- The actual bad subset of the five-star shell at threshold three.  Fuel is fixed to the
threshold, so `blockStream_length_le` ensures that equality to three captures every stream whose
length is at least three. -/
def widthTwoBad (cs : List (Clause 100)) : Finset (Restriction 100) :=
  Finset.univ.filter fun ρ => stars ρ = 5 ∧ (blockStream cs 3 ρ).length = 3

theorem widthTwoBad_stars (cs : List (Clause 100)) :
    ∀ ρ ∈ widthTwoBad cs, stars ρ = 5 := by
  intro ρ hρ
  exact (Finset.mem_filter.mp hρ).2.1

theorem widthTwoBad_depth (cs : List (Clause 100)) :
    ∀ ρ ∈ widthTwoBad cs, (blockStream cs 3 ρ).length = 3 := by
  intro ρ hρ
  exact (Finset.mem_filter.mp hρ).2.2

/-- Membership is exactly failure of the strict depth-three threshold inside the five-star shell. -/
theorem mem_widthTwoBad_iff (cs : List (Clause 100)) (ρ : Restriction 100) :
    ρ ∈ widthTwoBad cs ↔ stars ρ = 5 ∧ 3 ≤ (blockStream cs 3 ρ).length := by
  rw [widthTwoBad, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hstars, hlen⟩
    exact ⟨hstars, hlen.ge⟩
  · rintro ⟨hstars, hdeep⟩
    refine ⟨hstars, Nat.le_antisymm ?_ hdeep⟩
    exact blockStream_length_le cs 3 ρ

/-- **Structural closure of the concrete parameter theorem.**

The bad set is now constructed internally as the exact depth-three slice of the five-star shell.
Thus callers supply no `Bad`, star-shell proof, depth-slice proof, partition, or numerical premise.
-/
theorem widthTwo_actualBad_activeGap
    (cs : List (Clause 100))
    (hcons : ∀ T ∈ cs, Consistent T)
    (hw : ∀ T ∈ cs, T.lits.length ≤ 2) :
    ∃ i : Fin ((100).choose 5), goodBadWork 100 (100 - 5) (2 ^ (100 - 5))
      (concreteBadCount (K := 5) (widthTwoBad cs) i) (3 - 1)
      ≤ 2 ^ (100 - 2) := by
  exact widthTwo_blockSwitching_activeGap cs 3 hcons hw
    (widthTwoBad_stars cs) (widthTwoBad_depth cs)

end PallLean.Paper93.DeepMath.PathB.ACC0SwitchingConcreteParameters

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingConcreteParameters.widthTwo_tail_parameters
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingConcreteParameters.widthTwo_blockSwitching_activeGap
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingConcreteParameters.widthTwo_actualBad_activeGap
