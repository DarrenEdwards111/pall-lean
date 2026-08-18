import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SwitchingBoundedTermFamily
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Uniform linear scaling for bounded term count

For every positive term bound `m`, take `n = 1000m`, `K=5`, width two, canonical-depth threshold
three, and saving two.  The witnessed term-index overhead is then absorbed by the lower restriction
density, uniformly in `m`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SwitchingBoundedTermScaling

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.Depth3
open PallLean.Paper93.DeepMath.PathB.SwitchingCounting
open PallLean.Paper93.DeepMath.PathB.ACC0SwitchingBoundedTermFamily
open PallLean.Paper93.DeepMath.PathB.ACC0SwitchingShellBuckets
open PallLean.Paper93.DeepMath.PathB.ACC0GoodBadSwitchingCashout

set_option maxRecDepth 100000

/-- Choosing five coordinates scales at least as the fifth power under replication into `m` blocks. -/
theorem choose_five_scaling (m : ℕ) (hm : 0 < m) :
    (1000).choose 5 * m ^ 5 ≤ (1000 * m).choose 5 := by
  apply Nat.le_of_mul_le_mul_left (c := Nat.factorial 5) (hc := by norm_num)
  rw [← Nat.mul_assoc]
  rw [← Nat.descFactorial_eq_factorial_mul_choose]
  rw [← Nat.descFactorial_eq_factorial_mul_choose]
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero]
  norm_num
  calc
    990034950024000 * m ^ 5
        = (996 * m) * ((997 * m) * ((998 * m) * ((999 * m) * (1000 * m)))) := by ring
    _ ≤ (1000 * m - 4) * ((1000 * m - 3) *
          ((1000 * m - 2) * ((1000 * m - 1) * (1000 * m)))) := by
      gcongr <;> omega

/-- The normalized three-shell polynomial fits below the scaled five-coordinate shell. -/
theorem normalized_shell_budget (m : ℕ) (hm : 0 < m) :
    8 * (((1000 * m).choose 2) * (8 * m) ^ 3
          + (1000 * m) * (8 * m) ^ 4 + (8 * m) ^ 5)
      ≤ (1000 * m).choose 5 := by
  have hchoose2 : (1000 * m).choose 2 ≤ (1000 * m) ^ 2 := Nat.choose_le_pow _ _
  have hscale := choose_five_scaling m hm
  have hconst :
      8 * ((1000 ^ 2) * 8 ^ 3 + 1000 * 8 ^ 4 + 8 ^ 5) ≤ (1000).choose 5 := by
    norm_num [Nat.choose]
  calc
    8 * ((1000 * m).choose 2 * (8 * m) ^ 3
          + 1000 * m * (8 * m) ^ 4 + (8 * m) ^ 5)
        ≤ 8 * ((1000 * m) ^ 2 * (8 * m) ^ 3
          + 1000 * m * (8 * m) ^ 4 + (8 * m) ^ 5) := by
            gcongr
    _ = (8 * (1000 ^ 2 * 8 ^ 3 + 1000 * 8 ^ 4 + 8 ^ 5)) * m ^ 5 := by ring
    _ ≤ (1000).choose 5 * m ^ 5 := Nat.mul_le_mul_right _ hconst
    _ ≤ (1000 * m).choose 5 := hscale

/-- The explicit shell sum of the parameterized family satisfies the dyadic budget uniformly. -/
theorem linearScaling_shellBudget (m : ℕ) (hm : 0 < m) :
    (∑ t ∈ Finset.Icc 3 5,
        (1000 * m).choose (5 - t) * 2 ^ (1000 * m - (5 - t)) * (2 * 2 * m) ^ t)
        * 2 ^ 3
      ≤ (1000 * m).choose 5 * 2 ^ (1000 * m - 5) := by
  have hn : 5 ≤ 1000 * m := by omega
  have hnorm := normalized_shell_budget m hm
  have hi : Finset.Icc 3 5 = {3, 4, 5} := by decide
  rw [hi]
  norm_num [Finset.sum_insert]
  norm_num [pow_succ]
  rw [show 1000 * m - 2 = (1000 * m - 5) + 3 by omega,
    show 1000 * m - 1 = (1000 * m - 5) + 4 by omega,
    show 1000 * m = (1000 * m - 5) + 5 by omega]
  simp only [pow_add]
  simp only [show 1000 * m - 5 + 5 = 1000 * m by omega]
  calc
    _ = (8 * ((1000 * m).choose 2 * (8 * m) ^ 3
          + 1000 * m * (8 * m) ^ 4 + (8 * m) ^ 5)) * 2 ^ (1000 * m - 5) := by ring
    _ ≤ (1000 * m).choose 5 * 2 ^ (1000 * m - 5) :=
      Nat.mul_le_mul_right _ hnorm

/-- **Uniform corrected speedup for every positive bounded term count.** -/
theorem linearScaling_selectedBucket_activeGap
    (m : ℕ) [NeZero m] (cs : List (Clause (1000 * m)))
    (hw : ∀ T ∈ cs, T.lits.length ≤ 2) (hm : cs.length ≤ m) :
    ∃ i : Fin ((1000 * m).choose 5),
      goodBadWork (1000 * m) (1000 * m - 5) (2 ^ (1000 * m - 5))
        (concreteBadCount (K := 5) (boundedTermBad cs 5 3) i) 2
        ≤ 2 ^ (1000 * m - 2) := by
  apply boundedTerm_selectedBucket_activeGap cs hw hm
  · have : 0 < m := NeZero.pos m
    omega
  · have : 0 < m := NeZero.pos m
    omega
  · have : 0 < m := NeZero.pos m
    omega
  · have : 0 < m := NeZero.pos m
    omega
  · exact linearScaling_shellBudget m (NeZero.pos m)

end PallLean.Paper93.DeepMath.PathB.ACC0SwitchingBoundedTermScaling

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingBoundedTermScaling.choose_five_scaling
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingBoundedTermScaling.linearScaling_shellBudget
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingBoundedTermScaling.linearScaling_selectedBucket_activeGap
