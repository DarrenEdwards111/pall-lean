import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SwitchingShellAveraging
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BlockSwitchingProb

/-!
# Direct integration of the proved block-switching probability bound

`Depth3.block_switching_prob_closed` bounds a rational bad-shell fraction.  The deterministic SAT
pipeline needs an integer dyadic inequality.  This file closes that arithmetic bridge and composes
it with shell averaging and the good/bad work theorem.

The only remaining hypotheses are now structural/parameter facts visible in the statement:

* the concrete rational Håstad RHS is at most `2^(-(saving+1))`;
* the shell is partitioned into free-variable-set buckets (`sum badCount = Bad.card`);
* the chosen restriction and residual-depth budgets fit the active dimension.

No probability mass, exceptional leaf, or padding variable is discarded.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0BlockSwitchingDyadicIntegration

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.Depth3
open PallLean.Paper93.DeepMath.PathB.SwitchingCounting
open PallLean.Paper93.DeepMath.PathB.ACC0SwitchingShellAveraging
open PallLean.Paper93.DeepMath.PathB.ACC0GoodBadSwitchingCashout

/-- Convert a rational dyadic fraction bound to its exact cross-multiplied natural inequality. -/
theorem rational_dyadic_to_nat (bad total tailBits : ℕ) (htotal : 0 < total)
    (hprob : (bad : ℚ) / (total : ℚ) ≤ 1 / (2 ^ tailBits : ℚ)) :
    bad * 2 ^ tailBits ≤ total := by
  have htotalQ : (0 : ℚ) < (total : ℚ) := by exact_mod_cast htotal
  have hpowQ : (0 : ℚ) < (2 ^ tailBits : ℚ) := by positivity
  have hcross : (bad : ℚ) * (2 ^ tailBits : ℚ) ≤ 1 * (total : ℚ) :=
    (div_le_div_iff₀ htotalQ hpowQ).mp hprob
  norm_num at hcross
  exact_mod_cast hcross

/-- Apply the rational-to-dyadic bridge directly to `block_switching_prob_closed`. -/
theorem block_switching_bad_dyadic
    {n : ℕ} (cs : List (Clause n)) (w F K depth saving : ℕ)
    (hcons : ∀ T ∈ cs, Consistent T) (hw : ∀ T ∈ cs, T.lits.length ≤ w)
    {Bad : Finset (Restriction n)}
    (hstars : ∀ ρ ∈ Bad, stars ρ = K)
    (hdepth : ∀ ρ ∈ Bad, (blockStream cs F ρ).length = depth)
    (hdepthK : depth ≤ K) (hKn : K ≤ n) (hr : 2 * K < n - K + 1)
    (hrhs :
      ((2 : ℚ) ^ w * (((2 * K : ℕ) : ℚ) / ((n - K + 1 : ℕ) : ℚ))) ^ depth
          / (1 - ((2 * K : ℕ) : ℚ) / ((n - K + 1 : ℕ) : ℚ))
        ≤ 1 / (2 ^ (saving + 1) : ℚ)) :
    Bad.card * 2 ^ (saving + 1) ≤ n.choose K * 2 ^ (n - K) := by
  have hprob := block_switching_prob_closed cs w F K depth hcons hw
    hstars hdepth hdepthK hKn hr
  have htotal : 0 < n.choose K * 2 ^ (n - K) :=
    Nat.mul_pos (Nat.choose_pos hKn) (by positivity)
  have hprob' : (Bad.card : ℚ) / ((n.choose K * 2 ^ (n - K) : ℕ) : ℚ)
      ≤ 1 / (2 ^ (saving + 1) : ℚ) := by
    simpa [Nat.cast_mul, Nat.cast_pow] using hprob.trans hrhs
  exact rational_dyadic_to_nat Bad.card (n.choose K * 2 ^ (n - K))
    (saving + 1) htotal hprob'

/-- **End-to-end selected-bucket theorem from the concrete block-switching bound.**  The bucket
family represents the partition of `Bad` by its `K`-element free-variable set. -/
theorem block_switching_to_selectedBucket_activeGap
    {n : ℕ} (cs : List (Clause n)) (w F K depth saving : ℕ)
    (hcons : ∀ T ∈ cs, Consistent T) (hw : ∀ T ∈ cs, T.lits.length ≤ w)
    {Bad : Finset (Restriction n)}
    (hstars : ∀ ρ ∈ Bad, stars ρ = K)
    (hbadDepth : ∀ ρ ∈ Bad, (blockStream cs F ρ).length = depth)
    (hdepthK : depth ≤ K) (hKn : K ≤ n) (hr : 2 * K < n - K + 1)
    (hrhs :
      ((2 : ℚ) ^ w * (((2 * K : ℕ) : ℚ) / ((n - K + 1 : ℕ) : ℚ))) ^ depth
          / (1 - ((2 * K : ℕ) : ℚ) / ((n - K + 1 : ℕ) : ℚ))
        ≤ 1 / (2 ^ (saving + 1) : ℚ))
    (badCount : Fin (n.choose K) → ℕ)
    (hpartition : (∑ i, badCount i) = Bad.card)
    (hsq : saving + 1 ≤ n - K) (hsN : saving + 1 ≤ n)
    (hbudget : (n - K) + (depth - 1) ≤ n - saving - 1) :
    ∃ i, goodBadWork n (n - K) (2 ^ (n - K)) (badCount i) (depth - 1)
      ≤ 2 ^ (n - saving) := by
  have hB : 0 < n.choose K := Nat.choose_pos hKn
  have hagg0 := block_switching_bad_dyadic cs w F K depth saving hcons hw
    hstars hbadDepth hdepthK hKn hr hrhs
  have hagg : (∑ i, badCount i) * 2 ^ (saving + 1)
      ≤ n.choose K * 2 ^ (n - K) := by
    rw [hpartition]
    exact hagg0
  exact aggregateTail_to_selectedBucket_activeGap n (n.choose K) (n - K) saving
    (depth - 1) hB hsq (Nat.sub_le n K) hsN badCount hagg hbudget

end PallLean.Paper93.DeepMath.PathB.ACC0BlockSwitchingDyadicIntegration

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BlockSwitchingDyadicIntegration.rational_dyadic_to_nat
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BlockSwitchingDyadicIntegration.block_switching_bad_dyadic
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BlockSwitchingDyadicIntegration.block_switching_to_selectedBucket_activeGap
