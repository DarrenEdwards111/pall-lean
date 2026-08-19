import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SwitchingTailIntegerBridge

/-!
# Shell-to-algorithm bridge: average over free-variable sets

The repository's fixed-`K` switching bounds count bad restrictions over the entire `K`-star shell.
That shell mixes all choices of the `K` free variables.  A deterministic SAT decomposition instead
chooses one free-variable set and enumerates the `2^q` assignments to its `q = N-K` fixed variables.

This file supplies the missing averaging step.  If an aggregate dyadic tail holds after summing bad
counts over all free-variable-set buckets, at least one bucket satisfies the same dyadic tail.  The
previous integer bridge then converts that bucket's tail into the exact exceptional-assignment count
needed by the good/bad SAT theorem.

The result is deliberately distribution-agnostic: a concrete shell theorem only has to identify its
finite bucket type and prove the aggregate cross-multiplied inequality.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SwitchingShellAveraging

open PallLean.Paper93.DeepMath.PathB.ACC0SwitchingTailIntegerBridge

/-- If the sum of `B>0` bucket counts is at most `B*target`, some bucket is at most `target`. -/
theorem exists_bucket_le_average (B target : ℕ) (hB : 0 < B) (count : Fin B → ℕ)
    (hsum : (∑ i, count i) ≤ B * target) :
    ∃ i, count i ≤ target := by
  by_contra h
  push_neg at h
  have hlower : B * (target + 1) ≤ ∑ i, count i := by
    calc
      B * (target + 1) = ∑ _i : Fin B, (target + 1) := by simp
      _ ≤ ∑ i, count i := Finset.sum_le_sum fun i _ => h i
  have hstrict : B * target < B * (target + 1) := by nlinarith
  omega

/-- Multiplication by the dyadic tail denominator commutes with the bucket sum. -/
theorem sum_scaled (B scale : ℕ) (count : Fin B → ℕ) :
    (∑ i, count i * scale) = (∑ i, count i) * scale := by
  rw [Finset.sum_mul]

/-- **Aggregate shell tail to one deterministic bucket.**  If the total bad count, scaled by
`2^(saving+1)`, is at most `B*2^q`, one free-set bucket has the dyadic tail required by the SAT
algorithm. -/
theorem exists_bucket_dyadic_tail (B q saving : ℕ) (hB : 0 < B)
    (badCount : Fin B → ℕ)
    (haggregate : (∑ i, badCount i) * 2 ^ (saving + 1) ≤ B * 2 ^ q) :
    ∃ i, badCount i * 2 ^ (saving + 1) ≤ 2 ^ q := by
  apply exists_bucket_le_average B (2 ^ q) hB
    (fun i => badCount i * 2 ^ (saving + 1))
  rw [sum_scaled]
  exact haggregate

/-- The selected bucket has the exact integer bad-assignment bound. -/
theorem exists_bucket_badCount_le (B q saving : ℕ) (hB : 0 < B)
    (hsq : saving + 1 ≤ q) (badCount : Fin B → ℕ)
    (haggregate : (∑ i, badCount i) * 2 ^ (saving + 1) ≤ B * 2 ^ q) :
    ∃ i, badCount i ≤ 2 ^ (q - saving - 1) := by
  obtain ⟨i, hi⟩ := exists_bucket_dyadic_tail B q saving hB badCount haggregate
  exact ⟨i, badCount_le_of_dyadic_tail q saving (badCount i) hsq hi⟩

/-- End-to-end selected-bucket speedup: an aggregate shell tail selects one deterministic
free-variable set whose good/bad decomposition satisfies the active-normalized SAT bound. -/
theorem aggregateTail_to_selectedBucket_activeGap
    (N B q saving residualDepth : ℕ) (hB : 0 < B)
    (hsq : saving + 1 ≤ q) (hq : q ≤ N) (hsN : saving + 1 ≤ N)
    (badCount : Fin B → ℕ)
    (haggregate : (∑ i, badCount i) * 2 ^ (saving + 1) ≤ B * 2 ^ q)
    (hdepth : q + residualDepth ≤ N - saving - 1) :
    ∃ i, PallLean.Paper93.DeepMath.PathB.ACC0GoodBadSwitchingCashout.goodBadWork
        N q (2 ^ q) (badCount i) residualDepth ≤ 2 ^ (N - saving) := by
  obtain ⟨i, hi⟩ := exists_bucket_dyadic_tail B q saving hB badCount haggregate
  refine ⟨i, switchingTail_to_activeGap N q (2 ^ q) (badCount i) residualDepth saving
    hq hsN hsq (le_rfl) hdepth hi⟩

/-- The recursive form of selected-bucket averaging.  One and the same bucket carries both the
explicit exceptional-assignment bound and the complete good/bad work bound.  Keeping the witness
shared is essential when good children are recursively spliced while bad children stop here. -/
theorem aggregateTail_to_selectedBucket_certificate
    (N B q saving residualDepth : ℕ) (hB : 0 < B)
    (hsq : saving + 1 ≤ q) (hq : q ≤ N) (hsN : saving + 1 ≤ N)
    (badCount : Fin B → ℕ)
    (haggregate : (∑ i, badCount i) * 2 ^ (saving + 1) ≤ B * 2 ^ q)
    (hdepth : q + residualDepth ≤ N - saving - 1) :
    ∃ i, badCount i ≤ 2 ^ (q - saving - 1) ∧
      PallLean.Paper93.DeepMath.PathB.ACC0GoodBadSwitchingCashout.goodBadWork
        N q (2 ^ q) (badCount i) residualDepth ≤ 2 ^ (N - saving) := by
  obtain ⟨i, hi⟩ := exists_bucket_dyadic_tail B q saving hB badCount haggregate
  refine ⟨i, badCount_le_of_dyadic_tail q saving (badCount i) hsq hi, ?_⟩
  exact switchingTail_to_activeGap N q (2 ^ q) (badCount i) residualDepth saving
    hq hsN hsq (le_rfl) hdepth hi

end PallLean.Paper93.DeepMath.PathB.ACC0SwitchingShellAveraging

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingShellAveraging.exists_bucket_le_average
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingShellAveraging.exists_bucket_dyadic_tail
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingShellAveraging.exists_bucket_badCount_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingShellAveraging.aggregateTail_to_selectedBucket_activeGap
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingShellAveraging.aggregateTail_to_selectedBucket_certificate
