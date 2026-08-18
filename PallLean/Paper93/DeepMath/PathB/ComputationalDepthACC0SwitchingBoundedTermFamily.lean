import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SwitchingBoundedTermTail

/-!
# Parameterized bounded-term canonical-depth switching family

This file abstracts the corrected one- and two-term instances.  All objects use the actual
single-literal `canonicalDT` maximum depth.  The only numerical premise is the explicit finite sum
of witnessed fixed-shell bounds; no probability shorthand or block-stream surrogate remains.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SwitchingBoundedTermFamily

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.Depth3
open PallLean.Paper93.DeepMath.PathB.SwitchingCounting
open PallLean.Paper93.DeepMath.PathB.ACC0SwitchingBoundedTermTail
open PallLean.Paper93.DeepMath.PathB.ACC0SwitchingShellBuckets
open PallLean.Paper93.DeepMath.PathB.ACC0SwitchingShellAveraging
open PallLean.Paper93.DeepMath.PathB.ACC0GoodBadSwitchingCashout

/-- Actual bad restrictions in the `K`-star shell at canonical depth threshold `threshold`. -/
def boundedTermBad {n : ℕ} (cs : List (Clause n)) (K threshold : ℕ) :
    Finset (Restriction n) :=
  Finset.univ.filter fun ρ => stars ρ = K ∧ threshold ≤ (canonicalDT cs K ρ).depth

theorem mem_boundedTermBad_iff {n : ℕ} (cs : List (Clause n)) (K threshold : ℕ)
    (ρ : Restriction n) :
    ρ ∈ boundedTermBad cs K threshold ↔
      stars ρ = K ∧ threshold ≤ (canonicalDT cs K ρ).depth := by
  simp [boundedTermBad]

/-- The corrected bad set partitions into all exact canonical-depth shells from `threshold` to `K`. -/
theorem boundedTermBad_card_eq_shell_sum {n : ℕ} (cs : List (Clause n)) (K threshold : ℕ) :
    (boundedTermBad cs K threshold).card =
      ∑ t ∈ Finset.Icc threshold K,
        ((boundedTermBad cs K threshold).filter fun ρ =>
          (canonicalDT cs K ρ).depth = t).card := by
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun ρ : Restriction n => (canonicalDT cs K ρ).depth)
    (t := Finset.Icc threshold K)]
  intro ρ hρ
  have hρ' : ρ ∈ boundedTermBad cs K threshold := hρ
  rw [mem_boundedTermBad_iff] at hρ'
  exact Finset.mem_Icc.mpr ⟨hρ'.2, canonicalDT_depth_le cs K ρ⟩

/-- The full fixed-shell cardinal tail obtained by summing the unconditional witnessed count over
every possible bad canonical depth. -/
theorem boundedTermBad_card_le_shellSum
    {n w m : ℕ} [NeZero w] [NeZero m]
    (cs : List (Clause n)) (K threshold : ℕ)
    (hw : ∀ T ∈ cs, T.lits.length ≤ w) (hm : cs.length ≤ m) :
    (boundedTermBad cs K threshold).card ≤
      ∑ t ∈ Finset.Icc threshold K,
        n.choose (K - t) * 2 ^ (n - (K - t)) * (2 * w * m) ^ t := by
  rw [boundedTermBad_card_eq_shell_sum]
  apply Finset.sum_le_sum
  intro t ht
  apply canonicalDepth_shell_count_witness cs hw hm
  · intro ρ hρ
    have hbad : ρ ∈ boundedTermBad cs K threshold := (Finset.mem_filter.mp hρ).1
    exact (mem_boundedTermBad_iff cs K threshold ρ).mp hbad |>.1
  · intro ρ hρ
    exact (Finset.mem_filter.mp hρ).2

/-- Outside the parameterized bad set, the canonical tree is genuinely shallower than `threshold`
and its CNF conversion computes the same residual DNF on the whole restricted subcube. -/
theorem boundedTerm_good_semanticCollapse
    {n : ℕ} (cs : List (Clause n)) (K threshold : ℕ)
    (ρ : Restriction n) (hstars : stars ρ = K)
    (hgood : ρ ∉ boundedTermBad cs K threshold) :
    (∀ x, DTree.agreeRestriction ρ x →
        cnfValue (dtreeToCNF (toDTree (canonicalDT cs K ρ))) x = DTree.dnfValue cs x)
      ∧ (∀ C ∈ dtreeToCNF (toDTree (canonicalDT cs K ρ)),
          C.lits.length < threshold) := by
  have hshallow : (canonicalDT cs K ρ).depth < threshold := by
    rw [mem_boundedTermBad_iff] at hgood
    simp only [hstars, true_and, not_le] at hgood
    exact hgood
  exact collapse_core_tight K threshold cs (ρ := ρ) (by omega) hshallow

/-- **Parameterized corrected selected-bucket speedup.**

The explicit `hshellBudget` is precisely the sum of all witnessed canonical-depth shell bounds,
scaled by the dyadic exceptional denominator.  Once it fits the fixed-`K` shell, concrete bucket
averaging and fully charged good/bad work yield exponent saving `saving`. -/
theorem boundedTerm_selectedBucket_activeGap
    {n w m K threshold saving : ℕ} [NeZero w] [NeZero m]
    (cs : List (Clause n))
    (hw : ∀ T ∈ cs, T.lits.length ≤ w) (hm : cs.length ≤ m)
    (hKn : K ≤ n) (hsq : saving + 1 ≤ n - K) (hsN : saving + 1 ≤ n)
    (hwork : (n - K) + (threshold - 1) ≤ n - saving - 1)
    (hshellBudget :
      (∑ t ∈ Finset.Icc threshold K,
          n.choose (K - t) * 2 ^ (n - (K - t)) * (2 * w * m) ^ t)
          * 2 ^ (saving + 1)
        ≤ n.choose K * 2 ^ (n - K)) :
    ∃ i : Fin (n.choose K),
      goodBadWork n (n - K) (2 ^ (n - K))
        (concreteBadCount (K := K) (boundedTermBad cs K threshold) i) (threshold - 1)
        ≤ 2 ^ (n - saving) := by
  have hstars : ∀ ρ ∈ boundedTermBad cs K threshold, stars ρ = K := by
    intro ρ hρ
    exact (mem_boundedTermBad_iff cs K threshold ρ).mp hρ |>.1
  have hsum := sum_concreteBadCount (Bad := boundedTermBad cs K threshold) hstars
  have hcard := boundedTermBad_card_le_shellSum cs K threshold hw hm
  have htail : (boundedTermBad cs K threshold).card * 2 ^ (saving + 1)
      ≤ n.choose K * 2 ^ (n - K) :=
    le_trans (Nat.mul_le_mul_right _ hcard) hshellBudget
  refine aggregateTail_to_selectedBucket_activeGap n (n.choose K) (n - K) saving
    (threshold - 1) (Nat.choose_pos hKn) hsq (Nat.sub_le n K) hsN
    (concreteBadCount (K := K) (boundedTermBad cs K threshold)) ?_ hwork
  simpa [hsum] using htail

end PallLean.Paper93.DeepMath.PathB.ACC0SwitchingBoundedTermFamily

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingBoundedTermFamily.boundedTermBad_card_le_shellSum
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingBoundedTermFamily.boundedTerm_good_semanticCollapse
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingBoundedTermFamily.boundedTerm_selectedBucket_activeGap
