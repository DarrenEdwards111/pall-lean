import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SwitchingBoundedTermFamily

/-!
# A corrected nine-bit switching speedup

For a width-two DNF with at most one term on 1000 variables, twenty free coordinates and genuine
canonical-depth threshold ten fund an exponent saving of nine.  The exceptional set is the actual
maximum-depth bad set, and every exceptional restriction remains fully charged.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SwitchingNineBitSaving

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.Depth3
open PallLean.Paper93.DeepMath.PathB.SwitchingCounting
open PallLean.Paper93.DeepMath.PathB.ACC0SwitchingBoundedTermFamily
open PallLean.Paper93.DeepMath.PathB.ACC0SwitchingShellBuckets
open PallLean.Paper93.DeepMath.PathB.ACC0GoodBadSwitchingCashout

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 2000

/-- The exact depth-10-through-20 witnessed shell sum fits the ten-bit dyadic denominator. -/
theorem oneTerm_nineBit_shellBudget :
    (∑ t ∈ Finset.Icc 10 20,
        (1000).choose (20 - t) * 2 ^ (1000 - (20 - t)) * (2 * 2 * 1) ^ t)
        * 2 ^ (9 + 1)
      ≤ (1000).choose 20 * 2 ^ (1000 - 20) := by
  norm_num (config := { maxSteps := 1000000 }) [Finset.sum_Icc_succ_top, Nat.choose]

/-- Every good restriction has genuine canonical depth below ten and hence an equivalent CNF of
clause width below ten on its whole restricted subcube. -/
theorem oneTerm_nineBit_good_semanticCollapse
    (cs : List (Clause 1000)) (ρ : Restriction 1000)
    (hstars : stars ρ = 20) (hgood : ρ ∉ boundedTermBad cs 20 10) :
    (∀ x, DTree.agreeRestriction ρ x →
        cnfValue (dtreeToCNF (toDTree (canonicalDT cs 20 ρ))) x = DTree.dnfValue cs x)
      ∧ (∀ C ∈ dtreeToCNF (toDTree (canonicalDT cs 20 ρ)), C.lits.length < 10) :=
  boundedTerm_good_semanticCollapse cs 20 10 ρ hstars hgood

/-- **Fully corrected nine-bit active-variable gap.** -/
theorem oneTerm_nineBit_selectedBucket_activeGap
    (cs : List (Clause 1000))
    (hw : ∀ T ∈ cs, T.lits.length ≤ 2) (hm : cs.length ≤ 1) :
    ∃ i : Fin ((1000).choose 20),
      goodBadWork 1000 (1000 - 20) (2 ^ (1000 - 20))
        (concreteBadCount (K := 20) (boundedTermBad cs 20 10) i) (10 - 1)
        ≤ 2 ^ (1000 - 9) := by
  apply boundedTerm_selectedBucket_activeGap cs hw hm
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact oneTerm_nineBit_shellBudget

/-- The doubled parameter regime satisfies the full depth-20-through-40 shell budget. -/
theorem oneTerm_eighteenBit_shellBudget :
    (∑ t ∈ Finset.Icc 20 40,
        (2000).choose (40 - t) * 2 ^ (2000 - (40 - t)) * (2 * 2 * 1) ^ t)
        * 2 ^ (18 + 1)
      ≤ (2000).choose 40 * 2 ^ (2000 - 40) := by
  norm_num (config := { maxSteps := 1000000 }) [Finset.sum_Icc_succ_top, Nat.choose]

/-- **The corrected speedup amplifies to an eighteen-bit active-variable gap.** -/
theorem oneTerm_eighteenBit_selectedBucket_activeGap
    (cs : List (Clause 2000))
    (hw : ∀ T ∈ cs, T.lits.length ≤ 2) (hm : cs.length ≤ 1) :
    ∃ i : Fin ((2000).choose 40),
      goodBadWork 2000 (2000 - 40) (2 ^ (2000 - 40))
        (concreteBadCount (K := 40) (boundedTermBad cs 40 20) i) (20 - 1)
        ≤ 2 ^ (2000 - 18) := by
  apply boundedTerm_selectedBucket_activeGap cs hw hm
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact oneTerm_eighteenBit_shellBudget

end PallLean.Paper93.DeepMath.PathB.ACC0SwitchingNineBitSaving

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingNineBitSaving.oneTerm_nineBit_shellBudget
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingNineBitSaving.oneTerm_nineBit_good_semanticCollapse
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingNineBitSaving.oneTerm_nineBit_selectedBucket_activeGap
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingNineBitSaving.oneTerm_eighteenBit_shellBudget
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingNineBitSaving.oneTerm_eighteenBit_selectedBucket_activeGap
