import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseCoreTight

/-!
# Depth-corrected switching bridge

The block-stream count controls one chosen killing path and cannot bound maximum decision-tree depth.
This file therefore defines failure using the actual single-literal `canonicalDT` depth.  Outside that
bad set, the already-proved semantic collapse core turns the residual DNF into an equivalent CNF whose
clauses have width below three.  This is the correct interface to a verified 2-SAT solver.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SwitchingDepthCorrectedBridge

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.Depth3
open PallLean.Paper93.DeepMath.PathB.SwitchingCounting

set_option maxRecDepth 10000

/-- Actual failures: five-star restrictions whose canonical max-branch depth is at least three. -/
def depthCorrectBad (cs : List (Clause 100)) : Finset (Restriction 100) :=
  Finset.univ.filter fun ρ => stars ρ = 5 ∧ 3 ≤ (canonicalDT cs 5 ρ).depth

theorem mem_depthCorrectBad_iff (cs : List (Clause 100)) (ρ : Restriction 100) :
    ρ ∈ depthCorrectBad cs ↔ stars ρ = 5 ∧ 3 ≤ (canonicalDT cs 5 ρ).depth := by
  simp [depthCorrectBad]

/-- A five-star restriction outside the corrected bad set has genuinely shallow canonical depth. -/
theorem canonicalDT_depth_lt_three_of_good (cs : List (Clause 100))
    (ρ : Restriction 100) (hstars : stars ρ = 5) (hgood : ρ ∉ depthCorrectBad cs) :
    (canonicalDT cs 5 ρ).depth < 3 := by
  rw [mem_depthCorrectBad_iff] at hgood
  simp only [hstars, true_and, not_le] at hgood
  exact hgood

/-- **Sound semantic bridge for good restrictions.**  The residual DNF is represented on the whole
`ρ`-subcube by a CNF all of whose clauses have width at most two.  Unlike the refuted block-stream
bridge, the premise is the actual maximum depth of the very tree used by `collapse_core_tight`. -/
theorem good_restriction_collapses_to_twoCNF (cs : List (Clause 100))
    (ρ : Restriction 100) (hstars : stars ρ = 5) (hgood : ρ ∉ depthCorrectBad cs) :
    (∀ x, DTree.agreeRestriction ρ x →
        cnfValue (dtreeToCNF (toDTree (canonicalDT cs 5 ρ))) x = DTree.dnfValue cs x)
      ∧ (∀ C ∈ dtreeToCNF (toDTree (canonicalDT cs 5 ρ)), C.lits.length ≤ 2) := by
  have hcollapse := collapse_core_tight 5 3 cs (ρ := ρ) (by omega)
    (canonicalDT_depth_lt_three_of_good cs ρ hstars hgood)
  refine ⟨hcollapse.1, ?_⟩
  intro C hC
  exact Nat.le_of_lt_succ (hcollapse.2 C hC)

/-- The corrected bad set is exactly the disjoint sum of depth shells three, four, and five. -/
theorem depthCorrectBad_card_eq_shell_sum (cs : List (Clause 100)) :
    (depthCorrectBad cs).card =
      ∑ s ∈ Finset.Icc 3 5,
        ((depthCorrectBad cs).filter fun ρ => (canonicalDT cs 5 ρ).depth = s).card := by
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun ρ : Restriction 100 => (canonicalDT cs 5 ρ).depth)
    (t := Finset.Icc 3 5)]
  intro ρ hρ
  have hρ' : ρ ∈ depthCorrectBad cs := hρ
  rw [mem_depthCorrectBad_iff] at hρ'
  exact Finset.mem_Icc.mpr ⟨hρ'.2, canonicalDT_depth_le cs 5 ρ⟩

/-- At the natural five-star density `p = 1/20`, the available unconditional F-independent
canonical-depth cap for width two is already greater than one at depth three.  Consequently that
theorem cannot supply the `1/8` tail used by the earlier block-stream arithmetic. -/
theorem naturalDensity_findep_cap_not_dyadic :
    ¬ (((2 * (1 / 20 : ℚ) / (1 - (1 / 20 : ℚ))) * (4 * 2 + 1)) ^ 3
          / (1 - (2 * (1 / 20 : ℚ) / (1 - (1 / 20 : ℚ))) * (4 * 2 + 1))
        ≤ 1 / (2 ^ 3 : ℚ)) := by
  norm_num

end PallLean.Paper93.DeepMath.PathB.ACC0SwitchingDepthCorrectedBridge

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingDepthCorrectedBridge.good_restriction_collapses_to_twoCNF
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingDepthCorrectedBridge.depthCorrectBad_card_eq_shell_sum
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingDepthCorrectedBridge.naturalDensity_findep_cap_not_dyadic
