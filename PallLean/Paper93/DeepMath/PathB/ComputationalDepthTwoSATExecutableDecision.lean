import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTwoSATSimpleWalkCutoff

/-!
# Total executable 2-SAT decision specification

The fixed-fuel reachability kernel now decides implication reachability exactly.  This file packages it into a total
Boolean 2-SAT decider and proves end-to-end correctness against `TwoSat`.

This is the trusted executable specification that a later Kosaraju implementation must refine.  Its bounded recursive
search is not claimed linear; separating specification correctness from traversal optimization keeps the complexity
claim honest.
-/

namespace PallLean.Paper93.DeepMath.PathB.TwoSATExecutableDecision

open PallLean.Paper93.DeepMath.PathB.TwoSATFastSAT
open PallLean.Paper93.DeepMath.PathB.TwoSATSCCLinearBudget
open PallLean.Paper93.DeepMath.PathB.TwoSATBoundedReachability
open PallLean.Paper93.DeepMath.PathB.TwoSATSimpleWalkCutoff.EdgeWalk

variable {n : ℕ}

/-- Fixed-fuel complementary SCC conflict at one literal. -/
def boundedConflict (cls : List (Clause n)) (l : Lit n) : Prop :=
  boundedReach (implicationEdges cls) (2 * n - 1) l (neg l) = true ∧
    boundedReach (implicationEdges cls) (2 * n - 1) (neg l) l = true

instance boundedConflictDecidable (cls : List (Clause n)) (l : Lit n) :
    Decidable (boundedConflict cls l) := by
  unfold boundedConflict
  infer_instance

/-- Total Boolean decider: accept iff no literal has a bounded complementary SCC conflict. -/
def decideTwoSAT (cls : List (Clause n)) : Bool :=
  decide (∀ l : Lit n, ¬boundedConflict cls l)

/-- Fixed-fuel conflict is exactly semantic mutual reachability. -/
theorem boundedConflict_iff (cls : List (Clause n)) (l : Lit n) :
    boundedConflict cls l ↔ Reach cls l (neg l) ∧ Reach cls (neg l) l := by
  unfold boundedConflict
  rw [boundedReach_cutoff_iff, boundedReach_cutoff_iff]

/-- The Boolean decider accepts exactly formulas satisfying the SCC criterion. -/
theorem decideTwoSAT_eq_true_iff_noContra (cls : List (Clause n)) :
    decideTwoSAT cls = true ↔ NoContra cls := by
  simp only [decideTwoSAT, decide_eq_true_eq, NoContra]
  constructor
  · intro h l hcontra
    exact h l ((boundedConflict_iff cls l).mpr hcontra)
  · intro h l hbounded
    exact h l ((boundedConflict_iff cls l).mp hbounded)

/-- **End-to-end executable 2-SAT correctness (proved).** -/
theorem decideTwoSAT_eq_true_iff (cls : List (Clause n)) :
    decideTwoSAT cls = true ↔ TwoSat cls := by
  rw [decideTwoSAT_eq_true_iff_noContra]
  exact (twosat_iff cls).symm

end PallLean.Paper93.DeepMath.PathB.TwoSATExecutableDecision

#print axioms PallLean.Paper93.DeepMath.PathB.TwoSATExecutableDecision.boundedConflict_iff
#print axioms PallLean.Paper93.DeepMath.PathB.TwoSATExecutableDecision.decideTwoSAT_eq_true_iff_noContra
#print axioms PallLean.Paper93.DeepMath.PathB.TwoSATExecutableDecision.decideTwoSAT_eq_true_iff
