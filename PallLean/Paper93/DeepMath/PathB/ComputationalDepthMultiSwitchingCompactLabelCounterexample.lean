import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMultiSwitchingWitnessLabel

/-!
# Counterexample to the proposed compact common-path reconstruction

Gate-run counts and per-term multiplicities do not identify the variables queried by a common
canonical path.  The one-term DNF `¬x₀ ∧ ¬x₁` already gives a collision: starting with `x₁ = 0`
queries `x₀`, while starting with `x₀ = 0` queries `x₁`.  Under the all-zero assignment both runs
have the same endpoint, bit transcript, gate-run count, and term-count table.
-/

namespace PallLean.Paper93.DeepMath.PathB.MultiSwitching.CompactLabelCounterexample

open PallLean.Paper93.DeepMath.PathB.Depth3
open PallLean.Paper93.DeepMath.PathB.SwitchingCounting
open PallLean.Paper93.DeepMath.PathB.MultiSwitching

def gate : Clause 2 :=
  ⟨[Rung4Literal.neg (0 : Fin 2), Rung4Literal.neg (1 : Fin 2)]⟩

def gates : Fin 1 → List (Clause 2) := fun _ => [gate]

def leftRoot : Restriction 2 := ![none, some false]
def rightRoot : Restriction 2 := ![some false, none]
def zeroAssignment : Fin 2 → Bool := ![false, false]

def leftTree := canonicalFamilyTree gates 1 leftRoot
def rightTree := canonicalFamilyTree gates 1 rightRoot

theorem roots_ne : leftRoot ≠ rightRoot := by decide

theorem endpoints_eq :
    CommonTree.pathEndpoint leftRoot leftTree zeroAssignment =
      CommonTree.pathEndpoint rightRoot rightTree zeroAssignment := by
  decide

theorem transcripts_eq :
    CommonTree.trace (CommonTree.readOnce leftRoot leftTree) zeroAssignment =
      CommonTree.trace (CommonTree.readOnce rightRoot rightTree) zeroAssignment := by
  decide

theorem gate_run_counts_eq :
    (commonGateRunCounts (fun g => canonicalDT (gates g) 1 leftRoot)
        zeroAssignment (0 : Fin 1)).1 =
      (commonGateRunCounts (fun g => canonicalDT (gates g) 1 rightRoot)
        zeroAssignment (0 : Fin 1)).1 := by
  decide

theorem term_counts_eq :
    (commonTermCounts gates 1 leftRoot zeroAssignment (0 : Fin 1) (0 : Fin 1)).1 =
      (commonTermCounts gates 1 rightRoot zeroAssignment (0 : Fin 1) (0 : Fin 1)).1 := by
  decide

theorem pathVars_ne :
    CommonTree.pathVars leftRoot leftTree zeroAssignment ≠
      CommonTree.pathVars rightRoot rightTree zeroAssignment := by
  decide

/-- The exact obstruction: all information stored by the proposed compact label agrees, while the
selected coordinate set required for endpoint reconstruction differs. -/
theorem compact_boundary_data_do_not_recover_pathVars :
    CommonTree.pathEndpoint leftRoot leftTree zeroAssignment =
        CommonTree.pathEndpoint rightRoot rightTree zeroAssignment ∧
      CommonTree.trace (CommonTree.readOnce leftRoot leftTree) zeroAssignment =
        CommonTree.trace (CommonTree.readOnce rightRoot rightTree) zeroAssignment ∧
      (commonGateRunCounts (fun g => canonicalDT (gates g) 1 leftRoot)
          zeroAssignment (0 : Fin 1)).1 =
        (commonGateRunCounts (fun g => canonicalDT (gates g) 1 rightRoot)
          zeroAssignment (0 : Fin 1)).1 ∧
      (commonTermCounts gates 1 leftRoot zeroAssignment (0 : Fin 1) (0 : Fin 1)).1 =
        (commonTermCounts gates 1 rightRoot zeroAssignment (0 : Fin 1) (0 : Fin 1)).1 ∧
      CommonTree.pathVars leftRoot leftTree zeroAssignment ≠
        CommonTree.pathVars rightRoot rightTree zeroAssignment :=
  ⟨endpoints_eq, transcripts_eq, gate_run_counts_eq, term_counts_eq, pathVars_ne⟩

end PallLean.Paper93.DeepMath.PathB.MultiSwitching.CompactLabelCounterexample

#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CompactLabelCounterexample.compact_boundary_data_do_not_recover_pathVars
