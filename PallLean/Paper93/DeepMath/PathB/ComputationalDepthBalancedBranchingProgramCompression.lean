import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTimeUnrolledTensorNetwork
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBranchingProgramWidth

/-!
# Exact log-depth compression of bounded-width branching programs

For a fixed input, every level of a width-`w` leveled branching program is an
endomorphism of `Fin w`.  Balanced composition of `2^d` consecutive level maps
has depth `d`, preserves the exact terminal state, and uses state wires of
cardinality `w`.
-/

namespace PallLean.Paper93.DeepMath.PathB.BalancedBranchingProgramCompression

open PallLean.Paper93.DeepMath.PathB.BranchingProgram
open PallLean.Paper93.DeepMath.PathB.TimeUnrolledTensorNetwork

/-- The transition endomorphism at one branching-program level after fixing the
input assignment. -/
def levelTransition {n w : Nat} (P : LevBP n w) (input : Fin n → Bool)
    (level : Nat) : Fin w → Fin w :=
  fun state => P.δ level state (input (P.var level))

theorem runSequence_levelTransition_eq_runFrom {n w : Nat}
    (P : LevBP n w) (input : Fin n → Bool) (state : Fin w)
    (offset count : Nat) :
    runSequence (levelTransition P input) offset count state =
      P.runFrom input state offset count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [runSequence, LevBP.runFrom, levelTransition, ih]

/-- A `2^d`-level prefix is exactly represented by a balanced composition tree
of depth `d`. -/
theorem balanced_prefix_terminal {n w : Nat}
    (P : LevBP n w) (input : Fin n → Bool) (d : Nat) :
    (CompositionTree.balancedRange (levelTransition P input) 0 d).eval P.start =
      P.runUpto input (2 ^ d) := by
  rw [CompositionTree.balancedRange_eval,
    runSequence_levelTransition_eq_runFrom]
  induction (2 ^ d) with
  | zero => rfl
  | succ k ih =>
      simp only [LevBP.runFrom, LevBP.runUpto, Nat.zero_add, ih]

/-- The contraction depth of the exact prefix representation is logarithmic in
its `2^d` represented levels. -/
theorem balanced_prefix_height {n w : Nat}
    (P : LevBP n w) (input : Fin n → Bool) (d : Nat) :
    (CompositionTree.balancedRange (levelTransition P input) 0 d).height = d :=
  CompositionTree.balancedRange_height _ _ _

/-- Every internal state wire ranges over exactly the branching-program width. -/
theorem branchingProgram_bondDimension (w : Nat) :
    bondDimension (Fin w) = w := by
  simp [bondDimension]

end PallLean.Paper93.DeepMath.PathB.BalancedBranchingProgramCompression

#print axioms PallLean.Paper93.DeepMath.PathB.BalancedBranchingProgramCompression.balanced_prefix_terminal
#print axioms PallLean.Paper93.DeepMath.PathB.BalancedBranchingProgramCompression.balanced_prefix_height
#print axioms PallLean.Paper93.DeepMath.PathB.BalancedBranchingProgramCompression.branchingProgram_bondDimension
