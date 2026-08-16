import PallLean.Paper93.DeepMath.PathB.ComputationalDepthObserverAlgorithmicSchema

/-!
# Observer-guided restriction decomposition: the exact SAT cash-out and a parity obstruction

This file formalizes the smallest decisive lemma selected by the Mikoshi Research Lab's observer-path audit.
It separates the programme into two clean pieces:

1. **proved arithmetic cash-out:** a restriction decomposition with at most `2^(n-saving)` leaves and leaf
   observer boundary at most `saving-1` gives a strict improvement over `2^n` brute force;
2. **proved obstruction to a naive potential:** the one-bit output boundary of a parity residual stays equal to one
   after every proper nonempty variable-fixing step.  Consequently, output-state entropy alone cannot pay for a
   restriction tree.  Any successful contraction lemma must charge circuit structure, reconvergence, a separator,
   or another intensional resource in addition to the final Boolean output.

The structural existence of such decompositions for threshold circuits or `ACC⁰[m]` remains the load-bearing open
theorem.  It is represented here only by concrete data and inequalities, never by an axiom or a theorem claiming it
for a circuit class.
-/

namespace PallLean.Paper93.DeepMath.PathB.ObserverRestrictionDecomposition

open PallLean.Paper93.DeepMath.PathB.ObserverAlgorithmic

/-- The numerical certificate exported by an observer-guided restriction decomposition.

`leafCount ≤ 2^(n-saving)` is the saving obtained from branching/restriction, while
`boundary ≤ saving-1` is the maximum number of observer bits needed to solve a leaf by DP. -/
structure Certificate where
  /-- original number of input variables -/
  n : ℕ
  /-- number of terminal residuals in the restriction tree -/
  leafCount : ℕ
  /-- observer-boundary bits used by the residual DP -/
  boundary : ℕ
  /-- exponent reserved to pay for the boundary computation -/
  saving : ℕ
  /-- the instance is nonempty -/
  npos : 1 ≤ n
  /-- at least one exponent is saved -/
  savingPos : 1 ≤ saving
  /-- the claimed saving does not exceed the input dimension -/
  savingLe : saving ≤ n
  /-- restriction-tree leaf bound -/
  leafBound : leafCount ≤ 2 ^ (n - saving)
  /-- residual observer-boundary bound -/
  boundaryBound : boundary ≤ saving - 1

/-- Work of solving every restriction-tree leaf by a `2^boundary` observer-state DP. -/
def restrictionDpTime (C : Certificate) : ℕ := C.leafCount * 2 ^ C.boundary

/-- The two exponent budgets exactly fill `n-1`: branching uses `n-saving`, while residual DP uses
`saving-1`. -/
theorem exponent_budget_eq (C : Certificate) :
    (C.n - C.saving) + (C.saving - 1) = C.n - 1 := by
  have hs := C.savingLe
  have hp := C.savingPos
  omega

/-- **Restriction decomposition cash-out (proved).**  The leaf saving and residual-boundary budget combine to put
the total DP work below brute force. -/
theorem restrictionDpTime_le_half_cube (C : Certificate) :
    restrictionDpTime C ≤ 2 ^ (C.n - 1) := by
  unfold restrictionDpTime
  calc
    C.leafCount * 2 ^ C.boundary
        ≤ 2 ^ (C.n - C.saving) * 2 ^ C.boundary :=
          Nat.mul_le_mul_right _ C.leafBound
    _ ≤ 2 ^ (C.n - C.saving) * 2 ^ (C.saving - 1) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) C.boundaryBound)
    _ = 2 ^ ((C.n - C.saving) + (C.saving - 1)) := by
          rw [Nat.pow_add]
    _ = 2 ^ (C.n - 1) := by rw [exponent_budget_eq C]

/-- **The selected observer path, fully cashed out.**  Every certificate satisfying the restriction-tree and
boundary inequalities gives a strict sub-brute-force SAT running time. -/
theorem restrictionDp_beats_bruteforce (C : Certificate) :
    restrictionDpTime C < bruteForceTime C.n := by
  unfold restrictionDpTime
  exact dpSat_beats_bruteforce C.npos (restrictionDpTime_le_half_cube C)

/-! ## Why plain output entropy cannot prove the needed contraction

For parity on `free` still-unfixed variables, the set of possible final outputs has two elements whenever at least
one variable remains.  Its base-two output entropy is therefore one bit until the last variable is fixed.  The
following tiny model isolates that obstruction without smuggling in a circuit representation.
-/

/-- One-bit output boundary of a parity residual: zero after all variables are fixed, one otherwise. -/
def parityOutputBoundary (free : ℕ) : ℕ := if free = 0 then 0 else 1

/-- Fixing fewer variables than remain leaves the naive parity output boundary unchanged. -/
theorem parity_output_boundary_no_local_contraction {free fixed : ℕ}
    (hfixed : fixed < free) :
    parityOutputBoundary (free - fixed) = parityOutputBoundary free := by
  have hfree : free ≠ 0 := by omega
  have hremain : free - fixed ≠ 0 := by omega
  simp [parityOutputBoundary, hfree, hremain]

/-- In particular, no proper restriction step earns even one unit of decrease from the output-only potential. -/
theorem parity_output_boundary_not_strictly_decreasing {free fixed : ℕ}
    (hfixed : fixed < free) :
    ¬ parityOutputBoundary (free - fixed) < parityOutputBoundary free := by
  rw [parity_output_boundary_no_local_contraction hfixed]
  exact Nat.lt_irrefl _

end PallLean.Paper93.DeepMath.PathB.ObserverRestrictionDecomposition

#print axioms PallLean.Paper93.DeepMath.PathB.ObserverRestrictionDecomposition.restrictionDp_beats_bruteforce
#print axioms PallLean.Paper93.DeepMath.PathB.ObserverRestrictionDecomposition.parity_output_boundary_no_local_contraction
