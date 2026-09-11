import GodMoveCachedResidualMatrix
import GodMoveMachineRowFinder

/-!
# SAT row queries from a materialized residual matrix

One numeric residual matrix is constructed and retained before scanning its
rows. Rational coefficient reads in precision checks and query compilation
then use stored entries. The same adaptive witness searches return exactly
the old row finder's assignment and query count.

The additional counter charges matrix construction only; rational clearing,
query-circuit construction, SAT execution and bit-level costs are separate.
-/

namespace GodMoveCachedRowFinder

open GodMoveBooleanInterpolation GodMoveCachedDiscoveryBasis
open GodMoveCachedResidualMatrix
open GodMoveTrackedOrthogonalization (Row rowValue)
open GodMoveTrackedOrthogonalizationCost (Counted)
open GodMoveRationalMachineQuery GodMoveResidualQueries
open PallLean.Paper93.DeepMath.PathB
open NFrameBoundaryTransducer (CGate)
open ComposableMachine

def findIn (M : Machine) (T : ℕ → ℕ) {n : ℕ} (c : List (CGate n))
    (Q : Vector (Row c.length) c.length) :
    List (Fin c.length) → Option (Assignment n) × ℕ
  | [] => (none, 0)
  | j :: js =>
      let q := rowValue Q[j]
      let attempt := rationalWitnessWithCount M T c q (coefficientBits q)
      match attempt.1 with
      | some a => (some a, attempt.2)
      | none =>
          let rest := findIn M T c Q js
          (rest.1, attempt.2 + rest.2)

theorem findIn_value (M : Machine) (T : ℕ → ℕ) {n : ℕ} (c : List (CGate n))
    (B : CachedBasis c.length) (Q : Vector (Row c.length) c.length)
    (hQ : ∀ j, rowValue Q[j] = residualCoefficients B.toRowBasis j)
    (js : List (Fin c.length)) :
    findIn M T c Q js = GodMoveMachineRowFinder.findIn M T c B.toRowBasis js := by
  induction js with
  | nil => rfl
  | cons j js ih =>
      simp only [findIn, hQ, GodMoveMachineRowFinder.findIn,
        GodMoveMachineRowFinder.rowAttempt, ih]
      rfl

def findRowWithCount (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) (B : CachedBasis c.length) :
    Counted (Option (Assignment n) × ℕ) :=
  let Q := residualMatrix B
  ⟨findIn M T c Q.value (List.ofFn (fun j : Fin c.length => j)), Q.operations⟩

theorem findRowWithCount_value (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) (B : CachedBasis c.length) :
    (findRowWithCount M T c B).value =
      GodMoveMachineRowFinder.findRowWithCount M T c B.toRowBasis := by
  apply findIn_value
  intro j
  funext i
  exact residualMatrix_value B j i

theorem findRowWithCount_operations_le (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) (B : CachedBasis c.length) :
    (findRowWithCount M T c B).operations ≤ 4 * (c.length + 1) ^ 3 :=
  residualMatrix_operations_le_cubic B

end GodMoveCachedRowFinder

#print axioms GodMoveCachedRowFinder.findIn_value
#print axioms GodMoveCachedRowFinder.findRowWithCount_value
#print axioms GodMoveCachedRowFinder.findRowWithCount_operations_le
