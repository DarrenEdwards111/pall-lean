import GodMoveBinaryDotProduct
import GodMoveBinaryScalarExecution
import GodMoveCachedArithmeticPrecision

/-!
# Executing cached dot calls on the binary backend

The returned sign and words come from the actual Boolean evaluator. For cached
component, residual, norm and residual-matrix dot calls, the existing readiness theorem supplies
the intermediate precision bound; it is not a new assumption on those calls.

The counter measures the evaluator's explicit wire scans, appends and output
reads. Packing operands, generating code, compiling queries and implementing
the evaluator on a uniform tape machine remain outside this counter. This is
a replacement theorem for individual dot calls, not a runtime theorem for the
complete adaptive construction, and does not assert a SAT derivative-rank bound.
-/

namespace GodMoveCachedBinaryDotExecution

open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer
open GodMoveRationalWireEncoding GodMoveBinaryDotProduct
open GodMoveBinaryScalarExecution GodMoveBooleanExecutionCost
open GodMoveDotLoopPrecision GodMoveTrackedOrthogonalizationCost
open GodMoveCachedDiscoveryBasis GodMoveCachedBasisPrecision
open GodMoveCachedArithmeticPrecision GodMoveTrackedArithmeticPrecision
open GodMoveTrackedOrthogonalization (Row rowValue)

def evaluateDot {n : ℕ} (inputs vals : List Bool) (b zeroRef : ℕ)
    (acc : FractionRefs) (pairs : List (FractionRefs × FractionRefs)) : Execution FractionBits :=
  let p := dotFrom (n := n) vals.length (b + 1) zeroRef acc pairs
  executeFraction inputs vals p.1 p.2

def dotSteps (s b I V : ℕ) : ℕ :=
  7 * (2048 * s * (b + 2) ^ 3) * (I + V + 2048 * s * (b + 2) ^ 3 + 1) +
    (2 * (b + 1) + 1) * (V + 2048 * s * (b + 2) ^ 3 + 2) + 1

theorem evaluateDot_represents {n s : ℕ} (inputs vals : List Bool)
    (b zeroRef : ℕ) (acc : FractionRefs) (v u : Fin s → ℚ)
    (pairs : List (FractionRefs × FractionRefs))
    (haw : Width acc (b + 1)) (hav : Valid acc vals.length)
    (ha : Represents vals acc 0) (hz : zeroRef < vals.length)
    (hzv : vals.getD zeroRef false = false)
    (hr : PairsRepresent vals (b + 1) pairs ((List.finRange s).map fun i => (v i, u i)))
    (hp : DotPrecision v u b) :
    (evaluateDot (n := n) inputs vals b zeroRef acc pairs).value.Represents
      (sumProducts v u).value := by
  apply executeFraction_represents
  exact dotFrom_sumProductsOn (fun i => inputs.getD i.val false)
    vals b zeroRef acc v u pairs haw hav ha hz hzv hr hp

theorem evaluateDot_steps_le {n s : ℕ} (inputs vals : List Bool)
    (b zeroRef : ℕ) (acc : FractionRefs) (v u : Fin s → ℚ)
    (pairs : List (FractionRefs × FractionRefs)) (haw : Width acc (b + 1))
    (hr : PairsRepresent vals (b + 1) pairs ((List.finRange s).map fun i => (v i, u i))) :
    (evaluateDot (n := n) inputs vals b zeroRef acc pairs).steps ≤
      dotSteps s b inputs.length vals.length := by
  have hw := dotFrom_width (n := n) vals.length (b + 1) zeroRef acc pairs haw
  apply executeFraction_steps_le inputs vals _ _
    (2048 * s * (b + 2) ^ 3) (2 * (b + 1) + 1)
  · exact dotFrom_sumProductsOn_gate_count vals.length b zeroRef acc vals v u pairs haw hr
  · rw [hw.1, hw.2]
    omega

theorem dotSteps_le_eighth_power (s b I V : ℕ) :
    dotSteps s b I V ≤ 40000000 * (I + V + s + b + 2) ^ 8 := by
  let S := I + V + s + b + 2
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hs : s ≤ S := by dsimp [S]; omega
  have hb : b + 2 ≤ S := by dsimp [S]; omega
  have hi : I + V + 2 ≤ S := by dsimp [S]; omega
  have h4 : S ≤ S ^ 4 := by
    calc S = S ^ 1 := by simp
         _ ≤ S ^ 4 := Nat.pow_le_pow_right hS (by decide)
  have h5 : S ^ 5 ≤ S ^ 8 := Nat.pow_le_pow_right hS (by decide)
  have hg : 2048 * s * (b + 2) ^ 3 ≤ 2048 * S ^ 4 := by
    calc
      _ ≤ (2048 * S) * S ^ 3 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hs) (Nat.pow_le_pow_left hb _)
      _ = _ := by ring
  have hinner : I + V + 2048 * s * (b + 2) ^ 3 + 1 ≤ 2049 * S ^ 4 := by omega
  have houter : V + 2048 * s * (b + 2) ^ 3 + 2 ≤ 2049 * S ^ 4 := by omega
  have hfirst : 7 * (2048 * s * (b + 2) ^ 3) *
      (I + V + 2048 * s * (b + 2) ^ 3 + 1) ≤ 29374464 * S ^ 8 := by
    calc
      _ ≤ (7 * (2048 * S ^ 4)) * (2049 * S ^ 4) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hg) hinner
      _ = _ := by ring
  have hsecond : (2 * (b + 1) + 1) *
      (V + 2048 * s * (b + 2) ^ 3 + 2) ≤ 6147 * S ^ 8 := by
    calc
      _ ≤ (3 * S) * (2049 * S ^ 4) :=
        Nat.mul_le_mul (by omega) houter
      _ = 6147 * S ^ 5 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ h5
  have h8 : 1 ≤ S ^ 8 := Nat.one_le_pow _ _ hS
  change dotSteps s b I V ≤ 40000000 * S ^ 8
  unfold dotSteps
  omega

theorem evaluateDot_correct_and_cost {n s : ℕ} (inputs vals : List Bool)
    (b zeroRef : ℕ) (acc : FractionRefs) (v u : Fin s → ℚ)
    (pairs : List (FractionRefs × FractionRefs))
    (haw : Width acc (b + 1)) (hav : Valid acc vals.length)
    (ha : Represents vals acc 0) (hz : zeroRef < vals.length)
    (hzv : vals.getD zeroRef false = false)
    (hr : PairsRepresent vals (b + 1) pairs ((List.finRange s).map fun i => (v i, u i)))
    (hp : DotPrecision v u b) :
    (evaluateDot (n := n) inputs vals b zeroRef acc pairs).value.value = (sumProducts v u).value ∧
    (evaluateDot (n := n) inputs vals b zeroRef acc pairs).steps ≤
      40000000 * (inputs.length + vals.length + s + b + 2) ^ 8 :=
  ⟨(evaluateDot_represents inputs vals b zeroRef acc v u pairs haw hav ha hz hzv hr hp).value_eq,
    (evaluateDot_steps_le inputs vals b zeroRef acc v u pairs haw hr).trans
      (dotSteps_le_eighth_power _ _ _ _)⟩

/-- The actual component-dot operands of a cached Boolean-row insertion. The
precision premise is discharged from readiness and Boolean input. -/
theorem cached_component_correct_and_cost {n s : ℕ}
    (B : CachedBasis s) (hB : Ready B) (v : Row s) (hv : BooleanRow (rowValue v))
    (i : Fin B.count) (inputs vals : List Bool) (zeroRef : ℕ) (acc : FractionRefs)
    (pairs : List (FractionRefs × FractionRefs))
    (haw : Width acc (arithmeticBits s + 1)) (hav : Valid acc vals.length)
    (ha : Represents vals acc 0) (hz : zeroRef < vals.length)
    (hzv : vals.getD zeroRef false = false)
    (hr : PairsRepresent vals (arithmeticBits s + 1) pairs
      ((List.finRange s).map fun j => (v[j], B.rows[i][j]))) :
    (evaluateDot (n := n) inputs vals (arithmeticBits s) zeroRef acc pairs).value.value =
      (sumProducts (fun j : Fin s => v[j]) (fun j => B.rows[i][j])).value ∧
    (evaluateDot (n := n) inputs vals (arithmeticBits s) zeroRef acc pairs).steps ≤
      40000000 * (inputs.length + vals.length + s + arithmeticBits s + 2) ^ 8 :=
  evaluateDot_correct_and_cost inputs vals (arithmeticBits s) zeroRef acc _ _ pairs
    haw hav ha hz hzv hr ((insert_precision B hB v hv).componentDots i)

/-- The residual-matrix dot loop uses at most the ambient number of rows, and
its precision is obtained from the same actual cached basis. -/
theorem cached_matrix_correct_and_cost {n s : ℕ}
    (B : CachedBasis s) (hB : Ready B) (j i : Fin s)
    (inputs vals : List Bool) (zeroRef : ℕ) (acc : FractionRefs)
    (pairs : List (FractionRefs × FractionRefs))
    (haw : Width acc (arithmeticBits s + 1)) (hav : Valid acc vals.length)
    (ha : Represents vals acc 0) (hz : zeroRef < vals.length)
    (hzv : vals.getD zeroRef false = false)
    (hr : PairsRepresent vals (arithmeticBits s + 1) pairs
      ((List.finRange B.count).map fun h =>
        ((GodMoveCachedResidualMatrix.scaledRows B).value[h][i], B.rows[h][j]))) :
    (evaluateDot (n := n) inputs vals (arithmeticBits s) zeroRef acc pairs).value.value =
      (sumProducts (fun h : Fin B.count =>
        (GodMoveCachedResidualMatrix.scaledRows B).value[h][i]) (fun h => B.rows[h][j])).value ∧
    (evaluateDot (n := n) inputs vals (arithmeticBits s) zeroRef acc pairs).steps ≤
      40000000 * (inputs.length + vals.length + s + arithmeticBits s + 2) ^ 8 := by
  have h := evaluateDot_correct_and_cost (n := n) inputs vals (arithmeticBits s) zeroRef acc
    _ _ pairs haw hav ha hz hzv hr ((matrix_precision B hB).dots j i)
  refine ⟨h.1, h.2.trans ?_⟩
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  have hc := count_le_width B
  omega

/-- The dot sum subtracted from one residual coordinate. Components are the
actual cached component values; readiness supplies every prefix bound. -/
theorem cached_residual_correct_and_cost {n s : ℕ}
    (B : CachedBasis s) (hB : Ready B) (v : Row s) (hv : BooleanRow (rowValue v))
    (j : Fin s) (inputs vals : List Bool) (zeroRef : ℕ) (acc : FractionRefs)
    (pairs : List (FractionRefs × FractionRefs))
    (haw : Width acc (arithmeticBits s + 1)) (hav : Valid acc vals.length)
    (ha : Represents vals acc 0) (hz : zeroRef < vals.length)
    (hzv : vals.getD zeroRef false = false)
    (hr : PairsRepresent vals (arithmeticBits s + 1) pairs
      ((List.finRange B.count).map fun i =>
        ((GodMoveTrackedOrthogonalizationCost.components v B.rows B.norms).value[i],
          B.rows[i][j]))) :
    (evaluateDot (n := n) inputs vals (arithmeticBits s) zeroRef acc pairs).value.value =
      (sumProducts (fun i : Fin B.count =>
        (GodMoveTrackedOrthogonalizationCost.components v B.rows B.norms).value[i])
        (fun i => B.rows[i][j])).value ∧
    (evaluateDot (n := n) inputs vals (arithmeticBits s) zeroRef acc pairs).steps ≤
      40000000 * (inputs.length + vals.length + s + arithmeticBits s + 2) ^ 8 := by
  have h := evaluateDot_correct_and_cost (n := n) inputs vals (arithmeticBits s) zeroRef acc
    _ _ pairs haw hav ha hz hzv hr ((insert_precision B hB v hv).residualDots j)
  refine ⟨h.1, h.2.trans ?_⟩
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  have hc := count_le_width B
  omega

/-- The squared residual norm is computed from the actual cached residual,
including a zero residual that will be rejected by insertion. -/
theorem cached_norm_correct_and_cost {n s : ℕ}
    (B : CachedBasis s) (hB : Ready B) (v : Row s) (hv : BooleanRow (rowValue v))
    (inputs vals : List Bool) (zeroRef : ℕ) (acc : FractionRefs)
    (pairs : List (FractionRefs × FractionRefs))
    (haw : Width acc (arithmeticBits s + 1)) (hav : Valid acc vals.length)
    (ha : Represents vals acc 0) (hz : zeroRef < vals.length)
    (hzv : vals.getD zeroRef false = false)
    (hr : PairsRepresent vals (arithmeticBits s + 1) pairs
      ((List.finRange s).map fun j =>
        ((GodMoveCachedDiscoveryBasis.residual B v).value[j],
          (GodMoveCachedDiscoveryBasis.residual B v).value[j]))) :
    (evaluateDot (n := n) inputs vals (arithmeticBits s) zeroRef acc pairs).value.value =
      (sumProducts (fun j : Fin s => (GodMoveCachedDiscoveryBasis.residual B v).value[j])
        (fun j => (GodMoveCachedDiscoveryBasis.residual B v).value[j])).value ∧
    (evaluateDot (n := n) inputs vals (arithmeticBits s) zeroRef acc pairs).steps ≤
      40000000 * (inputs.length + vals.length + s + arithmeticBits s + 2) ^ 8 :=
  evaluateDot_correct_and_cost inputs vals (arithmeticBits s) zeroRef acc _ _ pairs
    haw hav ha hz hzv hr (insert_precision B hB v hv).normDot

end GodMoveCachedBinaryDotExecution

#print axioms GodMoveCachedBinaryDotExecution.evaluateDot_represents
#print axioms GodMoveCachedBinaryDotExecution.evaluateDot_steps_le
#print axioms GodMoveCachedBinaryDotExecution.dotSteps_le_eighth_power
#print axioms GodMoveCachedBinaryDotExecution.evaluateDot_correct_and_cost
#print axioms GodMoveCachedBinaryDotExecution.cached_component_correct_and_cost
#print axioms GodMoveCachedBinaryDotExecution.cached_matrix_correct_and_cost
#print axioms GodMoveCachedBinaryDotExecution.cached_residual_correct_and_cost
#print axioms GodMoveCachedBinaryDotExecution.cached_norm_correct_and_cost
