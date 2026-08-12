import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeProgressRecordClear
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeUniversalPassedShift

/-! # Fixed outer progress round -/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeFixedOuterRound

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeUniversalPassedShift
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeProgressReturn

set_option maxHeartbeats 4000000

/-- One exact outer round when an ordinary progress mark remains. -/
theorem runtimeFixedOuterRound_more (pre tail bits : List Bool) :
    let block := passedSourceBlock bits
    let T0 := pre ++ [true, false, true, false, false, false] ++
      flattenPairs block ++ tail
    let T1 := pre ++ [true, false, true, false] ++
      flattenPairs block ++ [false, false] ++ tail
    let T2 := pre ++ [true, false, false, false] ++
      flattenPairs block ++ [false, false] ++ tail
    (run runtimeUniversalPassedShiftMachine (8 * block.length)
        ⟨runtimeUniversalPassedShiftMachine.start, pre.length + 4, T0⟩ =
      ⟨RuntimeUniversalPassedShiftState.done,
        pre.length + 4 + 2 * block.length, T1⟩) ∧
    (run runtimeProgressReturnMachine (1 + 2 * block.length + 3)
        ⟨runtimeProgressReturnMachine.start,
          pre.length + 4 + 2 * block.length, T1⟩ =
      ⟨RuntimeProgressReturnState.done, pre.length + 2, T2⟩) ∧
    (run runtimeProgressExhaustMachine 2
        ⟨runtimeProgressExhaustMachine.start, pre.length + 2, T2⟩ =
      ⟨RuntimeProgressExhaustState.more, pre.length + 2, T2⟩) := by
  dsimp only
  constructor
  · have h := runtimeUniversalPassedShift_passedSourceBlock
      (pre ++ [true, false, true, false]) tail bits
    simpa [List.append_assoc, Nat.add_assoc] using h
  constructor
  · have h := runtimeProgressReturn_passed_progress
      (pre ++ [true, false]) tail bits
    simpa [List.append_assoc, Nat.add_assoc] using h
  · have h := runtimeProgressExhaust_more pre
      (flattenPairs (passedSourceBlock bits) ++ [false, false] ++ tail)
    simpa [List.append_assoc, Nat.add_assoc] using h

/-- The final outer round consumes the last `10` and then the `01` sentinel. -/
theorem runtimeFixedOuterRound_final (pre tail bits : List Bool) :
    let block := passedSourceBlock bits
    let T0 := pre ++ [false, true, true, false, false, false] ++
      flattenPairs block ++ tail
    let T1 := pre ++ [false, true, true, false] ++
      flattenPairs block ++ [false, false] ++ tail
    let T2 := pre ++ [false, true, false, false] ++
      flattenPairs block ++ [false, false] ++ tail
    let T3 := pre ++ [false, false, false, false] ++
      flattenPairs block ++ [false, false] ++ tail
    (run runtimeUniversalPassedShiftMachine (8 * block.length)
        ⟨runtimeUniversalPassedShiftMachine.start, pre.length + 4, T0⟩ =
      ⟨RuntimeUniversalPassedShiftState.done,
        pre.length + 4 + 2 * block.length, T1⟩) ∧
    (run runtimeProgressReturnMachine (1 + 2 * block.length + 3)
        ⟨runtimeProgressReturnMachine.start,
          pre.length + 4 + 2 * block.length, T1⟩ =
      ⟨RuntimeProgressReturnState.done, pre.length + 2, T2⟩) ∧
    (run runtimeProgressExhaustMachine 3
        ⟨runtimeProgressExhaustMachine.start, pre.length + 2, T2⟩ =
      ⟨RuntimeProgressExhaustState.final, pre.length + 1, T3⟩) := by
  dsimp only
  constructor
  · have h := runtimeUniversalPassedShift_passedSourceBlock
      (pre ++ [false, true, true, false]) tail bits
    simpa [List.append_assoc, Nat.add_assoc] using h
  constructor
  · have h := runtimeProgressReturn_passed_progress
      (pre ++ [false, true]) tail bits
    simpa [List.append_assoc, Nat.add_assoc] using h
  · have h := runtimeProgressExhaust_final pre
      (flattenPairs (passedSourceBlock bits) ++ [false, false] ++ tail)
    simpa [List.append_assoc, Nat.add_assoc] using h

/-! ## Structural iteration over the physical progress record -/

/-- A proof-level certificate for all remaining physical rounds.  In the
successor case, `k + 1` is the number of `10` words still on tape.  A
nonfinal round consumes the rightmost word, moves the passed block left by
one pair, and adds the old hole to `tail`; the recursion therefore follows
the tape itself rather than a controller counter. -/
def RuntimeFixedOuterRoundsCertified
    (pre tail bits : List Bool) : Nat → Prop
  | 0 => True
  | 1 =>
      let block := passedSourceBlock bits
      let T0 := pre ++ [false, true, true, false, false, false] ++
        flattenPairs block ++ tail
      let T1 := pre ++ [false, true, true, false] ++
        flattenPairs block ++ [false, false] ++ tail
      let T2 := pre ++ [false, true, false, false] ++
        flattenPairs block ++ [false, false] ++ tail
      let T3 := pre ++ [false, false, false, false] ++
        flattenPairs block ++ [false, false] ++ tail
      (run runtimeUniversalPassedShiftMachine (8 * block.length)
          ⟨runtimeUniversalPassedShiftMachine.start, pre.length + 4, T0⟩ =
        ⟨RuntimeUniversalPassedShiftState.done,
          pre.length + 4 + 2 * block.length, T1⟩) ∧
      (run runtimeProgressReturnMachine (1 + 2 * block.length + 3)
          ⟨runtimeProgressReturnMachine.start,
            pre.length + 4 + 2 * block.length, T1⟩ =
        ⟨RuntimeProgressReturnState.done, pre.length + 2, T2⟩) ∧
      (run runtimeProgressExhaustMachine 3
          ⟨runtimeProgressExhaustMachine.start, pre.length + 2, T2⟩ =
        ⟨RuntimeProgressExhaustState.final, pre.length + 1, T3⟩)
  | k + 2 =>
      let marks := flattenPairs (List.replicate k (true, false))
      let roundPre := pre ++ [false, true] ++ marks
      let block := passedSourceBlock bits
      let T0 := roundPre ++ [true, false, true, false, false, false] ++
        flattenPairs block ++ tail
      let T1 := roundPre ++ [true, false, true, false] ++
        flattenPairs block ++ [false, false] ++ tail
      let T2 := roundPre ++ [true, false, false, false] ++
        flattenPairs block ++ [false, false] ++ tail
      ((run runtimeUniversalPassedShiftMachine (8 * block.length)
          ⟨runtimeUniversalPassedShiftMachine.start, roundPre.length + 4, T0⟩ =
        ⟨RuntimeUniversalPassedShiftState.done,
          roundPre.length + 4 + 2 * block.length, T1⟩) ∧
      (run runtimeProgressReturnMachine (1 + 2 * block.length + 3)
          ⟨runtimeProgressReturnMachine.start,
            roundPre.length + 4 + 2 * block.length, T1⟩ =
        ⟨RuntimeProgressReturnState.done, roundPre.length + 2, T2⟩) ∧
      (run runtimeProgressExhaustMachine 2
          ⟨runtimeProgressExhaustMachine.start, roundPre.length + 2, T2⟩ =
        ⟨RuntimeProgressExhaustState.more, roundPre.length + 2, T2⟩)) ∧
      RuntimeFixedOuterRoundsCertified pre ([false, false] ++ tail) bits (k + 1)

/-- Every finite nonempty physical progress record has a complete certified
round trace ending in the fixed sentinel-final branch. -/
theorem runtimeFixedOuterRounds_certified
    (pre tail bits : List Bool) (k : Nat) :
    RuntimeFixedOuterRoundsCertified pre tail bits (k + 1) := by
  induction k generalizing tail with
  | zero =>
      simpa [RuntimeFixedOuterRoundsCertified] using
        runtimeFixedOuterRound_final pre tail bits
  | succ k ih =>
      rw [show k + 1 + 1 = k + 2 by omega]
      simp only [RuntimeFixedOuterRoundsCertified]
      constructor
      · simpa only using runtimeFixedOuterRound_more
          (pre ++ [false, true] ++
            flattenPairs (List.replicate k (true, false))) tail bits
      · simpa [Nat.add_assoc] using
          ih (tail := [false, false] ++ tail)
#print axioms runtimeFixedOuterRound_more
#print axioms runtimeFixedOuterRound_final
#print axioms runtimeFixedOuterRounds_certified

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeFixedOuterRound
