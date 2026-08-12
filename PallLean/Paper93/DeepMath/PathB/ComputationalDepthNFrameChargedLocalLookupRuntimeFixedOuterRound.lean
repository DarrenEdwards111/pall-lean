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

#print axioms runtimeFixedOuterRound_more
#print axioms runtimeFixedOuterRound_final

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeFixedOuterRound
