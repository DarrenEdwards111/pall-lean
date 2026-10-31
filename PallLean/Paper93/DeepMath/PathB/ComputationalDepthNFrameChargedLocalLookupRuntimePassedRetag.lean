import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeSourceSelect
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimePhysicalLeftSafety

/-! # Universal fresh-to-passed source header retagger -/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePassedRetag

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryTerminal

inductive RuntimePassedRetagState
  | lo | hi | done
  deriving DecidableEq, Fintype

open RuntimePassedRetagState

/-- Fixed finite control: cross the leading `1`, rewrite the fresh tag's
second bit from `0` to `1`, and halt at the payload origin. -/
def runtimePassedRetagMachine : Machine where
  State := RuntimePassedRetagState
  fin := inferInstance
  dec := inferInstance
  start := lo
  halt
    | done => true
    | _ => false
  δ s _ := match s with
    | lo => (hi, none, 1)
    | hi => (done, some true, 1)
    | done => (done, none, 2)
  accept _ := false

theorem writeAt_freshHeader_hi (pre rest : List Bool) :
    writeAt (pre ++ true :: false :: rest) (pre.length + 1) true =
      pre ++ true :: true :: rest := by
  simp [writeAt]

/-- Exact two-transition retag, independent of payload length and contents. -/
theorem runtimePassedRetag_run (pre payload tail : List Bool) :
    run runtimePassedRetagMachine 2
        ⟨runtimePassedRetagMachine.start, pre.length,
          pre ++ [true, false] ++ payload ++ tail⟩ =
      ⟨done, pre.length + 2,
        pre ++ [true, true] ++ payload ++ tail⟩ := by
  rw [show 2 = 1 + 1 by omega, run_add]
  simp [run_succ, step, runtimePassedRetagMachine, moveHead,
    writeAt_freshHeader_hi, List.append_assoc]

theorem runtimePassedRetag_halted (pre payload tail : List Bool) :
    runtimePassedRetagMachine.halt
      (run runtimePassedRetagMachine 2
        ⟨runtimePassedRetagMachine.start, pre.length,
          pre ++ [true, false] ++ payload ++ tail⟩).st = true := by
  rw [runtimePassedRetag_run]
  rfl

theorem runtimePassedRetag_leftSafe (pre payload tail : List Bool) :
    LeftSafeRun runtimePassedRetagMachine
      ⟨runtimePassedRetagMachine.start, pre.length,
        pre ++ [true, false] ++ payload ++ tail⟩ 2 := by
  intro i hi hlive hleft
  interval_cases i <;>
    simp [run_succ, step, runtimePassedRetagMachine, moveHead] at hleft

/-- Canonical block-level specialization. -/
theorem runtimePassedRetag_freshSourceBlock
    (pre bits tail : List Bool) :
    run runtimePassedRetagMachine 2
        ⟨runtimePassedRetagMachine.start, pre.length,
          pre ++ flattenPairs (freshSourceBlock bits) ++ tail⟩ =
      ⟨done, pre.length + 2,
        pre ++ flattenPairs (passedSourceBlock bits) ++ tail⟩ := by
  simpa [freshSourceBlock, passedSourceBlock, flattenPairs,
    flattenPairs_append, List.append_assoc] using
      runtimePassedRetag_run pre (flattenPairs (dataPairs bits) ++ [false, true]) tail

#print axioms runtimePassedRetag_run
#print axioms runtimePassedRetag_leftSafe
#print axioms runtimePassedRetag_freshSourceBlock

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePassedRetag
