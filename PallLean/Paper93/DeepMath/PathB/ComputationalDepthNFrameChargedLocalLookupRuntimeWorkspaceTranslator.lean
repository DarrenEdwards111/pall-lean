import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupNextStage
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeLeftSafety

/-!
# Completed-workspace to passed-block translator

The completed lookup workspace and the canonical passed-source block have
the same physical span, but different encodings.  This module reuses the
certified finite-control block writer to overwrite that span in place.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeWorkspaceTranslator

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupNextStage
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceLookup
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeLeftSafety
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryTerminal
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixRun

/-- The concrete translator is a finite-control writer for the flattened
canonical passed-source block.  It starts at the first workspace cell. -/
def runtimeWorkspaceTranslatorMachine (bits : List Bool) : Machine :=
  stageMachine 0 (flattenPairs (passedSourceBlock bits))

def runtimeWorkspaceTranslatorClock (bits : List Bool) : Nat :=
  (flattenPairs (passedSourceBlock bits)).length

theorem stageMachine_zero_leftSafe (target tape : List Bool) :
    LeftSafeRun (stageMachine 0 target) (init (stageMachine 0 target) tape)
      target.length := by
  intro i hi hlive hleft
  have hirun := stageMachine_run_write 0 target tape i (by omega)
  have hirun' : run (stageMachine 0 target) i
      (init (stageMachine 0 target) tape) =
      ⟨⟨i, by omega⟩, i, stagedTape 0 target i tape⟩ := by
    simpa [init] using hirun
  rw [hirun'] at hlive hleft ⊢
  exfalso
  simpa [stageMachine, hi] using hleft

theorem stageMachine_zero_prefixSafe (target tape : List Bool) :
    PrefixSafeRun (stageMachine 0 target) (init (stageMachine 0 target) tape)
      target.length := by
  intro i hi
  have hirun := stageMachine_run_write 0 target tape i (by omega)
  have hirun' : run (stageMachine 0 target) i
      (init (stageMachine 0 target) tape) =
      ⟨⟨i, by omega⟩, i, stagedTape 0 target i tape⟩ := by
    simpa [init] using hirun
  rw [hirun']
  constructor
  · intro _
    simp [stageMachine, hi]
  · intro _ hleft
    exfalso
    simpa [stageMachine, hi] using hleft

/-- Exact physical run at an arbitrary protected prefix.  The head begins at
the first workspace cell and ends immediately after the rewritten block. -/
theorem runtimeWorkspaceTranslator_run (pre old tail bits : List Bool)
    (_hlen : old.length = (flattenPairs (passedSourceBlock bits)).length) :
    run (runtimeWorkspaceTranslatorMachine bits)
        (runtimeWorkspaceTranslatorClock bits)
        ⟨(runtimeWorkspaceTranslatorMachine bits).start, pre.length,
          pre ++ old ++ tail⟩ =
      ⟨stageFinalState 0 (flattenPairs (passedSourceBlock bits)),
        pre.length + (flattenPairs (passedSourceBlock bits)).length,
        pre ++ stagedTape 0 (flattenPairs (passedSourceBlock bits))
          (flattenPairs (passedSourceBlock bits)).length (old ++ tail)⟩ := by
  let target := flattenPairs (passedSourceBlock bits)
  have hbase := stageMachine_run 0 target (old ++ tail)
  have hsafe := stageMachine_zero_prefixSafe target (old ++ tail)
  have hshift := run_shiftCfg (stageMachine 0 target) pre
    (init (stageMachine 0 target) (old ++ tail)) target.length hsafe
  have hbase' : run (stageMachine 0 target) target.length
      (init (stageMachine 0 target) (old ++ tail)) =
      ⟨stageFinalState 0 target, target.length,
        stagedTape 0 target target.length (old ++ tail)⟩ := by
    simpa using hbase
  rw [hbase'] at hshift
  simpa [runtimeWorkspaceTranslatorMachine, runtimeWorkspaceTranslatorClock,
    target, shiftCfg, Nat.zero_add, List.append_assoc] using hshift

/-- Every cell of the rewritten span is the corresponding canonical passed
block cell. -/
theorem runtimeWorkspaceTranslator_written (pre old tail bits : List Bool)
    {i : Nat} (hi : i < (flattenPairs (passedSourceBlock bits)).length) :
    (pre ++ stagedTape 0 (flattenPairs (passedSourceBlock bits))
        (flattenPairs (passedSourceBlock bits)).length (old ++ tail)).getD
        (pre.length + i) false =
      (flattenPairs (passedSourceBlock bits)).getD i false := by
  rw [PallLean.Paper93.DeepMath.PathB.CookLevinInP.getD_append_ge (by omega)]
  simpa using stagedTape_getD_written 0
    (flattenPairs (passedSourceBlock bits)) (old ++ tail) hi (by omega)

/-- The complete translator run is physically left-safe, including when the
workspace begins at tape origin. -/
theorem runtimeWorkspaceTranslator_leftSafe (pre old tail bits : List Bool) :
    LeftSafeRun (runtimeWorkspaceTranslatorMachine bits)
      ⟨(runtimeWorkspaceTranslatorMachine bits).start, pre.length,
        pre ++ old ++ tail⟩
      (runtimeWorkspaceTranslatorClock bits) := by
  let target := flattenPairs (passedSourceBlock bits)
  have hp := stageMachine_zero_prefixSafe target (old ++ tail)
  have hl := stageMachine_zero_leftSafe target (old ++ tail)
  simpa [runtimeWorkspaceTranslatorMachine, runtimeWorkspaceTranslatorClock,
    target, shiftCfg, List.append_assoc] using
      leftSafeRun_shiftCfg (stageMachine 0 target) pre
        (init (stageMachine 0 target) (old ++ tail)) target.length hp hl

#print axioms runtimeWorkspaceTranslator_run
#print axioms runtimeWorkspaceTranslator_written
#print axioms runtimeWorkspaceTranslator_leftSafe

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeWorkspaceTranslator
