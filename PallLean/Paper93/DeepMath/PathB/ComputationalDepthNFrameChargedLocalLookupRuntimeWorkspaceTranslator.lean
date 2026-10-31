import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupNextStage
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeLeftSafety
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeWorkspaceLocator

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

theorem stageMachine_prefixSafe_any (P : Nat) (target tape : List Bool)
    (n : Nat) :
    PrefixSafeRun (stageMachine P target) (init (stageMachine P target) tape) n := by
  intro i hi
  constructor
  · intro _
    simp only [stageMachine]
    split_ifs <;> simp
  · intro _ hleft
    simp only [stageMachine] at hleft
    split_ifs at hleft <;> simp_all

theorem stageMachine_leftSafe_any (P : Nat) (target tape : List Bool)
    (n : Nat) :
    LeftSafeRun (stageMachine P target) (init (stageMachine P target) tape) n := by
  have hs := stageMachine_prefixSafe_any P target tape n
  intro i hi
  exact (hs i hi).leftInside

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

theorem stagedTape_getD_after (P : Nat) (bits : List Bool) (T : List Bool) :
    ∀ {k p : Nat}, P + k ≤ p →
      (stagedTape P bits k T).getD p false = T.getD p false := by
  intro k
  induction k with
  | zero => simp [stagedTape]
  | succ k ih =>
      intro p hp
      simp only [stagedTape]
      rw [PallLean.Paper93.DeepMath.PathB.CookLevinShiftLoop.writeAt_getD_ne
        (by omega)]
      exact ih (by omega)

theorem stagedTape_length_eq (P : Nat) (bits T : List Bool) {k : Nat}
    (hk : k ≤ bits.length) (hfit : P + bits.length ≤ T.length) :
    (stagedTape P bits k T).length = T.length := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [stagedTape, writeAt_length, ih (by omega)]
      rw [max_eq_left]
      omega

/-- When the old and new blocks have equal length, staging is exactly list
replacement: both the protected prefix and the following tail are unchanged. -/
theorem stagedTape_replace_eq (pre old target tail : List Bool)
    (hlen : old.length = target.length) :
    stagedTape pre.length target target.length (pre ++ old ++ tail) =
      pre ++ target ++ tail := by
  let T := pre ++ old ++ tail
  have hfit : pre.length + target.length ≤ T.length := by
    simp [T, hlen]
  have hlength :
      (stagedTape pre.length target target.length T).length =
        (pre ++ target ++ tail).length := by
    rw [stagedTape_length_eq pre.length target T (by omega) hfit]
    simp [T, hlen]
  have hget : ∀ i, i < (pre ++ target ++ tail).length →
      (stagedTape pre.length target target.length T).getD i false =
        (pre ++ target ++ tail).getD i false := by
    intro i hi
    by_cases hpre : i < pre.length
    · rw [stagedTape_getD_before pre.length target target.length T hpre]
      rw [show T = pre ++ (old ++ tail) by simp [T, List.append_assoc],
        show pre ++ target ++ tail = pre ++ (target ++ tail) by
          simp [List.append_assoc],
        List.getD_append (h := hpre), List.getD_append (h := hpre)]
    · by_cases htarget : i < pre.length + target.length
      · let j := i - pre.length
        have hj : j < target.length := by dsimp [j]; omega
        have hw := stagedTape_getD_written pre.length target T
          (i := j) hj (by omega)
        have hij : pre.length + j = i := by dsimp [j]; omega
        rw [hij] at hw
        rw [hw]
        have hr :=
          PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeWorkspaceLocator.getD_append_middle
            pre target tail j hj
        simpa [hij] using hr.symm
      · rw [stagedTape_getD_after pre.length target T
            (k := target.length) (p := i) (by omega)]
        let j := i - (pre.length + target.length)
        have hijTarget : (pre ++ target).length + j = i := by
          simp only [List.length_append]
          dsimp [j]
          omega
        have hijOld : (pre ++ old).length + j = i := by
          simpa only [List.length_append, hlen] using hijTarget
        have hjtail : j < tail.length := by
          simp only [List.length_append] at hi
          dsimp [j]
          omega
        have ho :=
          PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeWorkspaceLocator.getD_append_middle
            (pre ++ old) tail [] j hjtail
        have hn :=
          PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeWorkspaceLocator.getD_append_middle
            (pre ++ target) tail [] j hjtail
        rw [List.append_nil, hijOld] at ho
        rw [List.append_nil, hijTarget] at hn
        simpa [T, List.append_assoc] using ho.trans hn.symm
  apply List.ext_getElem hlength
  intro i hi1 hi2
  have hg := hget i hi2
  rw [List.getD_eq_getElem _ false hi1,
    List.getD_eq_getElem _ false hi2] at hg
  exact hg

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
#print axioms stagedTape_replace_eq

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeWorkspaceTranslator
