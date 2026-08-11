import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimePreservedPassedCopy

/-!
# Duplicated scheduled source archive

Each scheduled source is stored as a consumable fresh block immediately
followed by its canonical passed copy.  The lookup path consumes only the
fresh block; the passed copy lies in the arbitrary tail preserved by
`sourceCompact` and `masterM`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeDuplicatedSourceArchive

open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect
open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinMaster
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLiteralWeld
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceCompact
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePreservedPassedCopy
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundEntryAdapter
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixRun

def duplicatedSourceBlock (bits : List Bool) : List (Bool × Bool) :=
  freshSourceBlock bits ++ passedSourceBlock bits

def duplicatedSourceArchive (schedule : List (List Bool)) :
    List (Bool × Bool) :=
  schedule.flatMap duplicatedSourceBlock

@[simp] theorem duplicatedSourceArchive_nil :
    duplicatedSourceArchive [] = [] := rfl

@[simp] theorem duplicatedSourceArchive_cons
    (bits : List Bool) (rest : List (List Bool)) :
    duplicatedSourceArchive (bits :: rest) =
      freshSourceBlock bits ++ passedSourceBlock bits ++
        duplicatedSourceArchive rest := by
  simp [duplicatedSourceArchive, duplicatedSourceBlock, List.append_assoc]

theorem duplicatedSourceBlock_length (bits : List Bool) :
    (duplicatedSourceBlock bits).length = 2 * bits.length + 4 := by
  simp [duplicatedSourceBlock, freshSourceBlock, passedSourceBlock, dataPairs]
  omega

theorem duplicatedSourceArchive_length (schedule : List (List Bool)) :
    (duplicatedSourceArchive schedule).length =
      2 * (schedule.map List.length).sum + 4 * schedule.length := by
  induction schedule with
  | nil => rfl
  | cons bits rest ih =>
      rw [duplicatedSourceArchive_cons]
      simp [freshSourceBlock, passedSourceBlock, dataPairs, ih]
      omega

/-- Exact selected-round split: prior canonical blocks, one consumable fresh
block, its preserved canonical copy, and the duplicated later archive. -/
theorem duplicatedSourceArchive_schedule_split
    (schedule : List (List Bool)) {t : Nat} (ht : t < schedule.length) :
    duplicatedSourceArchive schedule =
      (schedule.take t).flatMap duplicatedSourceBlock ++
        freshSourceBlock schedule[t] ++ passedSourceBlock schedule[t] ++
          duplicatedSourceArchive (schedule.drop (t + 1)) := by
  unfold duplicatedSourceArchive
  calc
    List.flatMap duplicatedSourceBlock schedule =
        List.flatMap duplicatedSourceBlock (schedule.take t) ++
          List.flatMap duplicatedSourceBlock (schedule.drop t) := by
      rw [← List.flatMap_append, List.take_append_drop]
    _ = _ := by
      rw [List.drop_eq_getElem_cons ht]
      rw [List.flatMap_cons]
      simp [duplicatedSourceBlock, List.append_assoc]

/-- After the fresh working block is consumed, the next physical block is
already exactly the canonical passed block required by successor adjacency. -/
theorem duplicatedSourceArchive_selected_tail
    (bits : List Bool) (rest : List (List Bool)) :
    (freshSourceBlock bits ++ passedSourceBlock bits ++
      duplicatedSourceArchive rest).drop (freshSourceBlock bits).length =
        passedSourceBlock bits ++ duplicatedSourceArchive rest := by
  simp

/-- Flattened form consumed by the one-tape machines. -/
theorem flattenPairs_duplicatedSourceArchive_cons
    (bits : List Bool) (rest : List (List Bool)) :
    flattenPairs (duplicatedSourceArchive (bits :: rest)) =
      flattenPairs (freshSourceBlock bits) ++
        flattenPairs (passedSourceBlock bits) ++
          flattenPairs (duplicatedSourceArchive rest) := by
  simp [duplicatedSourceArchive, duplicatedSourceBlock,
    flattenPairs_append, List.append_assoc]

/-- The existing fixed decoder consumes the fresh working block while the
adjacent canonical copy and duplicated future archive remain untouched. -/
theorem sourceCompact_run_with_preservedPassed
    (pre bits : List Bool) (rest : List (List Bool)) :
    run sourceCompactMachine (sourceCompactClock bits)
        ⟨SourceCompactState.backHi, pre.length + 2,
          pre ++ [true, false] ++ encodeD bits ++
            flattenPairs (passedSourceBlock bits) ++
              flattenPairs (duplicatedSourceArchive rest)⟩ =
      ⟨SourceCompactState.done, pre.length + bits.length + 3,
        pre ++ bits ++ preservedPassedTrailer bits
          (flattenPairs (duplicatedSourceArchive rest))⟩ := by
  have h := sourceCompact_run pre bits
    (flattenPairs (passedSourceBlock bits) ++
      flattenPairs (duplicatedSourceArchive rest))
  simpa [preservedPassedTrailer,
    PallLean.Paper93.DeepMath.PathB.CookLevinDoubled.encodeD,
    List.append_assoc] using h

/-- After resetting onto the raw lookup payload, `masterM` produces the
completed workspace followed by the already canonical current block and the
duplicated future archive. -/
theorem masterM_after_preservedPassed_decomposition
    (w : List Bool) (l : Lit) (rest : List (List Bool)) :
    let bits := literalLookupTape w l
    let tail := flattenPairs (duplicatedSourceArchive rest)
    let trailer := preservedPassedTrailer bits tail
    let cf := run masterM (literalLookupClock w l)
      (init masterM (bits ++ trailer))
    let m := 2 * l.1 + 2
    let n := 2 * l.1 + 4
    ∃ value,
      cf.tp = flattenPairs (runtimeWorkspaceFrontPairs value m n) ++
        flattenPairs (passedSourceBlock bits) ++ tail := by
  simpa using masterM_literal_workspace_preservedPassed_decomposition
    w l (flattenPairs (duplicatedSourceArchive rest))

#print axioms duplicatedSourceArchive_length
#print axioms duplicatedSourceArchive_schedule_split
#print axioms duplicatedSourceArchive_selected_tail
#print axioms sourceCompact_run_with_preservedPassed
#print axioms masterM_after_preservedPassed_decomposition

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeDuplicatedSourceArchive
