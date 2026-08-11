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

theorem duplicatedSourceArchive_length (schedule : List (List Bool)) :
    (duplicatedSourceArchive schedule).length =
      2 * (schedule.map List.length).sum + 4 * schedule.length := by
  induction schedule with
  | nil => rfl
  | cons bits rest ih =>
      rw [duplicatedSourceArchive_cons]
      simp [duplicatedSourceBlock_length, ih]
      omega

/-- Exact selected-round split: prior canonical blocks, one consumable fresh
block, its preserved canonical copy, and the duplicated later archive. -/
theorem duplicatedSourceArchive_schedule_split
    (schedule : List (List Bool)) {t : Nat} (ht : t < schedule.length) :
    duplicatedSourceArchive schedule =
      (schedule.take t).flatMap duplicatedSourceBlock ++
        freshSourceBlock schedule[t] ++ passedSourceBlock schedule[t] ++
          duplicatedSourceArchive (schedule.drop (t + 1)) := by
  conv_lhs => rw [← List.take_append_drop t schedule]
  rw [List.drop_eq_getElem_cons ht]
  simp [duplicatedSourceArchive, duplicatedSourceBlock, List.append_assoc]

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

#print axioms duplicatedSourceArchive_length
#print axioms duplicatedSourceArchive_schedule_split
#print axioms duplicatedSourceArchive_selected_tail

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeDuplicatedSourceArchive
