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

def preservedSelectedPairs (d : Nat) (done : List (List Bool))
    (bits : List Bool) (suffix : List (Bool × Bool)) : List (Bool × Bool) :=
  List.replicate done.length (true, true) ++
    List.replicate d (true, true) ++ [(false, true)] ++
    done.flatMap passedSourceBlock ++ freshSourceBlock bits ++ suffix

def cycleInputPreservedPairs (k r d : Nat) (done : List (List Bool))
    (bits : List Bool) (rest : List (List Bool))
    (suffix : List (Bool × Bool)) : List (Bool × Bool) :=
  cycleInputPairs k r d done bits rest ++ suffix

def cycleCountPreservedPairs (k r d : Nat) (done : List (List Bool))
    (bits : List Bool) (rest : List (List Bool))
    (suffix : List (Bool × Bool)) : List (Bool × Bool) :=
  cycleCountMarkedPairs k r d done bits rest ++ suffix

def cycleOutputPreservedPairs (k r d : Nat) (done : List (List Bool))
    (bits : List Bool) (rest : List (List Bool))
    (suffix : List (Bool × Bool)) : List (Bool × Bool) :=
  cycleOutputPairs k r d done bits rest ++ suffix

@[simp] theorem cycleInputPreservedPairs_length_pos (k r d : Nat)
    (done : List (List Bool)) (bits : List Bool)
    (rest : List (List Bool)) (suffix : List (Bool × Bool)) :
    k < (cycleInputPreservedPairs k r d done bits rest suffix).length := by
  have h := cycleInputPairs_length_pos k r d done bits rest
  simp only [cycleInputPreservedPairs, List.length_append]
  omega

theorem cycle_preserved_count_write (k r d : Nat)
    (done : List (List Bool)) (bits : List Bool)
    (rest : List (List Bool)) (suffix : List (Bool × Bool)) :
    writeAt (flattenPairs
      (cycleInputPreservedPairs k r d done bits rest suffix))
        (2 * k + 1) true =
      flattenPairs (cycleCountPreservedPairs k r d done bits rest suffix) := by
  rw [writeAt_flattenPairs_hi _ k
    (cycleInputPreservedPairs_length_pos k r d done bits rest suffix) true]
  congr 1
  let A := List.replicate k (true, true)
  let tail := List.replicate r (true, false) ++
    List.replicate d (true, true) ++ [(false, true)] ++
    done.flatMap passedSourceBlock ++ freshSourceBlock bits ++
    rest.flatMap freshSourceBlock ++ suffix
  have hin : cycleInputPreservedPairs k r d done bits rest suffix =
      A ++ (true, false) :: tail := by
    simp [cycleInputPreservedPairs, cycleInputPairs, A, tail,
      List.append_assoc]
  have hout : cycleCountPreservedPairs k r d done bits rest suffix =
      A ++ (true, true) :: tail := by
    rw [cycleCountPreservedPairs, cycleCountMarkedPairs,
      List.replicate_succ']
    simp [A, tail, List.append_assoc]
  have hk : k = A.length := by simp [A]
  rw [hin, hout, hk]
  exact set_fresh_header A tail

theorem cycle_preserved_archive_write (k r d : Nat)
    (done : List (List Bool)) (bits : List Bool)
    (rest : List (List Bool)) (suffix : List (Bool × Bool)) :
    let ps := cycleCountPreservedPairs k r d done bits rest suffix
    let q := k + 1 + r + d + 1 + (done.flatMap passedSourceBlock).length
    writeAt (flattenPairs ps) (2 * q + 1) true =
      flattenPairs (cycleOutputPreservedPairs k r d done bits rest suffix) := by
  dsimp only
  let A := List.replicate (k + 1) (true, true) ++
    List.replicate r (true, false) ++ List.replicate d (true, true) ++
    [(false, true)] ++ done.flatMap passedSourceBlock
  let tail := dataPairs bits ++ [(false, true)] ++
    rest.flatMap freshSourceBlock ++ suffix
  have hq : k + 1 + r + d + 1 + (done.flatMap passedSourceBlock).length =
      A.length := by simp [A]; omega
  have hform : cycleCountPreservedPairs k r d done bits rest suffix =
      A ++ (true, false) :: tail := by
    simp [cycleCountPreservedPairs, cycleCountMarkedPairs, A, tail,
      freshSourceBlock, List.append_assoc]
  have hout : cycleOutputPreservedPairs k r d done bits rest suffix =
      A ++ (true, true) :: tail := by
    simp [cycleOutputPreservedPairs, cycleOutputPairs, A, tail,
      passedSourceBlock, List.append_assoc]
  rw [hq, writeAt_flattenPairs_hi _ A.length (by rw [hform]; simp) true]
  congr 1
  rw [hform, hout]
  exact set_fresh_header A tail

/-- The final selector scan is suffix-parametric: it halts at the current
fresh payload without inspecting or changing the adjacent preserved copy. -/
theorem sourceSelect_final_preserved_suffix (d : Nat)
    (done : List (List Bool)) (bits : List Bool)
    (suffix : List (Bool × Bool)) :
    run sourceSelectMachine (sourceSelectFinalClock d done)
        ⟨SourceSelectState.cntLo, 0,
          flattenPairs (preservedSelectedPairs d done bits suffix)⟩ =
      ⟨SourceSelectState.done, 2 * (done.length + d + 1 +
          (done.flatMap passedSourceBlock).length + 1),
        flattenPairs (preservedSelectedPairs d done bits suffix)⟩ := by
  let T := flattenPairs (preservedSelectedPairs d done bits suffix)
  let cnt := List.replicate done.length (true, true) ++
    List.replicate d (true, true)
  have hcntNo : NoFreshMark cnt := by
    intro p hp
    unfold cnt at hp
    rcases List.mem_append.mp hp with hp | hp
    · rcases List.mem_replicate.mp hp with ⟨_, rfl⟩; simp
    · rcases List.mem_replicate.mp hp with ⟨_, rfl⟩; simp
  have hcntLo : ∀ p ∈ cnt, p.1 = true := by
    intro p hp
    unfold cnt at hp
    rcases List.mem_append.mp hp with hp | hp
    · rcases List.mem_replicate.mp hp with ⟨_, rfl⟩; rfl
    · rcases List.mem_replicate.mp hp with ⟨_, rfl⟩; rfl
  have hscan := cnt_skip_pairStream [] cnt
    ((false, true) :: done.flatMap passedSourceBlock ++
      freshSourceBlock bits ++ suffix) hcntNo hcntLo
  have hloBoundary : T.getD (2 * (done.length + d)) false = false := by
    unfold T preservedSelectedPairs
    simpa [List.append_assoc] using pair_start_lo
      (List.replicate done.length (true, true) ++
        List.replicate d (true, true)) false true
      (done.flatMap passedSourceBlock ++ freshSourceBlock bits ++ suffix)
  have hfinish := cnt_finish T (2 * (done.length + d)) hloBoundary
  have hpassed := select_skip_pairStream
    (List.replicate (done.length + d) (true, true) ++ [(false, true)])
    (done.flatMap passedSourceBlock) (freshSourceBlock bits ++ suffix)
    (passedArchive_noFresh done)
  let q := done.length + d + 1 + (done.flatMap passedSourceBlock).length
  have hloArchive : T.getD (2 * q) false = true := by
    unfold T preservedSelectedPairs q
    have he : done.length + d +
        ((done.flatMap passedSourceBlock).length + 1) = q := by
      unfold q
      omega
    have he2 : done.length + d +
        ((done.map fun a => (passedSourceBlock a).length).sum + 1) =
        done.length + d + 1 +
          (done.map fun a => (passedSourceBlock a).length).sum := by omega
    simpa [List.append_assoc, freshSourceBlock, he, he2] using
      pair_start_lo
        (List.replicate done.length (true, true) ++
          List.replicate d (true, true) ++ [(false, true)] ++
          done.flatMap passedSourceBlock) true false
        (dataPairs bits ++ [(false, true)] ++ suffix)
  have hhiArchive : T.getD (2 * q + 1) false = false := by
    unfold T preservedSelectedPairs q
    have he : done.length + d +
        ((done.flatMap passedSourceBlock).length + 1) = q := by
      unfold q
      omega
    have he2 : done.length + d +
        ((done.map fun a => (passedSourceBlock a).length).sum + 1) =
        done.length + d + 1 +
          (done.map fun a => (passedSourceBlock a).length).sum := by omega
    simpa [List.append_assoc, freshSourceBlock, he, he2] using
      pair_start_hi
        (List.replicate done.length (true, true) ++
          List.replicate d (true, true) ++ [(false, true)] ++
          done.flatMap passedSourceBlock) true false
        (dataPairs bits ++ [(false, true)] ++ suffix)
  have htake := select_take_mark T (2 * q) hloArchive hhiArchive
  have hscan' : run sourceSelectMachine (2 * (done.length + d))
      ⟨SourceSelectState.cntLo, 0, T⟩ =
      ⟨SourceSelectState.cntLo, 2 * (done.length + d), T⟩ := by
    simpa [T, cnt, preservedSelectedPairs, List.append_assoc] using hscan
  have hpassed' :
      run sourceSelectMachine (2 * (done.flatMap passedSourceBlock).length)
        ⟨SourceSelectState.selectLo, 2 * (done.length + d) + 2, T⟩ =
      ⟨SourceSelectState.selectLo, 2 * q, T⟩ := by
    have hs : 2 * (done.length + d + 1) = 2 * (done.length + d) + 2 := by
      omega
    have he : 2 * (done.length + d + 1 +
        (done.flatMap passedSourceBlock).length) = 2 * q := by
      unfold q
      omega
    simpa [T, preservedSelectedPairs, q, List.append_assoc, hs, he] using hpassed
  have hfirst : run sourceSelectMachine (2 * (done.length + d) + 2)
      ⟨SourceSelectState.cntLo, 0, T⟩ =
      ⟨SourceSelectState.selectLo, 2 * (done.length + d) + 2, T⟩ := by
    rw [run_add, hscan', hfinish]
  have hsecond : run sourceSelectMachine
      (2 * (done.flatMap passedSourceBlock).length + 2)
      ⟨SourceSelectState.selectLo, 2 * (done.length + d) + 2, T⟩ =
      ⟨SourceSelectState.done, 2 * q + 2, T⟩ := by
    rw [run_add, hpassed', htake]
  unfold sourceSelectFinalClock
  rw [run_add, hfirst, hsecond]
  unfold q T
  congr 2

/-- Concrete final-scan specialization for the duplicated source archive. -/
theorem sourceSelect_final_duplicated (d : Nat)
    (done : List (List Bool)) (bits : List Bool)
    (rest : List (List Bool)) :
    run sourceSelectMachine (sourceSelectFinalClock d done)
        ⟨SourceSelectState.cntLo, 0,
          flattenPairs (preservedSelectedPairs d done bits
            (passedSourceBlock bits ++ duplicatedSourceArchive rest))⟩ =
      ⟨SourceSelectState.done, 2 * (done.length + d + 1 +
          (done.flatMap passedSourceBlock).length + 1),
        flattenPairs (preservedSelectedPairs d done bits
          (passedSourceBlock bits ++ duplicatedSourceArchive rest))⟩ :=
  sourceSelect_final_preserved_suffix d done bits
    (passedSourceBlock bits ++ duplicatedSourceArchive rest)

theorem flattenPairs_preservedSelected_duplicated (d : Nat)
    (done : List (List Bool)) (bits : List Bool)
    (rest : List (List Bool)) :
    flattenPairs (preservedSelectedPairs d done bits
      (passedSourceBlock bits ++ duplicatedSourceArchive rest)) =
      selectedPrefix d done ++ [true, false] ++ encodeD bits ++
        flattenPairs (passedSourceBlock bits) ++
          flattenPairs (duplicatedSourceArchive rest) := by
  simp [preservedSelectedPairs, selectedPrefix, selectedPrefixPairs,
    freshSourceBlock, flattenPairs_append, flattenPairs, List.append_assoc]
  simpa [List.append_assoc] using congrArg
    (fun z => z ++ flattenPairs (passedSourceBlock bits) ++
      flattenPairs (duplicatedSourceArchive rest))
    (flattenPairs_dataPairs bits)

def sourceSelectCompactFinalClock (d : Nat) (done : List (List Bool))
    (bits : List Bool) : Nat :=
  sourceSelectFinalClock d done + 1 + sourceCompactClock bits

/-- From the already-normalized selected layout, the fixed selector and
decoder expose the raw payload while preserving its adjacent canonical copy. -/
theorem sourceSelectCompact_final_duplicated (d : Nat)
    (done : List (List Bool)) (bits : List Bool)
    (rest : List (List Bool)) :
    run sourceSelectCompactMachine
        (sourceSelectCompactFinalClock d done bits)
        (init sourceSelectCompactMachine
          (flattenPairs (preservedSelectedPairs d done bits
            (passedSourceBlock bits ++ duplicatedSourceArchive rest)))) =
      ⟨Sum.inr SourceCompactState.done,
        (selectedPrefix d done).length + bits.length + 3,
        selectedPrefix d done ++ bits ++ preservedPassedTrailer bits
          (flattenPairs (duplicatedSourceArchive rest))⟩ := by
  rw [flattenPairs_preservedSelected_duplicated]
  have hsel := sourceSelect_final_duplicated d done bits rest
  rw [flattenPairs_preservedSelected_duplicated,
    selected_progress_head] at hsel
  have hcomp0 := sourceCompact_run (selectedPrefix d done) bits
    (flattenPairs (passedSourceBlock bits) ++
      flattenPairs (duplicatedSourceArchive rest))
  have hcomp : run sourceCompactMachine (sourceCompactClock bits)
      ⟨SourceCompactState.backHi, (selectedPrefix d done).length + 2,
        selectedPrefix d done ++ [true, false] ++ encodeD bits ++
          flattenPairs (passedSourceBlock bits) ++
            flattenPairs (duplicatedSourceArchive rest)⟩ =
      ⟨SourceCompactState.done,
        (selectedPrefix d done).length + bits.length + 3,
        selectedPrefix d done ++ bits ++ preservedPassedTrailer bits
          (flattenPairs (duplicatedSourceArchive rest))⟩ := by
    simpa [preservedPassedTrailer,
      PallLean.Paper93.DeepMath.PathB.CookLevinDoubled.encodeD,
      List.append_assoc] using hcomp0
  exact headSeq_run sourceSelectMachine sourceCompactMachine
    (selectedPrefix d done ++ [true, false] ++ encodeD bits ++
      flattenPairs (passedSourceBlock bits) ++
        flattenPairs (duplicatedSourceArchive rest))
    (selectedPrefix d done ++ [true, false] ++ encodeD bits ++
      flattenPairs (passedSourceBlock bits) ++
        flattenPairs (duplicatedSourceArchive rest))
    (selectedPrefix d done ++ bits ++ preservedPassedTrailer bits
      (flattenPairs (duplicatedSourceArchive rest)))
    (sourceSelectFinalClock d done) (sourceCompactClock bits)
    ((selectedPrefix d done).length + 2)
    ((selectedPrefix d done).length + bits.length + 3)
    SourceSelectState.done SourceCompactState.done hsel rfl hcomp rfl

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
#print axioms cycle_preserved_count_write
#print axioms cycle_preserved_archive_write
#print axioms sourceSelect_final_preserved_suffix
#print axioms sourceSelect_final_duplicated
#print axioms sourceSelectCompact_final_duplicated
#print axioms sourceCompact_run_with_preservedPassed
#print axioms masterM_after_preservedPassed_decomposition

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeDuplicatedSourceArchive
