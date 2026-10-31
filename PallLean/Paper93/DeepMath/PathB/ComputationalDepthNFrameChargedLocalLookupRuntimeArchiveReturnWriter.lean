import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimePhysicalArchive

/-!
# Reverse archive return and rebase-boundary seed

The forward archive locator halts just after the blank `00` pair following the
untouched future archive.  The same grammar is reversible.  Scanning left,
each block has a terminal `01`, equal data pairs, and a `10` header.  A header
belongs to the first block exactly when its predecessor is the proved `11`
padding pair rather than the previous block's `01` terminator.

This file defines one fixed reverse parser, proves that it returns from the
terminal blank to the runtime-discovered future-archive origin without writes,
and composes a fixed two-cell writer that seeds the final `01` boundary of the
next round's countdown immediately to the left of that origin.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeArchiveReturnWriter

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSeq
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinMaster
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLiteralWeld
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupDynamicRoute
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupOutputCapacity
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRepeatController
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupScheduleBound
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeStage
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceCompact
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceLookup
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRelativeOutput
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeTailPreservation
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeOutputSourceLocator
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeWorkspaceLocator
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeWorkspaceTailLocator
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeArchiveLocator
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalArchive

inductive RuntimeArchiveReverseState
  | boot0 | boot1 | boot2
  | termHi | termLo
  | dataHi | dataLo (hi : Bool)
  | predHi | predLo (hi : Bool)
  | return1 | done
  deriving DecidableEq, Fintype

open RuntimeArchiveReverseState

/-- Fixed reverse parser for `10 (00|11)* 01` archive blocks. -/
def runtimeArchiveReverseMachine : Machine where
  State := RuntimeArchiveReverseState
  fin := inferInstance
  dec := inferInstance
  start := .boot0
  halt := fun s => decide (s = .done)
  δ := fun s b =>
    match s with
    | .boot0 => (.boot1, none, 0)
    | .boot1 => (.boot2, none, 0)
    | .boot2 => (.termHi, none, 0)
    | .termHi => if b then (.termLo, none, 0) else (.done, none, 2)
    | .termLo => if !b then (.dataHi, none, 0) else (.done, none, 2)
    | .dataHi => (.dataLo b, none, 0)
    | .dataLo hi =>
        if b = hi then (.dataHi, none, 0)
        else if b && !hi then (.predHi, none, 0)
        else (.done, none, 2)
    | .predHi => (.predLo b, none, 0)
    | .predLo hi =>
        if hi && !b then (.dataHi, none, 0)
        else if hi && b then (.return1, none, 1)
        else (.done, none, 2)
    | .return1 => (.done, none, 1)
    | .done => (.done, none, 2)
  accept := fun _ => false

theorem archiveReverse_run_boot (T : List Bool) (E : Nat) (hE : 3 ≤ E) :
    run runtimeArchiveReverseMachine 3 ⟨boot0, E, T⟩ =
      ⟨termHi, E - 3, T⟩ := by
  simp [run_succ, step, runtimeArchiveReverseMachine, moveHead]
  omega

theorem archiveReverse_run_terminator (T : List Bool) (p : Nat)
    (hp : 1 ≤ p)
    (hhi : T.getD p false = true)
    (hlo : T.getD (p - 1) false = false) :
    run runtimeArchiveReverseMachine 2 ⟨termHi, p, T⟩ =
      ⟨dataHi, p - 2, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at hhi hlo
  simp [run_succ, step, runtimeArchiveReverseMachine, moveHead, hhi, hlo]
  omega

theorem archiveReverse_run_equalPair (T : List Bool) (p : Nat)
    (hp : 1 ≤ p)
    (heq : T.getD p false = T.getD (p - 1) false) :
    run runtimeArchiveReverseMachine 2 ⟨dataHi, p, T⟩ =
      ⟨dataHi, p - 2, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at heq
  simp [run_succ, step, runtimeArchiveReverseMachine, moveHead, heq]
  omega

/-- Reverse scan of `m` equal data pairs immediately after a header at `H`. -/
theorem archiveReverse_run_dataPairs (T : List Bool) (H m : Nat)
    (hH : 1 ≤ H)
    (heq : ∀ i, i < m →
      T.getD (H + 2 + 2 * i) false =
        T.getD (H + 2 + 2 * i + 1) false) :
    run runtimeArchiveReverseMachine (2 * m)
        ⟨dataHi, H + 1 + 2 * m, T⟩ =
      ⟨dataHi, H + 1, T⟩ := by
  induction m with
  | zero => rfl
  | succ m ih =>
      have hm := heq m (by omega)
      have hp : 1 ≤ H + 1 + 2 * (m + 1) := by omega
      have hm' : T.getD (H + 1 + 2 * (m + 1)) false =
          T.getD (H + 1 + 2 * (m + 1) - 1) false := by
        rw [show H + 1 + 2 * (m + 1) = H + 2 + 2 * m + 1 by omega,
          show H + 2 + 2 * m + 1 - 1 = H + 2 + 2 * m by omega]
        exact hm.symm
      have hs := archiveReverse_run_equalPair T
        (H + 1 + 2 * (m + 1)) hp hm'
      rw [show H + 1 + 2 * (m + 1) = H + 1 + (2 + 2 * m) by omega] at hs
      have hs' : run runtimeArchiveReverseMachine 2
          ⟨dataHi, H + 1 + (2 + 2 * m), T⟩ =
          ⟨dataHi, H + 1 + 2 * m, T⟩ := by
        simpa only [show H + 1 + (2 + 2 * m) - 2 = H + 1 + 2 * m by omega]
          using hs
      rw [show 2 * (m + 1) = 2 + 2 * m by omega, run_add, hs',
        ih (fun i hi => heq i (by omega))]

theorem archiveReverse_run_previousHeader (T : List Bool) (H : Nat)
    (hH : 3 ≤ H)
    (hh : T.getD (H + 1) false = false)
    (hl : T.getD H false = true)
    (hph : T.getD (H - 1) false = true)
    (hpl : T.getD (H - 2) false = false) :
    run runtimeArchiveReverseMachine 4 ⟨dataHi, H + 1, T⟩ =
      ⟨dataHi, H - 3, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at hh hl hph hpl
  simp [run_succ, step, runtimeArchiveReverseMachine, moveHead,
    hh, hl, hph, show H - 1 - 1 = H - 2 by omega, hpl]
  omega

theorem archiveReverse_run_firstHeader (T : List Bool) (H : Nat)
    (hH : 2 ≤ H)
    (hh : T.getD (H + 1) false = false)
    (hl : T.getD H false = true)
    (hph : T.getD (H - 1) false = true)
    (hpl : T.getD (H - 2) false = true) :
    run runtimeArchiveReverseMachine 5 ⟨dataHi, H + 1, T⟩ =
      ⟨done, H, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at hh hl hph hpl
  simp [run_succ, step, runtimeArchiveReverseMachine, moveHead,
    hh, hl, hph, show H - 1 - 1 = H - 2 by omega, hpl]
  omega

theorem archiveReverse_block_data (pre bits tail : List Bool) (i : Nat)
    (hi : i < bits.length) :
    let T := pre ++ [true, false] ++ encodeD bits ++ tail
    T.getD (pre.length + 2 + 2 * i) false =
      T.getD (pre.length + 2 + 2 * i + 1) false := by
  simpa using prefixed_block_data_eq pre bits tail i hi

theorem archiveReverse_block_header_lo (pre bits tail : List Bool) :
    let T := pre ++ [true, false] ++ encodeD bits ++ tail
    T.getD pre.length false = true := by
  simpa using prefixed_block_header_lo pre bits tail

theorem archiveReverse_block_header_hi (pre bits tail : List Bool) :
    let T := pre ++ [true, false] ++ encodeD bits ++ tail
    T.getD (pre.length + 1) false = false := by
  simpa using prefixed_block_header_hi pre bits tail

/-- Reverse one nonfirst block, consuming its predecessor's `01` terminator. -/
theorem archiveReverse_run_nonfirstBlock
    (pre bits tail : List Bool) (hpre : 1 ≤ pre.length) :
    let T := pre ++ [false, true] ++ [true, false] ++ encodeD bits ++ tail
    let H := pre.length + 2
    run runtimeArchiveReverseMachine (2 * bits.length + 4)
        ⟨dataHi, H + 1 + 2 * bits.length, T⟩ =
      ⟨dataHi, pre.length - 1, T⟩ := by
  dsimp only
  let T := pre ++ [false, true] ++ [true, false] ++ encodeD bits ++ tail
  let blockPre := pre ++ [false, true]
  let H := blockPre.length
  have hd := archiveReverse_run_dataPairs T H bits.length (by simp [H, blockPre])
    (fun i hi => by
      simpa [T, H, blockPre, List.append_assoc] using
        archiveReverse_block_data blockPre bits tail i hi)
  have hh := archiveReverse_block_header_hi blockPre bits tail
  have hl := archiveReverse_block_header_lo blockPre bits tail
  have hph : T.getD (H - 1) false = true := by
    subst T
    rw [show H - 1 = pre.length + 1 by simp [H, blockPre]]
    rw [List.getD_append (h := by simp)]
    simp
  have hpl : T.getD (H - 2) false = false := by
    subst T
    rw [show H - 2 = pre.length by simp [H, blockPre]]
    rw [List.getD_append (h := by simp)]
    simp
  have hd' : run runtimeArchiveReverseMachine (2 * bits.length)
      ⟨dataHi, pre.length + 2 + 1 + 2 * bits.length,
        pre ++ [false, true] ++ [true, false] ++ encodeD bits ++ tail⟩ =
      ⟨dataHi, H + 1, T⟩ := by
    simpa [H, blockPre, T] using hd
  rw [show 2 * bits.length + 4 = 2 * bits.length + 4 by rfl,
    run_add, hd']
  have hp := archiveReverse_run_previousHeader T H (by simp [H, blockPre]; omega)
    (by simpa [T, H, blockPre, List.append_assoc] using hh)
    (by simpa [T, H, blockPre, List.append_assoc] using hl) hph hpl
  have hhead : H - 3 = pre.length - 1 := by
    simp [H, blockPre]
  simpa [H, blockPre, T, hhead] using hp

/-- Reverse the first block and recognize the `11` padding predecessor. -/
theorem archiveReverse_run_firstBlock
    (pre bits tail : List Bool) :
    let T := pre ++ [true, true] ++ [true, false] ++ encodeD bits ++ tail
    let H := pre.length + 2
    run runtimeArchiveReverseMachine (2 * bits.length + 5)
        ⟨dataHi, H + 1 + 2 * bits.length, T⟩ =
      ⟨done, H, T⟩ := by
  dsimp only
  let T := pre ++ [true, true] ++ [true, false] ++ encodeD bits ++ tail
  let blockPre := pre ++ [true, true]
  let H := blockPre.length
  have hd := archiveReverse_run_dataPairs T H bits.length (by simp [H, blockPre])
    (fun i hi => by
      simpa [T, H, blockPre, List.append_assoc] using
        archiveReverse_block_data blockPre bits tail i hi)
  have hh := archiveReverse_block_header_hi blockPre bits tail
  have hl := archiveReverse_block_header_lo blockPre bits tail
  have hph : T.getD (H - 1) false = true := by
    subst T
    rw [show H - 1 = pre.length + 1 by simp [H, blockPre]]
    rw [List.getD_append (h := by simp)]
    simp
  have hpl : T.getD (H - 2) false = true := by
    subst T
    rw [show H - 2 = pre.length by simp [H, blockPre]]
    rw [List.getD_append (h := by simp)]
    simp
  have hd' : run runtimeArchiveReverseMachine (2 * bits.length)
      ⟨dataHi, pre.length + 2 + 1 + 2 * bits.length,
        pre ++ [true, true] ++ [true, false] ++ encodeD bits ++ tail⟩ =
      ⟨dataHi, H + 1, T⟩ := by
    simpa [H, blockPre, T] using hd
  rw [show 2 * bits.length + 5 = 2 * bits.length + 5 by rfl,
    run_add, hd']
  have hp := archiveReverse_run_firstHeader T H (by simp [H, blockPre])
    (by simpa [T, H, blockPre, List.append_assoc] using hh)
    (by simpa [T, H, blockPre, List.append_assoc] using hl) hph hpl
  simpa [H, blockPre, T] using hp

/-- Every nonempty archive ends in its final `01` terminator. -/
theorem selectedTail_eq_core_term (rest : List (List Bool)) (hne : rest ≠ []) :
    ∃ core, selectedTail rest = core ++ [false, true] := by
  induction rest with
  | nil => exact False.elim (hne rfl)
  | cons bits rest ih =>
      by_cases hr : rest = []
      · subst rest
        refine ⟨[true, false] ++ flattenPairs (dataPairs bits), ?_⟩
        have h := flattenPairs_dataPairs bits
        rw [flattenPairs_append] at h
        rw [selectedTail_cons]
        simp only [selectedTail, List.flatMap_nil, flattenPairs]
        simpa [List.append_assoc] using congrArg ([true, false] ++ ·) h.symm
      · obtain ⟨core, hcore⟩ := ih hr
        refine ⟨[true, false] ++ encodeD bits ++ core, ?_⟩
        rw [selectedTail_cons, hcore]
        simp [List.append_assoc]

/-- Once the terminal pair of the rightmost block has been crossed, the
reverse parser consumes every nonempty archive and returns to its origin.
The arbitrary suffix is never inspected or modified. -/
theorem archiveReverse_run_blocks_prefixed (pre tail : List Bool) :
    ∀ (rest : List (List Bool)), rest ≠ [] →
      let T := pre ++ [true, true] ++ selectedTail rest ++ tail
      let R := pre.length + 2
      run runtimeArchiveReverseMachine ((selectedTail rest).length + 1)
          ⟨dataHi, R + (selectedTail rest).length - 3, T⟩ =
        ⟨done, R, T⟩ := by
  intro rest hne
  induction rest using List.reverseRecOn generalizing tail with
  | nil => exact False.elim (hne rfl)
  | append_singleton init bits ih =>
      by_cases hinit : init = []
      · subst init
        dsimp only
        have hrun := archiveReverse_run_firstBlock pre bits tail
        have htail : selectedTail [bits] =
            [true, false] ++ encodeD bits := by
          simpa [selectedTail, flattenPairs] using selectedTail_cons bits []
        simp only [List.nil_append]
        rw [htail]
        have hlen : ([true, false] ++ encodeD bits).length =
            2 * bits.length + 4 := by simp [encodeD_length]
        rw [hlen]
        have hhead : pre.length + 2 + (2 * bits.length + 4) - 3 =
            pre.length + 2 + 1 + 2 * bits.length := by omega
        rw [hhead]
        simpa only [List.append_assoc] using hrun
      · obtain ⟨core, hcore⟩ := selectedTail_eq_core_term init hinit
        let block := [true, false] ++ encodeD bits
        let tail' := block ++ tail
        let pre' := pre ++ [true, true] ++ core
        let T := pre ++ [true, true] ++ selectedTail (init ++ [bits]) ++ tail
        have hsel : selectedTail (init ++ [bits]) =
            selectedTail init ++ block := by
          simp [selectedTail, List.flatMap_append, flattenPairs_append,
            flattenPairs_freshSourceBlock, block, List.append_assoc]
        have hT : T = pre' ++ [false, true] ++
            [true, false] ++ encodeD bits ++ tail := by
          simp [T, pre', hsel, hcore, block, List.append_assoc]
        have hpre' : 1 ≤ pre'.length := by
          have hpLen : pre'.length = pre.length + 2 + core.length := by
            simp [pre']
            omega
          rw [hpLen]
          omega
        have hlast := archiveReverse_run_nonfirstBlock pre' bits tail hpre'
        have hlast' : run runtimeArchiveReverseMachine
            (2 * bits.length + 4)
            ⟨dataHi,
              (pre.length + 2) + (selectedTail (init ++ [bits])).length - 3,
              T⟩ =
            ⟨dataHi,
              (pre.length + 2) + (selectedTail init).length - 3, T⟩ := by
          rw [hT]
          have hstart : (pre.length + 2) +
              (selectedTail (init ++ [bits])).length - 3 =
              pre'.length + 2 + 1 + 2 * bits.length := by
            rw [hsel, hcore]
            simp [pre', block, encodeD_length]
            omega
          have hend : (pre.length + 2) +
              (selectedTail init).length - 3 = pre'.length - 1 := by
            rw [hcore]
            simp [pre']
            omega
          rw [hstart, hend]
          simpa only using hlast
        have hih := ih tail' hinit
        have hih' : run runtimeArchiveReverseMachine
            ((selectedTail init).length + 1)
            ⟨dataHi,
              (pre.length + 2) + (selectedTail init).length - 3, T⟩ =
            ⟨done, pre.length + 2, T⟩ := by
          simpa [T, tail', block, hsel, List.append_assoc] using
            hih
        dsimp only
        rw [show (selectedTail (init ++ [bits])).length + 1 =
            (2 * bits.length + 4) + ((selectedTail init).length + 1) by
              rw [hsel]
              simp [block, encodeD_length]
              omega,
          run_add, hlast', hih']

def runtimeArchiveReverseClock (rest : List (List Bool)) : Nat :=
  (selectedTail rest).length + 6

/-- Complete reverse traversal from the forward locator's endpoint: cross
the terminal blank, validate the last `01`, reverse every block, and halt at
the first archive header. -/
theorem runtimeArchiveReverse_run_prefixed
    (pre tail : List Bool) (first : List Bool) (more : List (List Bool)) :
    let rest := first :: more
    let T := pre ++ [true, true] ++ selectedTail rest ++ tail
    let R := pre.length + 2
    run runtimeArchiveReverseMachine (runtimeArchiveReverseClock rest)
        ⟨boot0, R + (selectedTail rest).length + 2, T⟩ =
      ⟨done, R, T⟩ := by
  dsimp only
  let rest := first :: more
  let T := pre ++ [true, true] ++ selectedTail rest ++ tail
  let R := pre.length + 2
  have hb := archiveReverse_run_boot T
    (R + (selectedTail rest).length + 2) (by omega)
  have hlen : 2 ≤ (selectedTail rest).length := by
    simp [rest, selectedTail_cons]
  obtain ⟨core, hcore⟩ := selectedTail_eq_core_term rest (by simp [rest])
  have hcorelen : core.length = (selectedTail rest).length - 2 := by
    rw [hcore]
    simp
  let P := pre ++ [true, true] ++ core
  have hshape : T = P ++ ([false, true] ++ tail) := by
    dsimp [T]
    rw [hcore]
    simp [P, List.append_assoc]
  have htermHi : T.getD (R + (selectedTail rest).length - 1) false = true := by
    rw [hshape]
    rw [show R + (selectedTail rest).length - 1 =
      P.length + 1 by
        simp [P, R, hcorelen]
        omega]
    rw [List.getD_append_right (h := by omega)]
    simp
  have htermLo : T.getD (R + (selectedTail rest).length - 2) false = false := by
    rw [hshape]
    rw [show R + (selectedTail rest).length - 2 =
      P.length by
        simp [P, R, hcorelen]
        omega]
    rw [List.getD_append_right (h := le_rfl)]
    simp
  have ht := archiveReverse_run_terminator T
    (R + (selectedTail rest).length - 1) (by
      omega) htermHi (by
        convert htermLo using 1 <;> omega)
  have hblocks := archiveReverse_run_blocks_prefixed pre tail rest (by simp [rest])
  have hb' : run runtimeArchiveReverseMachine 3
      ⟨boot0, R + (selectedTail rest).length + 2, T⟩ =
      ⟨termHi, R + (selectedTail rest).length - 1, T⟩ := by
    convert hb using 1 <;> omega
  have ht' : run runtimeArchiveReverseMachine 2
      ⟨termHi, R + (selectedTail rest).length - 1, T⟩ =
      ⟨dataHi, R + (selectedTail rest).length - 3, T⟩ := by
    convert ht using 1 <;> omega
  rw [show runtimeArchiveReverseClock rest =
      3 + (2 + ((selectedTail rest).length + 1)) by
        unfold runtimeArchiveReverseClock
        omega,
    run_add, hb', run_add, ht', hblocks]

/-- Complete reverse traversal with the temporary canonical `11` marker. -/
theorem runtimeArchiveReverse_run_markedPrefixed
    (pre tail : List Bool) (first : List Bool) (more : List (List Bool)) :
    let rest := first :: more
    let T := pre ++ [true, true] ++ selectedTail rest ++ tail
    let R := pre.length + 2
    run runtimeArchiveReverseMachine (runtimeArchiveReverseClock rest)
        ⟨boot0, R + (selectedTail rest).length + 2, T⟩ =
      ⟨done, R, T⟩ := by
  exact runtimeArchiveReverse_run_prefixed pre tail first more

/-! ## Fixed marker and rebase-boundary writers -/

/-- Four-state left-write-return walk used for both temporary and final pairs. -/
inductive RuntimeRebaseSeedState
  | back1 | writeHi | writeLo | return1 | done
  deriving DecidableEq, Fintype

open RuntimeRebaseSeedState

/-- The marker writer and final seed writer share the same four-state walk. -/
def runtimeRebaseMarkMachine : Machine where
  State := RuntimeRebaseSeedState
  fin := inferInstance
  dec := inferInstance
  start := .back1
  halt := fun s => decide (s = .done)
  δ := fun s _ =>
    match s with
    | .back1 => (.writeHi, none, 0)
    | .writeHi => (.writeLo, some true, 0)
    | .writeLo => (.return1, some true, 1)
    | .return1 => (.done, none, 1)
    | .done => (.done, none, 2)
  accept := fun _ => false

def markArchiveBoundary (T : List Bool) (R : Nat) : List Bool :=
  writeAt (writeAt T (R - 1) true) (R - 2) true

theorem runtimeRebaseMark_run (T : List Bool) (R : Nat) (hR : 2 ≤ R) :
    run runtimeRebaseMarkMachine 4 ⟨back1, R, T⟩ =
      ⟨RuntimeRebaseSeedState.done, R, markArchiveBoundary T R⟩ := by
  simp [run_succ, step, runtimeRebaseMarkMachine, markArchiveBoundary,
    moveHead, show R - 1 - 1 = R - 2 by omega]
  omega

theorem markArchiveBoundary_prefixed (pre suffix : List Bool) (a b : Bool) :
    markArchiveBoundary (pre ++ [a, b] ++ suffix) (pre.length + 2) =
      pre ++ [true, true] ++ suffix := by
  simp [markArchiveBoundary, writeAt, List.set_append]

/-- Starting at a discovered archive origin `R`, write the final countdown
boundary `01` at `R-2,R-1` and return to `R`. -/
def runtimeRebaseSeedMachine : Machine where
  State := RuntimeRebaseSeedState
  fin := inferInstance
  dec := inferInstance
  start := .back1
  halt := fun s => decide (s = .done)
  δ := fun s _ =>
    match s with
    | .back1 => (.writeHi, none, 0)
    | .writeHi => (.writeLo, some true, 0)
    | .writeLo => (.return1, some false, 1)
    | .return1 => (.done, none, 1)
    | .done => (.done, none, 2)
  accept := fun _ => false

def seedRebaseBoundary (T : List Bool) (R : Nat) : List Bool :=
  writeAt (writeAt T (R - 1) true) (R - 2) false

theorem runtimeRebaseSeed_run (T : List Bool) (R : Nat) (hR : 2 ≤ R) :
    run runtimeRebaseSeedMachine 4 ⟨back1, R, T⟩ =
      ⟨RuntimeRebaseSeedState.done, R, seedRebaseBoundary T R⟩ := by
  simp [run_succ, step, runtimeRebaseSeedMachine, seedRebaseBoundary,
    moveHead, show R - 1 - 1 = R - 2 by omega]
  omega

theorem runtimeRebaseSeed_halted (T : List Bool) (R : Nat) (hR : 2 ≤ R) :
    runtimeRebaseSeedMachine.halt
      (run runtimeRebaseSeedMachine 4 ⟨back1, R, T⟩).st = true := by
  rw [runtimeRebaseSeed_run T R hR]
  rfl

theorem seedRebaseBoundary_prefixed (pre suffix : List Bool) (a b : Bool) :
    seedRebaseBoundary (pre ++ [a, b] ++ suffix) (pre.length + 2) =
      pre ++ [false, true] ++ suffix := by
  simp [seedRebaseBoundary, writeAt, List.set_append]

/-! ## Marker-driven operational composition -/

theorem run_stable_cfg (M : Machine) (c : Cfg M) {t T : Nat}
    (hle : t ≤ T) (hh : M.halt (run M t c).st = true) :
    run M T c = run M t c := by
  rw [show T = t + (T - t) by omega, run_add]
  exact run_of_halted M hh _

/-- Head-preserving composition from an already discovered physical head. -/
theorem headSeq_run_at (M1 M2 : Machine) (T0 T1 T2 : List Bool)
    (p0 t1 t2 p1 p2 : Nat) (s1 : M1.State) (s2 : M2.State)
    (h1 : run M1 t1 ⟨M1.start, p0, T0⟩ = ⟨s1, p1, T1⟩)
    (hh1 : M1.halt s1 = true)
    (h2 : run M2 t2 ⟨M2.start, p1, T1⟩ = ⟨s2, p2, T2⟩)
    (hh2 : M2.halt s2 = true) :
    run (headSeqMachine M1 M2) (t1 + 1 + t2)
        ⟨(headSeqMachine M1 M2).start, p0, T0⟩ =
      ⟨Sum.inr s2, p2, T2⟩ := by
  let c0 : Cfg M1 := ⟨M1.start, p0, T0⟩
  have hex : ∃ t, M1.halt (run M1 t c0).st = true :=
    ⟨t1, by rw [h1]; exact hh1⟩
  let tm := Nat.find hex
  have htm : M1.halt (run M1 tm c0).st = true := Nat.find_spec hex
  have htmle : tm ≤ t1 := Nat.find_le (by rw [h1]; exact hh1)
  have hfrozen : run M1 tm c0 = ⟨s1, p1, T1⟩ := by
    rw [← run_stable_cfg M1 c0 htmle htm, h1]
  have hno : ∀ s < tm, M1.halt (run M1 s c0).st = false := by
    intro s hs
    simpa using Nat.find_min hex hs
  have hleft := headSeq_run_inl M1 M2 c0 tm hno
  rw [hfrozen] at hleft
  have hright := headSeq_run_inr M1 M2
    (⟨M2.start, p1, T1⟩ : Cfg M2) t2
  rw [h2] at hright
  have hhalt : (headSeqMachine M1 M2).halt (Sum.inr s2) = true := by
    simpa [headSeqMachine] using hh2
  rw [show t1 + 1 + t2 = tm + (1 + (t2 + (t1 - tm))) by omega,
    run_add]
  rw [show (⟨(headSeqMachine M1 M2).start, p0, T0⟩ :
      Cfg (headSeqMachine M1 M2)) = headInlCfg M1 M2 c0 from rfl]
  rw [hleft, run_add]
  have hswitch := headSeq_step_handoff M1 M2
    (⟨s1, p1, T1⟩ : Cfg M1) hh1
  rw [show run (headSeqMachine M1 M2) 1
      (headInlCfg M1 M2 (⟨s1, p1, T1⟩ : Cfg M1)) =
      headInrCfg M1 M2 ⟨M2.start, p1, T1⟩ by
        rw [run_succ, run_zero]
        exact hswitch,
    run_add, hright]
  exact run_of_halted (headSeqMachine M1 M2) hhalt _

def runtimeArchiveMarkLocateMachine : Machine :=
  headSeqMachine runtimeRebaseMarkMachine runtimeArchiveLocatorMachine

def runtimeArchiveMarkLocateReturnMachine : Machine :=
  headSeqMachine runtimeArchiveMarkLocateMachine runtimeArchiveReverseMachine

/-- Fixed controller from a runtime-discovered archive origin: install a
temporary marker, traverse the archive, return to that marker, and replace it
with the canonical final `01` selector boundary. -/
def runtimeArchiveReturnSeedMachine : Machine :=
  headSeqMachine runtimeArchiveMarkLocateReturnMachine runtimeRebaseSeedMachine

def runtimeArchiveReturnSeedClock (rest : List (List Bool)) : Nat :=
  4 + 1 + runtimeArchiveLocatorClock rest + 1 +
    runtimeArchiveReverseClock rest + 1 + 4

set_option maxHeartbeats 4000000 in
theorem runtimeArchiveReturnSeed_run_prefixed
    (pre : List Bool) (a b : Bool) (first : List Bool)
    (more : List (List Bool)) :
    let rest := first :: more
    let T0 := pre ++ [a, b] ++ selectedTail rest
    let Tm := pre ++ [true, true] ++ selectedTail rest
    let T1 := pre ++ [false, true] ++ selectedTail rest
    let R := pre.length + 2
    run runtimeArchiveReturnSeedMachine (runtimeArchiveReturnSeedClock rest)
        ⟨runtimeArchiveReturnSeedMachine.start, R, T0⟩ =
      ⟨Sum.inr RuntimeRebaseSeedState.done, R, T1⟩ := by
  dsimp only
  let rest := first :: more
  let T0 := pre ++ [a, b] ++ selectedTail rest
  let Tm := pre ++ [true, true] ++ selectedTail rest
  let T1 := pre ++ [false, true] ++ selectedTail rest
  let R := pre.length + 2
  have hm0 := runtimeRebaseMark_run T0 R (by simp [R])
  have hm : run runtimeRebaseMarkMachine 4
      ⟨runtimeRebaseMarkMachine.start, R, T0⟩ =
      ⟨RuntimeRebaseSeedState.done, R, Tm⟩ := by
    dsimp [T0, Tm, R, runtimeRebaseMarkMachine] at hm0 ⊢
    rw [markArchiveBoundary_prefixed] at hm0
    exact hm0
  have hf0 := runtimeArchiveLocator_run_prefixed
    (pre ++ [true, true]) rest
  have hf : run runtimeArchiveLocatorMachine
      (runtimeArchiveLocatorClock rest)
      ⟨runtimeArchiveLocatorMachine.start, R, Tm⟩ =
      ⟨RuntimeArchiveLocatorState.done,
        R + (selectedTail rest).length + 2, Tm⟩ := by
    simpa [Tm, R, List.append_assoc] using hf0
  have hmf := headSeq_run_at runtimeRebaseMarkMachine
    runtimeArchiveLocatorMachine T0 Tm Tm R 4
    (runtimeArchiveLocatorClock rest) R
    (R + (selectedTail rest).length + 2)
    RuntimeRebaseSeedState.done RuntimeArchiveLocatorState.done
    hm rfl hf rfl
  have hr0 := runtimeArchiveReverse_run_markedPrefixed pre [] first more
  have hr : run runtimeArchiveReverseMachine
      (runtimeArchiveReverseClock rest)
      ⟨runtimeArchiveReverseMachine.start,
        R + (selectedTail rest).length + 2, Tm⟩ =
      ⟨RuntimeArchiveReverseState.done, R, Tm⟩ := by
    simpa [rest, Tm, R, List.append_assoc] using hr0
  have hmfr := headSeq_run_at runtimeArchiveMarkLocateMachine
    runtimeArchiveReverseMachine T0 Tm Tm R
    (4 + 1 + runtimeArchiveLocatorClock rest)
    (runtimeArchiveReverseClock rest)
    (R + (selectedTail rest).length + 2) R
    (Sum.inr RuntimeArchiveLocatorState.done)
    RuntimeArchiveReverseState.done
    (by simpa [runtimeArchiveMarkLocateMachine] using hmf)
    rfl hr rfl
  have hs0 := runtimeRebaseSeed_run Tm R (by simp [R])
  have hs : run runtimeRebaseSeedMachine 4
      ⟨runtimeRebaseSeedMachine.start, R, Tm⟩ =
      ⟨RuntimeRebaseSeedState.done, R, T1⟩ := by
    dsimp [Tm, T1, R, runtimeRebaseSeedMachine] at hs0 ⊢
    rw [seedRebaseBoundary_prefixed] at hs0
    exact hs0
  have hall := headSeq_run_at runtimeArchiveMarkLocateReturnMachine
    runtimeRebaseSeedMachine T0 Tm T1 R
    (4 + 1 + runtimeArchiveLocatorClock rest + 1 +
      runtimeArchiveReverseClock rest) 4 R R
    (Sum.inr RuntimeArchiveReverseState.done)
    RuntimeRebaseSeedState.done
    (by simpa [runtimeArchiveMarkLocateReturnMachine] using hmfr)
    rfl hs rfl
  dsimp [rest, T0, T1, R] at hall ⊢
  simpa [runtimeArchiveReturnSeedMachine, runtimeArchiveReturnSeedClock,
    Nat.add_assoc] using hall

/-- Any tape with a two-cell physical prefix before a known suffix can be
split at that boundary without inspecting the two cells. -/
theorem split_two_before_suffix (T suffix : List Bool) (R : Nat)
    (hR : 2 ≤ R) (hRlen : R ≤ T.length) (hdrop : T.drop R = suffix) :
    ∃ pre a b, pre.length = R - 2 ∧ T = pre ++ [a, b] ++ suffix := by
  let pre := T.take (R - 2)
  let pair := (T.drop (R - 2)).take 2
  have hpre : pre.length = R - 2 := by
    simp [pre]
    omega
  have hsum : R - 2 + 2 = R := by omega
  have htwo : 2 ≤ (T.drop (R - 2)).length := by
    rw [List.length_drop]
    apply Nat.le_sub_of_add_le
    omega
  have hpairlen : pair.length = 2 := by
    dsimp [pair]
    rw [List.length_take, Nat.min_eq_left htwo]
  obtain ⟨a, b, hpair⟩ : ∃ a b, pair = [a, b] := by
    cases hp : pair with
    | nil => simp [hp] at hpairlen
    | cons a xs =>
        cases hx : xs with
        | nil => simp [hp, hx] at hpairlen
        | cons b ys =>
            cases hy : ys with
            | nil => exact ⟨a, b, by simp [hp, hx, hy]⟩
            | cons c zs => simp [hp, hx, hy] at hpairlen
  refine ⟨pre, a, b, hpre, ?_⟩
  have htail : T.drop (R - 2) = pair ++ T.drop R := by
    calc
      T.drop (R - 2) = (T.drop (R - 2)).take 2 ++
          (T.drop (R - 2)).drop 2 :=
        (List.take_append_drop 2 (T.drop (R - 2))).symm
      _ = pair ++ T.drop R := by
        simp only [pair, List.drop_drop, hsum]
  calc
    T = T.take (R - 2) ++ T.drop (R - 2) :=
      (List.take_append_drop (R - 2) T).symm
    _ = pre ++ pair ++ T.drop R := by
      rw [htail]
      simp [pre]
    _ = pre ++ [a, b] ++ suffix := by rw [hpair, hdrop]

/-- Boundary-contract form of the controller: only the discovered archive
suffix and the fact that two writable cells precede it are required. -/
theorem runtimeArchiveReturnSeed_run_of_drop
    (T : List Bool) (R : Nat) (first : List Bool)
    (more : List (List Bool))
    (hR : 2 ≤ R) (hRlen : R ≤ T.length)
    (hdrop : T.drop R = selectedTail (first :: more)) :
    ∃ pre a b,
      pre.length = R - 2 ∧
      T = pre ++ [a, b] ++ selectedTail (first :: more) ∧
      run runtimeArchiveReturnSeedMachine
          (runtimeArchiveReturnSeedClock (first :: more))
          ⟨runtimeArchiveReturnSeedMachine.start, R, T⟩ =
        ⟨Sum.inr RuntimeRebaseSeedState.done, R,
          pre ++ [false, true] ++ selectedTail (first :: more)⟩ := by
  obtain ⟨pre, a, b, hpre, hshape⟩ :=
    split_two_before_suffix T (selectedTail (first :: more)) R
      hR hRlen hdrop
  refine ⟨pre, a, b, hpre, hshape, ?_⟩
  rw [hshape]
  have hp := runtimeArchiveReturnSeed_run_prefixed pre a b first more
  simpa [show pre.length + 2 = R by omega] using hp

/-! ## Genuine scheduled post-cashout specialization -/

/-- The fixed controller consumes the real runtime-discovered archive origin.
Its only semantic input is the already-proved physical suffix equation; the
preceding cells are discovered and overwritten by the machine itself. -/
theorem scheduledRuntimeRelativeOutput_archiveReturnSeed
    (x w : List Bool) {t : Nat}
    (ht : t < (decodedLiterals x).length)
    (htnext : t + 1 < (decodedLiterals x).length) :
    let B := (decodedLiterals x).length
    let schedule := literalTapeSchedule x w
    let preBlocks := schedule.take t
    let l := scheduledLiteral x t
    let bits := literalLookupTape w l
    let rest := schedule.drop (t + 1)
    let pre := selectedPrefix (B - t) preBlocks
    let out := (scheduledTruths x w).take t
    let T := sourceSelectorInput B t schedule
    let n := sourceRuntimeLookupClock (B - t) preBlocks w l
    let M := runtimeRelativeOutputSourceMachine B
    let clock := runtimeRelativeOutputRouteClock B out T n
    let rcf := run (acceptRouteMachine M) clock
      (init (acceptRouteMachine M) (outputCap B out ++ T))
    let R := 2 * B + 2 + pre.length + 2 * bits.length + 4
    ∃ phys a b,
      phys.length = R - 2 ∧
      rcf.tp = phys ++ [a, b] ++ selectedTail rest ∧
      run runtimeArchiveReturnSeedMachine
          (runtimeArchiveReturnSeedClock rest)
          ⟨runtimeArchiveReturnSeedMachine.start, R, rcf.tp⟩ =
        ⟨Sum.inr RuntimeRebaseSeedState.done, R,
          phys ++ [false, true] ++ selectedTail rest⟩ := by
  dsimp only
  let B := (decodedLiterals x).length
  let schedule := literalTapeSchedule x w
  let preBlocks := schedule.take t
  let l := scheduledLiteral x t
  let bits := literalLookupTape w l
  let rest := schedule.drop (t + 1)
  let pre := selectedPrefix (B - t) preBlocks
  let out := (scheduledTruths x w).take t
  let T := sourceSelectorInput B t schedule
  let n := sourceRuntimeLookupClock (B - t) preBlocks w l
  let M := runtimeRelativeOutputSourceMachine B
  let clock := runtimeRelativeOutputRouteClock B out T n
  let rcf := run (acceptRouteMachine M) clock
    (init (acceptRouteMachine M) (outputCap B out ++ T))
  let R := 2 * B + 2 + pre.length + 2 * bits.length + 4
  have hfuture : rcf.tp.drop R = selectedTail rest := by
    simpa [B, schedule, preBlocks, l, bits, rest, pre, out, T, n, M,
      clock, rcf, R] using
      scheduledRuntimeRelativeOutput_futureArchive x w ht
  have hslen : schedule.length = B := by
    simp [schedule, B, literalTapeSchedule]
  have hrestpos : 0 < rest.length := by
    simp [rest, hslen]
    omega
  obtain ⟨first, more, hrest⟩ := List.exists_cons_of_ne_nil
    (List.ne_nil_of_length_pos hrestpos)
  have htailpos : 0 < (selectedTail rest).length := by
    rw [hrest]
    simp [selectedTail_cons]
  have hRlen : R ≤ rcf.tp.length := by
    have hlen := congrArg List.length hfuture
    simp only [List.length_drop] at hlen
    omega
  have hr := runtimeArchiveReturnSeed_run_of_drop rcf.tp R first more
    (by simp [R]) hRlen (by simpa [hrest] using hfuture)
  obtain ⟨phys, a, b, hphys, hshape, hrun⟩ := hr
  refine ⟨phys, a, b, ?_, ?_, ?_⟩
  · simpa [R] using hphys
  · simpa [B, schedule, preBlocks, l, bits, rest, pre, out, T, n,
      M, clock, rcf, hrest] using hshape
  · simpa [B, schedule, preBlocks, l, bits, rest, pre, out, T, n,
      M, clock, rcf, R, hrest] using hrun

/-- Physical-origin controller: rediscover the future archive from the real
cashout tape, install the marker, traverse and return, then leave the canonical
`01` boundary immediately before the untouched archive. -/
def outputWorkspaceArchiveReturnSeedMachine : Machine :=
  headSeqMachine outputWorkspaceTailLocatorMachine
    runtimeArchiveReturnSeedMachine

theorem scheduledRuntimeRelativeOutput_physicalArchiveReturnSeed
    (x w : List Bool) {t : Nat}
    (ht : t < (decodedLiterals x).length)
    (htnext : t + 1 < (decodedLiterals x).length) :
    let B := (decodedLiterals x).length
    let schedule := literalTapeSchedule x w
    let preBlocks := schedule.take t
    let l := scheduledLiteral x t
    let bits := literalLookupTape w l
    let rest := schedule.drop (t + 1)
    let pre := selectedPrefix (B - t) preBlocks
    let out := (scheduledTruths x w).take t
    let out' := (scheduledTruths x w).take (t + 1)
    let T := sourceSelectorInput B t schedule
    let n := sourceRuntimeLookupClock (B - t) preBlocks w l
    let M := runtimeRelativeOutputSourceMachine B
    let routeClock := runtimeRelativeOutputRouteClock B out T n
    let rcf := run (acceptRouteMachine M) routeClock
      (init (acceptRouteMachine M) (outputCap B out ++ T))
    let locateClock := outputSourceLocatorClock B out' + 1 +
      (pre.length + 2)
    let tailClock := 8 * l.1 + 22
    let prefixClock := locateClock + 1 + tailClock
    let R := 2 * B + 2 + pre.length + 2 * bits.length + 4
    ∃ phys a b,
      phys.length = R - 2 ∧
      rcf.tp = phys ++ [a, b] ++ selectedTail rest ∧
      run outputWorkspaceArchiveReturnSeedMachine
          (prefixClock + 1 + runtimeArchiveReturnSeedClock rest)
          (init outputWorkspaceArchiveReturnSeedMachine rcf.tp) =
        ⟨Sum.inr (Sum.inr RuntimeRebaseSeedState.done), R,
          phys ++ [false, true] ++ selectedTail rest⟩ := by
  dsimp only
  let B := (decodedLiterals x).length
  let schedule := literalTapeSchedule x w
  let preBlocks := schedule.take t
  let l := scheduledLiteral x t
  let bits := literalLookupTape w l
  let rest := schedule.drop (t + 1)
  let pre := selectedPrefix (B - t) preBlocks
  let out := (scheduledTruths x w).take t
  let out' := (scheduledTruths x w).take (t + 1)
  let T := sourceSelectorInput B t schedule
  let n := sourceRuntimeLookupClock (B - t) preBlocks w l
  let M := runtimeRelativeOutputSourceMachine B
  let routeClock := runtimeRelativeOutputRouteClock B out T n
  let rcf := run (acceptRouteMachine M) routeClock
    (init (acceptRouteMachine M) (outputCap B out ++ T))
  let locateClock := outputSourceLocatorClock B out' + 1 +
    (pre.length + 2)
  let tailClock := 8 * l.1 + 22
  let prefixClock := locateClock + 1 + tailClock
  let R := 2 * B + 2 + pre.length + 2 * bits.length + 4
  have hloc := scheduledRuntimeRelativeOutput_physicalWorkspaceTailLocate
    x w ht htnext
  have hseed := scheduledRuntimeRelativeOutput_archiveReturnSeed
    x w ht htnext
  obtain ⟨phys, a, b, hphys, hshape, hrun⟩ := hseed
  let finalTape := phys ++ [false, true] ++ selectedTail rest
  have hjoin := headSeq_run outputWorkspaceTailLocatorMachine
    runtimeArchiveReturnSeedMachine rcf.tp rcf.tp finalTape
    prefixClock (runtimeArchiveReturnSeedClock rest) R R
    (Sum.inr RuntimeWorkspaceTailLocatorState.done)
    (Sum.inr RuntimeRebaseSeedState.done)
    (by simpa [B, schedule, preBlocks, l, bits, rest, pre, out, out', T,
      n, M, routeClock, rcf, locateClock, tailClock, prefixClock, R]
      using hloc)
    rfl
    (by simpa [B, schedule, preBlocks, l, bits, rest, pre, out, T, n,
      M, routeClock, rcf, R, finalTape] using hrun)
    rfl
  refine ⟨phys, a, b, ?_, ?_, ?_⟩
  · simpa [B, schedule, preBlocks, l, bits, rest, pre, R] using hphys
  · simpa [B, schedule, preBlocks, l, bits, rest, pre, out, T, n,
      M, routeClock, rcf] using hshape
  · simpa [outputWorkspaceArchiveReturnSeedMachine, finalTape,
      prefixClock] using hjoin

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeArchiveReturnWriter

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeArchiveReturnWriter.archiveReverse_run_nonfirstBlock
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeArchiveReturnWriter.archiveReverse_run_firstBlock
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeArchiveReturnWriter.runtimeArchiveReverse_run_prefixed
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeArchiveReturnWriter.runtimeRebaseSeed_run
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeArchiveReturnWriter.runtimeArchiveReturnSeed_run_prefixed
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeArchiveReturnWriter.scheduledRuntimeRelativeOutput_physicalArchiveReturnSeed
