import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeMarkedEntry

/-!
# Charged local lookup: complete lookup from a rebased archive front

After unary rebase the surviving archive is fresh: its selector index is
zero.  This file composes the reset-free front selector with the existing
in-place compactor, canonical rewind, and `masterM`.  The resulting accepting
machine is fixed, preserves the rebased selector prefix, and returns the real
literal truth bit.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeFrontLookup

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinMaster
open PallLean.Paper93.DeepMath.PathB.CookLevinRoundInvariant
open PallLean.Paper93.DeepMath.PathB.CookLevinWholeRun
open PallLean.Paper93.DeepMath.PathB.CookLevinInP
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLiteralWeld
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryTerminal
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryWholeRun
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixAdapter
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixRun
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceCompact
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceLookup
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeLeftSafety
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeMarkedEntry
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundEntryLocator
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundEntryAdapter

def runtimeFrontSelectCompactMachine : Machine :=
  headSeqMachine runtimeFrontSelectorMachine sourceCompactMachine

def runtimeFrontSelectCompactRewindMachine : Machine :=
  headSeqMachine runtimeFrontSelectCompactMachine sourceRewindMachine

def runtimeFrontLookupCore : Machine :=
  headSeqAcceptMachine runtimeFrontSelectCompactRewindMachine masterM

def runtimeFrontLookupClock (d : Nat) (w : List Bool) (l : Lit) : Nat :=
  (2 * d + 4 + 1 + sourceCompactClock (literalLookupTape w l)) + 1 +
    canonicalRewindClock w l + 1 + literalLookupClock w l

theorem runtimeFrontLookup_run (w : List Bool) (l : Lit)
    (rest : List (List Bool)) :
    let bits := literalLookupTape w l
    let d := (bits :: rest).length
    let source := sourceSelectorInput d 0 (bits :: rest)
    let pre := flattenPairs (List.replicate d (true, true)) ++ [false, true]
    let archiveTail := flattenPairs (rest.flatMap freshSourceBlock)
    let trailer := [true, false, false, true] ++
      List.replicate bits.length true ++ archiveTail
    let mcf := run masterM (literalLookupClock w l)
      (init masterM (bits ++ trailer))
    run runtimeFrontLookupCore (runtimeFrontLookupClock d w l)
        (init runtimeFrontLookupCore source) =
      ⟨Sum.inr mcf.st, pre.length + mcf.hd, pre ++ mcf.tp⟩ := by
  dsimp only
  let bits := literalLookupTape w l
  let d := (bits :: rest).length
  let source := sourceSelectorInput d 0 (bits :: rest)
  let pre := flattenPairs (List.replicate d (true, true)) ++ [false, true]
  let archiveTail := flattenPairs (rest.flatMap freshSourceBlock)
  let trailer := [true, false, false, true] ++
    List.replicate bits.length true ++ archiveTail
  have hsource : source = pre ++ [true, false] ++ encodeD bits ++ archiveTail := by
    change sourceSelectorInput (bits :: rest).length 0 (bits :: rest) = _
    rw [sourceSelectorInput_front]
    simp [d, pre, archiveTail, runtimeFrontSelectorInput,
      List.append_assoc]
  have hpreLen : pre.length = 2 * d + 2 := by
    simp [pre, flattenPairs_length]
  have hfront0 := runtimeFrontSelector_run d (encodeD bits ++ archiveTail)
  have hfront : run runtimeFrontSelectorMachine (2 * d + 4)
      (init runtimeFrontSelectorMachine source) =
      ⟨RuntimeFrontSelectorState.done, pre.length + 2, source⟩ := by
    rw [hsource]
    simpa [pre, hpreLen, List.append_assoc] using hfront0
  have hcompact0 := sourceCompact_run pre bits archiveTail
  have hcompact : run sourceCompactMachine (sourceCompactClock bits)
      ⟨sourceCompactMachine.start, pre.length + 2, source⟩ =
      ⟨SourceCompactState.done, pre.length + bits.length + 3,
        pre ++ bits ++ trailer⟩ := by
    rw [hsource]
    simpa [sourceCompactMachine, trailer, List.append_assoc] using hcompact0
  have hfirst := headSeq_run runtimeFrontSelectorMachine sourceCompactMachine
    source source (pre ++ bits ++ trailer)
    (2 * d + 4) (sourceCompactClock bits)
    (pre.length + 2) (pre.length + bits.length + 3)
    RuntimeFrontSelectorState.done SourceCompactState.done
    hfront rfl hcompact rfl
  have hrew0 := sourceRewind_literal pre w l
    (List.replicate bits.length true ++ archiveTail)
  have hrew : run sourceRewindMachine (canonicalRewindClock w l)
      ⟨sourceRewindMachine.start, pre.length + bits.length + 3,
        pre ++ bits ++ trailer⟩ =
      ⟨SourceRewindState.done, pre.length, pre ++ bits ++ trailer⟩ := by
    simpa [bits, trailer, List.append_assoc] using hrew0
  have hsecond := headSeq_run runtimeFrontSelectCompactMachine
    sourceRewindMachine source (pre ++ bits ++ trailer)
    (pre ++ bits ++ trailer)
    (2 * d + 4 + 1 + sourceCompactClock bits)
    (canonicalRewindClock w l)
    (pre.length + bits.length + 3) pre.length
    (Sum.inr SourceCompactState.done) SourceRewindState.done
    (by simpa [runtimeFrontSelectCompactMachine, Nat.add_assoc] using hfirst)
    rfl hrew rfl
  let mcf := run masterM (literalLookupClock w l)
    (init masterM (bits ++ trailer))
  have hmaster : run masterM (literalLookupClock w l)
      ⟨masterM.start, pre.length, pre ++ bits ++ trailer⟩ =
      shiftCfg masterM pre mcf := by
    simpa [bits, mcf, List.append_assoc] using
      masterM_run_shifted pre w l trailer
  let A := signedLookupAssignment w l.1 l.2
  have hv : l.1 ≤ A.length := by
    dsimp only [A]
    rw [signedLookupAssignment_length]
    omega
  have hinv : RoundInv (bits ++ trailer) l.1 A.length := by
    dsimp only [bits, A]
    exact literalLookupTape_append_roundInv w l trailer
  have happ := readAv_promise (bits ++ trailer) l.1 A.length hv hinv
  have hmhalt : masterM.halt mcf.st = true := by
    simpa [mcf, literalLookupClock, A, bits] using happ.1
  have hfinal := headSeqAccept_run runtimeFrontSelectCompactRewindMachine
    masterM source (pre ++ bits ++ trailer) (pre ++ mcf.tp)
    ((2 * d + 4 + 1 + sourceCompactClock bits) + 1 +
      canonicalRewindClock w l)
    (literalLookupClock w l) pre.length (pre.length + mcf.hd)
    (Sum.inr SourceRewindState.done) mcf.st
    (by simpa [runtimeFrontSelectCompactRewindMachine, Nat.add_assoc]
      using hsecond)
    rfl (by simpa [shiftCfg] using hmaster) hmhalt
  simpa [runtimeFrontLookupCore, runtimeFrontLookupClock, bits, d, source,
    pre, archiveTail, trailer, mcf, Nat.add_assoc] using hfinal

private theorem sourceCompact_move_ne_reset
    (s : sourceCompactMachine.State) (b : Bool) :
    (sourceCompactMachine.δ s b).2.2 ≠ 3 := by
  cases s <;> simp [sourceCompactMachine] <;> split_ifs <;> simp

private theorem sourceRewind_move_ne_reset
    (s : sourceRewindMachine.State) (b : Bool) :
    (sourceRewindMachine.δ s b).2.2 ≠ 3 := by
  cases s <;> simp [sourceRewindMachine] <;> split_ifs <;> simp

private theorem headSeq_move_ne_reset (M1 M2 : Machine)
    (h1 : ∀ s b, (M1.δ s b).2.2 ≠ 3)
    (h2 : ∀ s b, (M2.δ s b).2.2 ≠ 3)
    (s : (headSeqMachine M1 M2).State) (b : Bool) :
    ((headSeqMachine M1 M2).δ s b).2.2 ≠ 3 := by
  rcases s with s | s
  · by_cases hh : M1.halt s = true
    · simp [headSeqMachine, hh]
    · have hh' : M1.halt s = false := by simpa using hh
      simpa [headSeqMachine, hh'] using h1 s b
  · simpa [headSeqMachine] using h2 s b

private theorem headSeqAccept_move_ne_reset (M1 M2 : Machine)
    (h1 : ∀ s b, (M1.δ s b).2.2 ≠ 3)
    (h2 : ∀ s b, (M2.δ s b).2.2 ≠ 3)
    (s : (headSeqAcceptMachine M1 M2).State) (b : Bool) :
    ((headSeqAcceptMachine M1 M2).δ s b).2.2 ≠ 3 := by
  rcases s with s | s
  · by_cases hh : M1.halt s = true
    · simp [headSeqAcceptMachine, hh]
    · have hh' : M1.halt s = false := by simpa using hh
      simpa [headSeqAcceptMachine, hh'] using h1 s b
  · simpa [headSeqAcceptMachine] using h2 s b

theorem runtimeFrontLookupCore_move_ne_reset
    (s : runtimeFrontLookupCore.State) (b : Bool) :
    (runtimeFrontLookupCore.δ s b).2.2 ≠ 3 := by
  apply headSeqAccept_move_ne_reset
  · apply headSeq_move_ne_reset
    · apply headSeq_move_ne_reset
      · exact runtimeFrontSelector_move_ne_reset
      · exact sourceCompact_move_ne_reset
    · exact sourceRewind_move_ne_reset
  · exact masterM_reset_free

set_option maxHeartbeats 1000000 in
theorem runtimeFrontLookup_leftSafe (w : List Bool) (l : Lit)
    (rest : List (List Bool)) :
    let bits := literalLookupTape w l
    let d := (bits :: rest).length
    let source := sourceSelectorInput d 0 (bits :: rest)
    LeftSafeRun runtimeFrontLookupCore (init runtimeFrontLookupCore source)
      (runtimeFrontLookupClock d w l) := by
  dsimp only
  let bits := literalLookupTape w l
  let d := (bits :: rest).length
  let source := sourceSelectorInput d 0 (bits :: rest)
  let pre := flattenPairs (List.replicate d (true, true)) ++ [false, true]
  let archiveTail := flattenPairs (rest.flatMap freshSourceBlock)
  let trailer := [true, false, false, true] ++
    List.replicate bits.length true ++ archiveTail
  have hsource : source = pre ++ [true, false] ++ encodeD bits ++ archiveTail := by
    change sourceSelectorInput (bits :: rest).length 0 (bits :: rest) = _
    rw [sourceSelectorInput_front]
    simp [d, pre, archiveTail, runtimeFrontSelectorInput,
      List.append_assoc]
  have hpreLen : pre.length = 2 * d + 2 := by
    simp [pre, flattenPairs_length]
  have hfront0 := runtimeFrontSelector_run d (encodeD bits ++ archiveTail)
  have hfront : run runtimeFrontSelectorMachine (2 * d + 4)
      (init runtimeFrontSelectorMachine source) =
      ⟨RuntimeFrontSelectorState.done, pre.length + 2, source⟩ := by
    rw [hsource]
    simpa [pre, hpreLen, List.append_assoc] using hfront0
  have hsfront : LeftSafeRun runtimeFrontSelectorMachine
      (init runtimeFrontSelectorMachine source) (2 * d + 4) := by
    intro i hi
    exact (runtimeFrontSelector_prefixSafe source (2 * d + 4) i hi).leftInside
  have hcompact0 := sourceCompact_run pre bits archiveTail
  have hcompact : run sourceCompactMachine (sourceCompactClock bits)
      ⟨sourceCompactMachine.start, pre.length + 2, source⟩ =
      ⟨SourceCompactState.done, pre.length + bits.length + 3,
        pre ++ bits ++ trailer⟩ := by
    rw [hsource]
    simpa [sourceCompactMachine, trailer, List.append_assoc] using hcompact0
  have hscompact : LeftSafeRun sourceCompactMachine
      ⟨sourceCompactMachine.start, pre.length + 2, source⟩
      (sourceCompactClock bits) := by
    rw [hsource]
    simpa [sourceCompactMachine] using
      sourceCompact_run_leftSafe pre bits archiveTail
  have hfirst := headSeq_run runtimeFrontSelectorMachine sourceCompactMachine
    source source (pre ++ bits ++ trailer)
    (2 * d + 4) (sourceCompactClock bits)
    (pre.length + 2) (pre.length + bits.length + 3)
    RuntimeFrontSelectorState.done SourceCompactState.done
    hfront rfl hcompact rfl
  have hsfirst : LeftSafeRun runtimeFrontSelectCompactMachine
      (init runtimeFrontSelectCompactMachine source)
      (2 * d + 4 + 1 + sourceCompactClock bits) := by
    exact headSeq_leftSafe runtimeFrontSelectorMachine sourceCompactMachine
      source source (2 * d + 4) (sourceCompactClock bits)
      (pre.length + 2) RuntimeFrontSelectorState.done
      hfront rfl hsfront hscompact (by rw [hcompact]; rfl)
  have hrew0 := sourceRewind_literal pre w l
    (List.replicate bits.length true ++ archiveTail)
  have hrew : run sourceRewindMachine (canonicalRewindClock w l)
      ⟨sourceRewindMachine.start, pre.length + bits.length + 3,
        pre ++ bits ++ trailer⟩ =
      ⟨SourceRewindState.done, pre.length, pre ++ bits ++ trailer⟩ := by
    simpa [bits, trailer, List.append_assoc] using hrew0
  have hsrew : LeftSafeRun sourceRewindMachine
      ⟨sourceRewindMachine.start, pre.length + bits.length + 3,
        pre ++ bits ++ trailer⟩ (canonicalRewindClock w l) := by
    simpa [bits, trailer, canonicalRewindClock, rewindTape,
      literalLookupTape_rewind_shape, List.append_assoc] using
      sourceRewind_run_leftSafe pre (literalMiddlePairs w l)
        (List.replicate bits.length true ++ archiveTail)
        (literalMiddlePairs_noRend w l)
  have hsecond := headSeq_run runtimeFrontSelectCompactMachine
    sourceRewindMachine source (pre ++ bits ++ trailer)
    (pre ++ bits ++ trailer)
    (2 * d + 4 + 1 + sourceCompactClock bits)
    (canonicalRewindClock w l)
    (pre.length + bits.length + 3) pre.length
    (Sum.inr SourceCompactState.done) SourceRewindState.done
    (by simpa [runtimeFrontSelectCompactMachine, Nat.add_assoc] using hfirst)
    rfl hrew rfl
  have hssecond : LeftSafeRun runtimeFrontSelectCompactRewindMachine
      (init runtimeFrontSelectCompactRewindMachine source)
      ((2 * d + 4 + 1 + sourceCompactClock bits) + 1 +
        canonicalRewindClock w l) := by
    exact headSeq_leftSafe runtimeFrontSelectCompactMachine sourceRewindMachine
      source (pre ++ bits ++ trailer)
      (2 * d + 4 + 1 + sourceCompactClock bits)
      (canonicalRewindClock w l)
      (pre.length + bits.length + 3) (Sum.inr SourceCompactState.done)
      (by simpa [runtimeFrontSelectCompactMachine, Nat.add_assoc] using hfirst)
      rfl hsfirst hsrew (by rw [hrew]; rfl)
  let mcf := run masterM (literalLookupClock w l)
    (init masterM (bits ++ trailer))
  have hmaster : run masterM (literalLookupClock w l)
      ⟨masterM.start, pre.length, pre ++ bits ++ trailer⟩ =
      shiftCfg masterM pre mcf := by
    simpa [bits, mcf, List.append_assoc] using
      masterM_run_shifted pre w l trailer
  let A := signedLookupAssignment w l.1 l.2
  have hv : l.1 ≤ A.length := by
    dsimp only [A]
    rw [signedLookupAssignment_length]
    omega
  have hinv : RoundInv (bits ++ trailer) l.1 A.length := by
    dsimp only [bits, A]
    exact literalLookupTape_append_roundInv w l trailer
  have happ := readAv_promise (bits ++ trailer) l.1 A.length hv hinv
  have hmhalt : masterM.halt mcf.st = true := by
    simpa [mcf, literalLookupClock, A, bits] using happ.1
  have hmasterLeft : LeftSafeRun masterM
      (init masterM (bits ++ trailer)) (literalLookupClock w l) := by
    have hs := fullRun_leftSafe (bits ++ trailer) l.1 A.length hv hinv
    simpa [literalLookupClock, A, bits, master_forced_init] using hs
  have hmasterPrefix : PrefixSafeRun masterM
      (init masterM (bits ++ trailer)) (literalLookupClock w l) := by
    intro i hi
    exact ⟨fun _ => masterM_reset_free _ _, hmasterLeft i hi⟩
  have hmasterShift : LeftSafeRun masterM
      ⟨masterM.start, pre.length, pre ++ bits ++ trailer⟩
      (literalLookupClock w l) := by
    simpa [shiftCfg] using leftSafeRun_shiftCfg masterM pre
      (init masterM (bits ++ trailer)) (literalLookupClock w l)
      hmasterPrefix hmasterLeft
  have hmasterHalt : masterM.halt
      (run masterM (literalLookupClock w l)
        ⟨masterM.start, pre.length, pre ++ bits ++ trailer⟩).st = true := by
    rw [hmaster]
    simpa [shiftCfg] using hmhalt
  have hsall := headSeqAccept_leftSafe
    runtimeFrontSelectCompactRewindMachine masterM source
    (pre ++ bits ++ trailer)
    ((2 * d + 4 + 1 + sourceCompactClock bits) + 1 +
      canonicalRewindClock w l)
    (literalLookupClock w l) pre.length (Sum.inr SourceRewindState.done)
    (by simpa [runtimeFrontSelectCompactRewindMachine, Nat.add_assoc]
      using hsecond)
    rfl hssecond hmasterShift hmasterHalt
  simpa [runtimeFrontLookupCore, runtimeFrontLookupClock, bits, d, source,
    Nat.add_assoc] using hsall

/-- The complete rebased lookup is safe to execute after an arbitrary
runtime-discovered marker prefix. -/
theorem runtimeFrontLookup_prefixSafe (w : List Bool) (l : Lit)
    (rest : List (List Bool)) :
    let bits := literalLookupTape w l
    let d := (bits :: rest).length
    let source := sourceSelectorInput d 0 (bits :: rest)
    PrefixSafeRun runtimeFrontLookupCore (init runtimeFrontLookupCore source)
      (runtimeFrontLookupClock d w l) := by
  dsimp only
  have hleft := runtimeFrontLookup_leftSafe w l rest
  intro i hi
  exact ⟨fun _ => runtimeFrontLookupCore_move_ne_reset _ _, hleft i hi⟩

theorem runtimeFrontLookup_halt_accept (w : List Bool) (l : Lit)
    (rest : List (List Bool)) :
    let bits := literalLookupTape w l
    let d := (bits :: rest).length
    let source := sourceSelectorInput d 0 (bits :: rest)
    let cf := run runtimeFrontLookupCore (runtimeFrontLookupClock d w l)
      (init runtimeFrontLookupCore source)
    runtimeFrontLookupCore.halt cf.st = true ∧
      runtimeFrontLookupCore.accept cf.st =
        evalLit (fun k => w.getD k false) l := by
  dsimp only
  let bits := literalLookupTape w l
  let d := (bits :: rest).length
  let source := sourceSelectorInput d 0 (bits :: rest)
  let pre := flattenPairs (List.replicate d (true, true)) ++ [false, true]
  let archiveTail := flattenPairs (rest.flatMap freshSourceBlock)
  let trailer := [true, false, false, true] ++
    List.replicate bits.length true ++ archiveTail
  let mcf := run masterM (literalLookupClock w l)
    (init masterM (bits ++ trailer))
  have hrun := runtimeFrontLookup_run w l rest
  have hrun' : run runtimeFrontLookupCore (runtimeFrontLookupClock d w l)
      (init runtimeFrontLookupCore source) =
      ⟨Sum.inr mcf.st, pre.length + mcf.hd, pre ++ mcf.tp⟩ := by
    simpa [bits, d, source, pre, archiveTail, trailer, mcf] using hrun
  let A := signedLookupAssignment w l.1 l.2
  have hv : l.1 ≤ A.length := by
    dsimp only [A]
    rw [signedLookupAssignment_length]
    omega
  have hinv : RoundInv (bits ++ trailer) l.1 A.length := by
    dsimp only [bits, A]
    exact literalLookupTape_append_roundInv w l trailer
  have happ := readAv_promise (bits ++ trailer) l.1 A.length hv hinv
  have hmhalt : masterM.halt mcf.st = true := by
    simpa [mcf, literalLookupClock, A, bits] using happ.1
  have hidx : 2 * l.1 + 4 + 2 * l.1 < bits.length := by
    simp [bits, literalLookupTape, CookLevinInP.encode,
      signedLookupAssignment_length,
      PallLean.Paper93.DeepMath.PathB.CookLevinInP.double_length]
    omega
  have hpureInv : RoundInv bits l.1 A.length := by
    dsimp only [bits, A]
    simpa [literalLookupTape, A] using
      encode_roundInv (signedLookupAssignment w l.1 l.2) l.1
  have hpure := readAv_promise bits l.1 A.length hv hpureInv
  have hvalue : bits.getD (2 * l.1 + 4 + 2 * l.1) false =
      evalLit (fun k => w.getD k false) l := by
    have hm := (masterM_reads_literal w l).2
    rw [← hpure.2]
    simpa [decideOut, literalLookupClock, A, bits] using hm
  have hmacc : masterM.accept mcf.st =
      evalLit (fun k => w.getD k false) l := by
    have ha := happ.2
    rw [List.getD_append bits trailer false
      (2 * l.1 + 4 + 2 * l.1) hidx, hvalue] at ha
    simpa [decideOut, mcf, literalLookupClock, A, bits] using ha
  rw [hrun']
  constructor
  · simpa [runtimeFrontLookupCore, headSeqAcceptMachine] using hmhalt
  · simpa [runtimeFrontLookupCore, headSeqAcceptMachine] using hmacc

def runtimeMarkedFrontLookupMachine : Machine :=
  runtimeMarkedAcceptBody runtimeFrontLookupCore

def runtimeMarkedFrontLookupClock (pairs : List (Bool × Bool))
    (d : Nat) (w : List Bool) (l : Lit) : Nat :=
  runtimeMarkedAcceptClock pairs (runtimeFrontLookupClock d w l)

/-- Complete execution from an arbitrary reachable residue, through the
doubled marker and rebased selector, to the real accepting lookup endpoint. -/
theorem runtimeMarkedFrontLookup_run
    (pairs : List (Bool × Bool)) (w : List Bool) (l : Lit)
    (rest : List (List Bool))
    (hsafe : RuntimeNoDoubleSepFrom false pairs) :
    let bits := literalLookupTape w l
    let d := (bits :: rest).length
    let source := sourceSelectorInput d 0 (bits :: rest)
    let markerPre := flattenPairs pairs ++ [false, true, false, true]
    let sourcePre := flattenPairs (List.replicate d (true, true)) ++
      [false, true]
    let archiveTail := flattenPairs (rest.flatMap freshSourceBlock)
    let trailer := [true, false, false, true] ++
      List.replicate bits.length true ++ archiveTail
    let mcf := run masterM (literalLookupClock w l)
      (init masterM (bits ++ trailer))
    run runtimeMarkedFrontLookupMachine
        (runtimeMarkedFrontLookupClock pairs d w l)
        (init runtimeMarkedFrontLookupMachine (markerPre ++ source)) =
      ⟨Sum.inr (Sum.inr mcf.st),
        markerPre.length + (sourcePre.length + mcf.hd),
        markerPre ++ sourcePre ++ mcf.tp⟩ := by
  dsimp only
  let bits := literalLookupTape w l
  let d := (bits :: rest).length
  let source := sourceSelectorInput d 0 (bits :: rest)
  let sourcePre := flattenPairs (List.replicate d (true, true)) ++
    [false, true]
  let archiveTail := flattenPairs (rest.flatMap freshSourceBlock)
  let trailer := [true, false, false, true] ++
    List.replicate bits.length true ++ archiveTail
  let mcf := run masterM (literalLookupClock w l)
    (init masterM (bits ++ trailer))
  have hsource : source = true :: true :: source.drop 2 := by
    change sourceSelectorInput (bits :: rest).length 0 (bits :: rest) =
      true :: true ::
        (sourceSelectorInput (bits :: rest).length 0 (bits :: rest)).drop 2
    rw [sourceSelectorInput_front]
    simp [runtimeFrontSelectorInput, List.replicate_succ, flattenPairs,
      List.append_assoc]
  have hrun := runtimeFrontLookup_run w l rest
  have hrun' : run runtimeFrontLookupCore (runtimeFrontLookupClock d w l)
      (init runtimeFrontLookupCore source) =
      ⟨Sum.inr mcf.st, sourcePre.length + mcf.hd,
        sourcePre ++ mcf.tp⟩ := by
    simpa [bits, d, source, sourcePre, archiveTail, trailer, mcf] using hrun
  have hh := (runtimeFrontLookup_halt_accept w l rest).1
  have hhalt : runtimeFrontLookupCore.halt (Sum.inr mcf.st) = true := by
    rw [show run runtimeFrontLookupCore (runtimeFrontLookupClock d w l)
        (init runtimeFrontLookupCore source) =
      ⟨Sum.inr mcf.st, sourcePre.length + mcf.hd,
        sourcePre ++ mcf.tp⟩ from hrun'] at hh
    exact hh
  have hp := runtimeFrontLookup_prefixSafe w l rest
  have hjoined := runtimeMarkedAcceptBody_run runtimeFrontLookupCore pairs
    source (sourcePre ++ mcf.tp) true true hsafe hsource
    (by simp [runtimePairIsSep]) (runtimeFrontLookupClock d w l)
    (Sum.inr mcf.st) (sourcePre.length + mcf.hd) hrun' hhalt hp
  simpa [runtimeMarkedFrontLookupMachine, runtimeMarkedFrontLookupClock,
    bits, d, source, sourcePre, archiveTail, trailer, mcf,
    List.append_assoc] using hjoined

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeFrontLookup

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeFrontLookup.runtimeFrontLookup_run
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeFrontLookup.runtimeFrontLookup_prefixSafe
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeFrontLookup.runtimeFrontLookup_halt_accept
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeFrontLookup.runtimeMarkedFrontLookup_run
