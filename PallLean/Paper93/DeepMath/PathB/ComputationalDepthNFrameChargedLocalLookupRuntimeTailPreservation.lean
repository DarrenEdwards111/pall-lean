import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeRelativeOutput

/-!
# Runtime lookup tail preservation

The lookup body destructively shifts its canonical literal prefix, but every
write remains strictly before the input's original `REND` boundary.  Hence an
arbitrary trailer, in particular the untouched future source archive, remains
byte-for-byte unchanged.  This is the structural fact needed by the next-round
progression transducer.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeTailPreservation

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinMaster
open PallLean.Paper93.DeepMath.PathB.CookLevinMasterRound
open PallLean.Paper93.DeepMath.PathB.CookLevinRendShift
open PallLean.Paper93.DeepMath.PathB.CookLevinRoundInvariant
open PallLean.Paper93.DeepMath.PathB.CookLevinWholeRun
open PallLean.Paper93.DeepMath.PathB.CookLevinInP
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLiteralWeld
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixRun
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceCompact
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceLookup
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRelativeOutput
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupDynamicRoute
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupOutputCapacity
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRepeatController
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeStage
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupScheduleBound

theorem rsTape_length_of_le (x : List Bool) (q k : Nat)
    (h : q + 2 * k ≤ x.length) :
    (rsTape x q k).length = x.length := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hk : q + 2 * k ≤ x.length := by omega
      have hlen := ih hk
      simp only [rsTape]
      have h0 : q + 2 * k < (rsTape x q k).length := by omega
      have h1 : q + 2 * k + 1 <
          (writeAt (rsTape x q k) (q + 2 * k)
            (x.getD (q + 2 * k + 2) false)).length := by
        rw [writeAt_of_lt _ h0, List.length_set, hlen]
        omega
      rw [writeAt_of_lt _ h1, List.length_set,
        writeAt_of_lt _ h0, List.length_set, hlen]

/-- Every suffix beginning weakly after the complete shifted window is
preserved exactly, not merely pointwise on an infinite default tape. -/
theorem rsTape_drop_of_le (x : List Bool) (q k R : Nat)
    (hwin : q + 2 * k ≤ R) (hR : R ≤ x.length) :
    (rsTape x q k).drop R = x.drop R := by
  have hlen : (rsTape x q k).length = x.length :=
    rsTape_length_of_le x q k (by omega)
  apply List.ext_getElem
  · simp [hlen]
  · intro i hi1 hi2
    have hpos : q + 2 * k ≤ R + i := by omega
    have hcell := rsTape_getD_ge x q (R + i) k hpos
    have hr1 : R + i < (rsTape x q k).length := by
      simp only [List.length_drop] at hi1
      omega
    have hr2 : R + i < x.length := by
      simp only [List.length_drop] at hi2
      omega
    rw [List.getElem_drop, List.getElem_drop]
    rw [List.getD_eq_getElem _ _ hr1,
      List.getD_eq_getElem _ _ hr2] at hcell
    exact hcell

/-- One invariant-level lookup round preserves any suffix beyond the original
counter/data/REND footprint. -/
theorem roundInv_round_drop (T : List Bool) (k D R : Nat)
    (hk : 1 ≤ k) (hD : 1 ≤ D) (h : RoundInv T k D)
    (hbound : 2 * k + 2 * D + 6 ≤ R) (hR : R ≤ T.length) :
    let T' := rsTape (rsTape T (2 * k + 4) D) (2 * k) (D + 1)
    T'.drop R = T.drop R ∧ T'.length = T.length := by
  dsimp only
  let TA := rsTape T (2 * k + 4) D
  have hTAle : 2 * k + 4 + 2 * D ≤ T.length := by omega
  have hTAlen : TA.length = T.length := by
    exact rsTape_length_of_le T (2 * k + 4) D hTAle
  have hdropA : TA.drop R = T.drop R := by
    exact rsTape_drop_of_le T (2 * k + 4) D R (by omega) hR
  let TB := rsTape TA (2 * k) (D + 1)
  have hTBlen : TB.length = TA.length := by
    exact rsTape_length_of_le TA (2 * k) (D + 1) (by
      rw [hTAlen]
      omega)
  have hdropB : TB.drop R = TA.drop R := by
    exact rsTape_drop_of_le TA (2 * k) (D + 1) R (by omega) (by
      rw [hTAlen]
      exact hR)
  exact ⟨hdropB.trans hdropA, hTBlen.trans hTAlen⟩

/-- All counter-deletion rounds preserve the same original trailer boundary. -/
theorem rounds_drop (v : Nat) : ∀ (T : List Bool) (D R : Nat),
    v ≤ D → RoundInv T v D →
    2 * v + 2 * D + 6 ≤ R → R ≤ T.length →
    ∃ T', run masterM (clockSum v D)
        ⟨(1, 0, false, false), 2 * v + 2, T⟩ =
        ⟨(1, 0, false, false), 2, T'⟩ ∧
      RoundInv T' 0 (D - v) ∧
      T'.drop R = T.drop R ∧ T'.length = T.length := by
  intro T D R hv hinv hbound hR
  induction v generalizing T D with
  | zero =>
      refine ⟨T, ?_, by simpa using hinv, rfl, rfl⟩
      simp [clockSum]
  | succ v ih =>
      have hk : 1 ≤ v + 1 := by omega
      have hD : 1 ≤ D := by omega
      let T1 := rsTape (rsTape T (2 * (v + 1) + 4) D)
        (2 * (v + 1)) (D + 1)
      have hrun1 : run masterM (roundClock D)
          ⟨(1, 0, false, false), 2 * (v + 1) + 2, T⟩ =
          ⟨(1, 0, false, false), 2 * v + 2, T1⟩ := by
        simpa [roundClock, T1] using
          roundInv_step T (v + 1) D hk hD hinv
      have hinv1 : RoundInv T1 v (D - 1) := by
        simpa [T1] using roundInv_preserved T (v + 1) D hk hD hinv
      have hpres := roundInv_round_drop T (v + 1) D R hk hD hinv
        hbound hR
      have hT1len : T1.length = T.length := by
        simpa [T1] using hpres.2
      have hT1drop : T1.drop R = T.drop R := by
        simpa [T1] using hpres.1
      obtain ⟨T', hrun2, hinv2, hdrop2, hlen2⟩ :=
        ih T1 (D - 1) (by omega) hinv1 (by omega) (by
          rw [hT1len]
          exact hR)
      refine ⟨T', ?_, ?_, hdrop2.trans hT1drop, hlen2.trans hT1len⟩
      · simp only [clockSum]
        rw [run_add, hrun1]
        exact hrun2
      · simpa [show D - (v + 1) = D - 1 - v by omega] using hinv2

/-- The terminal read performs no writes, so the complete round-start run
retains the same arbitrary trailer. -/
theorem wholeRun_drop (v : Nat) (T : List Bool) (D R : Nat)
    (hv : v ≤ D) (h : RoundInv T v D)
    (hbound : 2 * v + 2 * D + 6 ≤ R) (hR : R ≤ T.length) :
    ∃ T', run masterM (clockSum v D + 7)
        ⟨(1, 0, false, false), 2 * v + 2, T⟩ =
        ⟨(9, 0, T.getD (2 * v + 4 + 2 * v) false, false), 4, T'⟩ ∧
      T'.drop R = T.drop R ∧ T'.length = T.length := by
  obtain ⟨T1, hrun, hinv, hdrop, hlen⟩ :=
    rounds_drop v T D R hv h hbound hR
  have htail : run masterM 7
      ⟨(1, 0, false, false), 2, T1⟩ =
      ⟨(9, 0, T1.getD 4 false, false), 4, T1⟩ := by
    exact tail_read (s := 2) (tape := T1) (by omega)
      (by simpa using hinv.lsent)
  have hrun1 : run masterM (clockSum v D + 7)
      ⟨(1, 0, false, false), 2 * v + 2, T⟩ =
      ⟨(9, 0, T1.getD 4 false, false), 4, T1⟩ := by
    rw [run_add, hrun]
    exact htail
  obtain ⟨T2, hrun2⟩ := wholeRun v T D hv h
  have heq : T2 = T1 := by
    rw [hrun2] at hrun1
    exact congrArg (fun c => c.tp) hrun1
  subst T2
  refine ⟨T1, hrun2, hdrop, hlen⟩

/-- On a canonical literal tape followed by any trailer, the actual complete
`masterM` result retains that trailer at the original literal boundary. -/
theorem masterM_literal_trailer (w : List Bool) (l : Lit)
    (trailer : List Bool) :
    let bits := literalLookupTape w l
    let cf := run masterM (literalLookupClock w l)
      (init masterM (bits ++ trailer))
    cf.tp.drop bits.length = trailer := by
  dsimp only
  let bits := literalLookupTape w l
  let A := signedLookupAssignment w l.1 l.2
  have hv : l.1 ≤ A.length := by
    dsimp [A]
    rw [signedLookupAssignment_length]
    omega
  have hinv : RoundInv (bits ++ trailer) l.1 A.length := by
    dsimp [bits, A]
    exact literalLookupTape_append_roundInv w l trailer
  have hlen : bits.length = 4 * l.1 + 8 := by
    simp [bits, literalLookupTape, CookLevinInP.encode,
      signedLookupAssignment_length,
      PallLean.Paper93.DeepMath.PathB.CookLevinInP.double_length]
    ring
  have hrun := wholeRun_drop l.1 (bits ++ trailer) A.length bits.length
    hv hinv (by
      dsimp [A]
      rw [signedLookupAssignment_length, hlen]
      omega) (by simp)
  obtain ⟨T', hwhole, hdrop, hTlen⟩ := hrun
  have hinit := init_phase (bits ++ trailer) l.1 A.length hinv
  have hfull : run masterM (literalLookupClock w l)
      (init masterM (bits ++ trailer)) =
      ⟨(9, 0, (bits ++ trailer).getD (2 * l.1 + 4 + 2 * l.1) false,
          false), 4, T'⟩ := by
    rw [literalLookupClock, master_forced_init, run_add, hinit]
    exact hwhole
  rw [hfull]
  simpa using hdrop

/-- Exact source-runtime endpoint, now retaining the nested master's tape
rather than hiding it behind the semantic accept theorem. -/
theorem sourceRuntimeLookup_run_shape (d : Nat)
    (preBlocks : List (List Bool)) (w : List Bool) (l : Lit)
    (rest : List (List Bool)) :
    let bits := literalLookupTape w l
    let pre := selectedPrefix d preBlocks
    let trailer := [true, false, false, true] ++
      List.replicate bits.length true ++ selectedTail rest
    let mcf := run masterM (literalLookupClock w l)
      (init masterM (bits ++ trailer))
    run sourceRuntimeLookupCore
        (sourceRuntimeLookupClock d preBlocks w l)
        (init sourceRuntimeLookupCore
          (flattenPairs (progressPairs d [] preBlocks (bits :: rest)))) =
      ⟨Sum.inr mcf.st, pre.length + mcf.hd, pre ++ mcf.tp⟩ := by
  dsimp only
  let bits := literalLookupTape w l
  let pre := selectedPrefix d preBlocks
  let trailer := [true, false, false, true] ++
    List.replicate bits.length true ++ selectedTail rest
  have hcompact := sourceSelectCompact_run d preBlocks bits rest
  have hrew := sourceRewind_literal pre w l
    (List.replicate bits.length true ++ selectedTail rest)
  have hrew' : run sourceRewindMachine (canonicalRewindClock w l)
      ⟨sourceRewindMachine.start, pre.length + bits.length + 3,
        pre ++ bits ++ trailer⟩ =
      ⟨SourceRewindState.done, pre.length, pre ++ bits ++ trailer⟩ := by
    simpa [bits, trailer, List.append_assoc] using hrew
  have hfirst := headSeq_run sourceSelectCompactMachine sourceRewindMachine
    (flattenPairs (progressPairs d [] preBlocks (bits :: rest)))
    (pre ++ bits ++ trailer) (pre ++ bits ++ trailer)
    (sourceSelectCompactClock d preBlocks bits)
    (canonicalRewindClock w l)
    (pre.length + bits.length + 3) pre.length
    (Sum.inr SourceCompactState.done) SourceRewindState.done
    (by simpa [pre, trailer, List.append_assoc] using hcompact)
    rfl hrew' rfl
  let mcf := run masterM (literalLookupClock w l)
    (init masterM (bits ++ trailer))
  have hmaster : run masterM (literalLookupClock w l)
      ⟨masterM.start, pre.length, pre ++ bits ++ trailer⟩ =
      shiftCfg masterM pre mcf := by
    simpa [bits, mcf, List.append_assoc] using
      masterM_run_shifted pre w l trailer
  let A := signedLookupAssignment w l.1 l.2
  have hv : l.1 ≤ A.length := by
    dsimp [A]
    rw [signedLookupAssignment_length]
    omega
  have hinv : RoundInv (bits ++ trailer) l.1 A.length := by
    dsimp [bits, A]
    exact literalLookupTape_append_roundInv w l trailer
  have hmhalt : masterM.halt mcf.st = true := by
    have happ := readAv_promise (bits ++ trailer) l.1 A.length hv hinv
    simpa [mcf, literalLookupClock, A, bits] using happ.1
  have hsecond := headSeqAccept_run sourceSelectCompactRewindMachine masterM
    (flattenPairs (progressPairs d [] preBlocks (bits :: rest)))
    (pre ++ bits ++ trailer) (pre ++ mcf.tp)
    (sourceSelectCompactClock d preBlocks bits + 1 +
      canonicalRewindClock w l)
    (literalLookupClock w l) pre.length (pre.length + mcf.hd)
    (Sum.inr SourceRewindState.done) mcf.st hfirst rfl
    (by simpa [shiftCfg] using hmaster) hmhalt
  simpa [sourceRuntimeLookupCore, sourceRuntimeLookupClock, bits,
    Nat.add_assoc] using hsecond

/-- The complete fixed runtime lookup leaves its four-cell compaction trailer,
padding, and every later fresh source block exactly unchanged. -/
theorem sourceRuntimeLookup_trailer (d : Nat)
    (preBlocks : List (List Bool)) (w : List Bool) (l : Lit)
    (rest : List (List Bool)) :
    let bits := literalLookupTape w l
    let pre := selectedPrefix d preBlocks
    let trailer := [true, false, false, true] ++
      List.replicate bits.length true ++ selectedTail rest
    let cf := run sourceRuntimeLookupCore
      (sourceRuntimeLookupClock d preBlocks w l)
      (init sourceRuntimeLookupCore
        (flattenPairs (progressPairs d [] preBlocks (bits :: rest))))
    cf.tp.drop (pre.length + bits.length) = trailer := by
  dsimp only
  let bits := literalLookupTape w l
  let pre := selectedPrefix d preBlocks
  let trailer := [true, false, false, true] ++
    List.replicate bits.length true ++ selectedTail rest
  let mcf := run masterM (literalLookupClock w l)
    (init masterM (bits ++ trailer))
  have hrun := sourceRuntimeLookup_run_shape d preBlocks w l rest
  have htail := masterM_literal_trailer w l trailer
  rw [show run sourceRuntimeLookupCore
      (sourceRuntimeLookupClock d preBlocks w l)
      (init sourceRuntimeLookupCore
        (flattenPairs (progressPairs d [] preBlocks (bits :: rest)))) =
      ⟨Sum.inr mcf.st, pre.length + mcf.hd, pre ++ mcf.tp⟩ by
        simpa [bits, pre, trailer, mcf] using hrun]
  simp only [Cfg.tp]
  rw [← List.drop_drop, List.drop_left]
  simpa [bits, trailer, mcf] using htail

/-- After the complete physical cashout, dropping the fixed output footprint,
the evolved selected prefix, the original literal footprint, the four-cell
trailer, and its equal-length padding lands exactly on the untouched future
archive.  No bulk copy is required for progression. -/
theorem scheduledRuntimeRelativeOutput_futureArchive
    (x w : List Bool) {t : Nat}
    (ht : t < (decodedLiterals x).length) :
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
    rcf.tp.drop (2 * B + 2 + pre.length +
      2 * bits.length + 4) = selectedTail rest := by
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
  let cf := run sourceRuntimeLookupCore n (init sourceRuntimeLookupCore T)
  have hshape : T =
      flattenPairs (progressPairs (B - t) [] preBlocks (bits :: rest)) := by
    have hget : schedule.getD t [] = bits := by
      dsimp [schedule, bits, l]
      exact literalTapeSchedule_getD x w ht
    have hslen : schedule.length = B := by
      simp [schedule, B, literalTapeSchedule]
    have hts : t < schedule.length := by simpa [hslen] using ht
    have hbit : schedule[t] = bits := by
      rw [← hget, List.getD_eq_getElem schedule [] hts]
    have hsplit : schedule = preBlocks ++ bits :: rest := by
      dsimp [preBlocks, rest]
      conv_lhs => rw [← List.take_append_drop t schedule]
      rw [List.drop_eq_getElem_cons hts, hbit]
    have hprelen : preBlocks.length = t := by
      dsimp [preBlocks]
      rw [List.length_take, Nat.min_eq_left hts.le]
    dsimp [T]
    rw [sourceSelectorInput, progressPairs, sourceArchive, hsplit]
    simp [hprelen, List.append_assoc]
  have hcore : cf.tp.drop (pre.length + bits.length) =
      [true, false, false, true] ++ List.replicate bits.length true ++
        selectedTail rest := by
    dsimp [cf, n]
    rw [hshape]
    simpa [bits, pre] using sourceRuntimeLookup_trailer
      (B - t) preBlocks w l rest
  have hroute := scheduledRuntimeRelativeOutputSourceRoute x w ht
  have houtlen : out.length ≤ B := by
    have : out.length = t := by
      dsimp [out]
      rw [List.length_take, scheduledTruths_length,
        Nat.min_eq_left (by simpa [B] using ht.le)]
    omega
  have hcap : (outputCap B
      (out ++ [evalLit (fun k => w.getD k false) l])).length = 2 * B + 2 := by
    apply outputCap_length
    simp only [List.length_append, List.length_singleton]
    have : out.length = t := by
      dsimp [out]
      rw [List.length_take, scheduledTruths_length,
        Nat.min_eq_left (by simpa [B] using ht.le)]
    omega
  have htp : (run (acceptRouteMachine (runtimeRelativeOutputSourceMachine B))
      (runtimeRelativeOutputRouteClock B out T n)
      (init (acceptRouteMachine (runtimeRelativeOutputSourceMachine B))
        (outputCap B out ++ T))).tp =
      outputCap B
        (out ++ [evalLit (fun k => w.getD k false) l]) ++ cf.tp := by
    simpa [B, schedule, preBlocks, l, out, T, n, cf] using hroute.2
  rw [htp]
  rw [show 2 * B + 2 + pre.length + 2 * bits.length + 4 =
      (2 * B + 2) + ((pre.length + bits.length) +
        (4 + bits.length)) by omega]
  rw [← List.drop_drop, ← hcap, List.drop_left]
  rw [← List.drop_drop, hcore]
  change List.drop (4 + bits.length)
    ([true, false, false, true] ++ List.replicate bits.length true ++
      selectedTail rest) = selectedTail rest
  rw [show 4 + bits.length =
      4 + (List.replicate bits.length true).length by simp]
  rw [← List.drop_drop]
  simp

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeTailPreservation

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeTailPreservation.rsTape_drop_of_le
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeTailPreservation.rounds_drop
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeTailPreservation.masterM_literal_trailer
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeTailPreservation.sourceRuntimeLookup_trailer
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeTailPreservation.scheduledRuntimeRelativeOutput_futureArchive
