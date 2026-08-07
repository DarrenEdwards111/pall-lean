import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeRoundEntryLocator

/-!
# Reset-aware physical next-round entry adapter

The unary rebaser halts at the far end of the restored archive.  The ordinary
`seqMachine` handoff supplies the one physical reset required by the next
round: it resets to tape cell zero and starts the fixed doubled-marker locator.
The locator then traverses the aligned reachable corridor and halts on the
first cell of the canonical rebased selector.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundEntryAdapter

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSeq
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLiteralWeld
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupDynamicRoute
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupOutputCapacity
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRepeatController
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupScheduleBound
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeStage
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceCompact
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceLookup
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRelativeOutput
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeOutputSourceLocator
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeArchiveReturnWriter
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeUnaryRebaseWriter
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalUnaryRebase
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundEntryLocator

/-! ## Structural grammar bricks -/

def runtimeOutputCapPairs (B : Nat) (out : List Bool) :
    List (Bool × Bool) :=
  dataPairs out ++ [(false, true)] ++
    List.replicate (B - out.length) (false, false)

theorem runtimeEntryPrev_append (previous : Bool)
    (xs ys : List (Bool × Bool)) :
    runtimeEntryPrev previous (xs ++ ys) =
      runtimeEntryPrev (runtimeEntryPrev previous xs) ys := by
  induction xs generalizing previous with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.cons_append, runtimeEntryPrev]
      exact ih (runtimePairIsSep x)

theorem runtimeNoDoubleSepFrom_append (previous : Bool)
    (xs ys : List (Bool × Bool)) :
    RuntimeNoDoubleSepFrom previous (xs ++ ys) ↔
      RuntimeNoDoubleSepFrom previous xs ∧
        RuntimeNoDoubleSepFrom (runtimeEntryPrev previous xs) ys := by
  induction xs generalizing previous with
  | nil => simp [RuntimeNoDoubleSepFrom, runtimeEntryPrev]
  | cons x xs ih =>
      simp only [List.cons_append, RuntimeNoDoubleSepFrom, runtimeEntryPrev]
      rw [ih]
      tauto

theorem runtimeEntry_dataPairs_safe (bits : List Bool) :
    RuntimeNoDoubleSepFrom false (dataPairs bits) ∧
      runtimeEntryPrev false (dataPairs bits) = false := by
  induction bits with
  | nil => simp [dataPairs, RuntimeNoDoubleSepFrom, runtimeEntryPrev]
  | cons b bits ih =>
      cases b <;>
        simp_all [dataPairs, RuntimeNoDoubleSepFrom, runtimeEntryPrev,
          runtimePairIsSep]

theorem runtimeEntry_zeroPairs_safe (previous : Bool) (n : Nat) :
    RuntimeNoDoubleSepFrom previous
        (List.replicate n (false, false)) ∧
      runtimeEntryPrev previous (List.replicate n (false, false)) =
        if n = 0 then previous else false := by
  induction n generalizing previous with
  | zero => simp [RuntimeNoDoubleSepFrom, runtimeEntryPrev]
  | succ n ih =>
      rw [List.replicate_succ]
      simp only [RuntimeNoDoubleSepFrom, runtimeEntryPrev, runtimePairIsSep,
        Bool.not_false]
      simpa using ih false

theorem runtimeEntry_truePairs_safe (previous : Bool) (n : Nat) :
    RuntimeNoDoubleSepFrom previous
        (List.replicate n (true, true)) ∧
      runtimeEntryPrev previous (List.replicate n (true, true)) =
        if n = 0 then previous else false := by
  induction n generalizing previous with
  | zero => simp [RuntimeNoDoubleSepFrom, runtimeEntryPrev]
  | succ n ih =>
      rw [List.replicate_succ]
      simp only [RuntimeNoDoubleSepFrom, runtimeEntryPrev, runtimePairIsSep,
        Bool.not_true, Bool.false_and, Bool.false_eq_true, and_false,
        not_false_eq_true, true_and]
      simpa using ih false

theorem runtimePassedSourceBlock_safe (previous : Bool)
    (bits : List Bool) :
    RuntimeNoDoubleSepFrom previous (passedSourceBlock bits) ∧
      runtimeEntryPrev previous (passedSourceBlock bits) = true := by
  obtain ⟨hdata, hdataEnd⟩ := runtimeEntry_dataPairs_safe bits
  have hhead : RuntimeNoDoubleSepFrom previous [(true, true)] ∧
      runtimeEntryPrev previous [(true, true)] = false := by
    cases previous <;>
      simp [RuntimeNoDoubleSepFrom, runtimeEntryPrev, runtimePairIsSep]
  have hbody : RuntimeNoDoubleSepFrom false
        (dataPairs bits ++ [(false, true)]) ∧
      runtimeEntryPrev false (dataPairs bits ++ [(false, true)]) = true := by
    rw [runtimeNoDoubleSepFrom_append, runtimeEntryPrev_append, hdataEnd]
    simpa [RuntimeNoDoubleSepFrom, runtimeEntryPrev, runtimePairIsSep]
      using hdata
  simpa [passedSourceBlock, List.append_assoc] using
    And.intro
      ((runtimeNoDoubleSepFrom_append previous [(true, true)]
        (dataPairs bits ++ [(false, true)])).2 ⟨hhead.1, by
          simpa [hhead.2] using hbody.1⟩)
      (by
        simp only [runtimeEntryPrev, runtimePairIsSep, Bool.not_true,
          Bool.false_and]
        exact hbody.2)

theorem runtimePassedBlocks_safe (previous : Bool)
    (blocks : List (List Bool)) :
    RuntimeNoDoubleSepFrom previous (blocks.flatMap passedSourceBlock) ∧
      runtimeEntryPrev previous (blocks.flatMap passedSourceBlock) =
        if blocks = [] then previous else true := by
  induction blocks generalizing previous with
  | nil => simp [RuntimeNoDoubleSepFrom, runtimeEntryPrev]
  | cons bits blocks ih =>
      have hb := runtimePassedSourceBlock_safe previous bits
      have ht := ih true
      simp only [List.flatMap_cons]
      constructor
      · rw [runtimeNoDoubleSepFrom_append, hb.2]
        exact ⟨hb.1, ht.1⟩
      · rw [runtimeEntryPrev_append, hb.2, ht.2]
        split <;> simp_all

/-- The complete consumed-source prefix has only isolated `01` tokens.  It
always ends at its final passed-block boundary (or at the count boundary when
there are no passed blocks). -/
theorem runtimeSelectedPrefixPairs_safe (d : Nat)
    (preBlocks : List (List Bool)) :
    RuntimeNoDoubleSepFrom false (selectedPrefixPairs d preBlocks) ∧
      runtimeEntryPrev false (selectedPrefixPairs d preBlocks) = true := by
  let n := preBlocks.length + d
  have hcnt := runtimeEntry_truePairs_safe false n
  have hcntEnd : runtimeEntryPrev false
      (List.replicate n (true, true)) = false := by
    by_cases hn : n = 0
    · simp [hn, runtimeEntryPrev]
    · simpa [hn] using hcnt.2
  have hsep : RuntimeNoDoubleSepFrom false [(false, true)] ∧
      runtimeEntryPrev false [(false, true)] = true := by
    simp [RuntimeNoDoubleSepFrom, runtimeEntryPrev, runtimePairIsSep]
  have hblocks := runtimePassedBlocks_safe true preBlocks
  have hleft : RuntimeNoDoubleSepFrom false
        (List.replicate n (true, true) ++ [(false, true)]) ∧
      runtimeEntryPrev false
        (List.replicate n (true, true) ++ [(false, true)]) = true := by
    constructor
    · rw [runtimeNoDoubleSepFrom_append, hcntEnd]
      exact ⟨hcnt.1, hsep.1⟩
    · rw [runtimeEntryPrev_append, hcntEnd]
      exact hsep.2
  have hall : RuntimeNoDoubleSepFrom false
      ((List.replicate n (true, true) ++ [(false, true)]) ++
        preBlocks.flatMap passedSourceBlock) := by
    rw [runtimeNoDoubleSepFrom_append, hleft.2]
    exact ⟨hleft.1, hblocks.1⟩
  have hend : runtimeEntryPrev false
      ((List.replicate n (true, true) ++ [(false, true)]) ++
        preBlocks.flatMap passedSourceBlock) = true := by
    rw [runtimeEntryPrev_append, hleft.2, hblocks.2]
    split <;> simp_all
  have hshape : selectedPrefixPairs d preBlocks =
      (List.replicate n (true, true) ++ [(false, true)]) ++
        preBlocks.flatMap passedSourceBlock := by
    dsimp [selectedPrefixPairs, n]
    rw [← List.replicate_add]
  rw [hshape]
  exact ⟨hall, hend⟩

theorem flattenPairs_replicate_ff (n : Nat) :
    flattenPairs (List.replicate n (false, false)) =
      List.replicate (2 * n) false := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ]
      simp only [flattenPairs, ih]
      rw [show 2 * (n + 1) = 2 + 2 * n by omega]
      simp [List.replicate_add]

theorem runtimeOutputCapPairs_flatten (B : Nat) (out : List Bool) :
    flattenPairs (runtimeOutputCapPairs B out) = outputCap B out := by
  rw [runtimeOutputCapPairs, flattenPairs_append,
    flattenPairs_dataPairs, flattenPairs_replicate_ff]
  rfl

/-- A non-full output capacity is an isolated-separator grammar and ends in
`00`.  Nonterminal rounds always have this strict-capacity condition. -/
theorem runtimeOutputCapPairs_safe (B : Nat) (out : List Bool)
    (hout : out.length < B) :
    RuntimeNoDoubleSepFrom false (runtimeOutputCapPairs B out) ∧
      runtimeEntryPrev false (runtimeOutputCapPairs B out) = false := by
  obtain ⟨hdata, hdataEnd⟩ := runtimeEntry_dataPairs_safe out
  have hz := runtimeEntry_zeroPairs_safe true (B - out.length)
  have hpos : B - out.length ≠ 0 := by omega
  have hterm : RuntimeNoDoubleSepFrom false
        (dataPairs out ++ [(false, true)]) ∧
      runtimeEntryPrev false (dataPairs out ++ [(false, true)]) = true := by
    rw [runtimeNoDoubleSepFrom_append, runtimeEntryPrev_append,
      hdataEnd]
    simpa [RuntimeNoDoubleSepFrom, runtimeEntryPrev, runtimePairIsSep]
      using hdata
  have hall : RuntimeNoDoubleSepFrom false
      ((dataPairs out ++ [(false, true)]) ++
        List.replicate (B - out.length) (false, false)) := by
    rw [runtimeNoDoubleSepFrom_append, hterm.2]
    exact ⟨hterm.1, hz.1⟩
  have hend : runtimeEntryPrev false
      ((dataPairs out ++ [(false, true)]) ++
        List.replicate (B - out.length) (false, false)) = false := by
    rw [runtimeEntryPrev_append, hterm.2]
    simpa [hpos] using hz.2
  simpa [runtimeOutputCapPairs, List.append_assoc] using And.intro hall hend

/-- The real nonterminal output capacity joins safely to the complete evolved
selected prefix: the reserved zero capacity pair separates the output's `01`
terminator from the selector grammar. -/
theorem runtimeOutputSelectedPairs_safe (B : Nat) (out : List Bool)
    (d : Nat) (preBlocks : List (List Bool)) (hout : out.length < B) :
    RuntimeNoDoubleSepFrom false
        (runtimeOutputCapPairs B out ++ selectedPrefixPairs d preBlocks) ∧
      runtimeEntryPrev false
        (runtimeOutputCapPairs B out ++ selectedPrefixPairs d preBlocks) =
          true := by
  have ho := runtimeOutputCapPairs_safe B out hout
  have hs := runtimeSelectedPrefixPairs_safe d preBlocks
  constructor
  · rw [runtimeNoDoubleSepFrom_append, ho.2]
    exact ⟨ho.1, hs.1⟩
  · rw [runtimeEntryPrev_append, ho.2]
    exact hs.2

def runtimeWorkspaceFrontPairs (value : Bool) (m n : Nat) :
    List (Bool × Bool) :=
  [(true, false), (false, true), (value, value)] ++
    List.replicate m (true, false) ++ [(false, true)] ++
    List.replicate n (true, true)

theorem runtimeEntry_rendPairs_safe (previous : Bool) (n : Nat) :
    RuntimeNoDoubleSepFrom previous
        (List.replicate n (true, false)) ∧
      runtimeEntryPrev previous (List.replicate n (true, false)) =
        if n = 0 then previous else false := by
  induction n generalizing previous with
  | zero => simp [RuntimeNoDoubleSepFrom, runtimeEntryPrev]
  | succ n ih =>
      rw [List.replicate_succ]
      simp only [RuntimeNoDoubleSepFrom, runtimeEntryPrev, runtimePairIsSep,
        Bool.not_true, Bool.false_and, Bool.false_eq_true, and_false,
        not_false_eq_true, true_and]
      simpa using ih false

/-- Pair grammar proved independently of semantic offsets for the entire
reachable completed-workspace front: `10 01 dd 10* 01 11*`.  It safely
follows the selected prefix's final ordinary separator and, because the live
padding is nonempty, ends in a nonseparator pair before the reserved marker. -/
theorem runtimeWorkspaceFrontPairs_safe (value : Bool) (m n : Nat)
    (hn : 0 < n) :
    RuntimeNoDoubleSepFrom true (runtimeWorkspaceFrontPairs value m n) ∧
      runtimeEntryPrev true (runtimeWorkspaceFrontPairs value m n) = false := by
  have hboot : RuntimeNoDoubleSepFrom true
        [(true, false), (false, true), (value, value)] ∧
      runtimeEntryPrev true
        [(true, false), (false, true), (value, value)] = false := by
    cases value <;>
      simp [RuntimeNoDoubleSepFrom, runtimeEntryPrev, runtimePairIsSep]
  have hrend := runtimeEntry_rendPairs_safe false m
  have hrendEnd : runtimeEntryPrev false
      (List.replicate m (true, false)) = false := by
    by_cases hm : m = 0
    · simp [hm, runtimeEntryPrev]
    · simpa [hm] using hrend.2
  have hboundary : RuntimeNoDoubleSepFrom false [(false, true)] ∧
      runtimeEntryPrev false [(false, true)] = true := by
    simp [RuntimeNoDoubleSepFrom, runtimeEntryPrev, runtimePairIsSep]
  have hpad := runtimeEntry_truePairs_safe true n
  have hpadEnd : runtimeEntryPrev true
      (List.replicate n (true, true)) = false := by
    simpa [show n ≠ 0 by omega] using hpad.2
  let left := [(true, false), (false, true), (value, value)] ++
    List.replicate m (true, false)
  have hleft : RuntimeNoDoubleSepFrom true left ∧
      runtimeEntryPrev true left = false := by
    have hs : RuntimeNoDoubleSepFrom true
        ([(true, false), (false, true), (value, value)] ++
          List.replicate m (true, false)) :=
      (runtimeNoDoubleSepFrom_append true
        [(true, false), (false, true), (value, value)]
        (List.replicate m (true, false))).2 ⟨hboot.1, by
          simpa [hboot.2] using hrend.1⟩
    have he : runtimeEntryPrev true
        ([(true, false), (false, true), (value, value)] ++
          List.replicate m (true, false)) = false := by
      rw [runtimeEntryPrev_append, hboot.2]
      exact hrendEnd
    exact ⟨by simpa [left] using hs, by simpa [left] using he⟩
  let mid := left ++ [(false, true)]
  have hmid : RuntimeNoDoubleSepFrom true mid ∧
      runtimeEntryPrev true mid = true := by
    dsimp [mid]
    constructor
    · rw [runtimeNoDoubleSepFrom_append, hleft.2]
      exact ⟨hleft.1, hboundary.1⟩
    · rw [runtimeEntryPrev_append, hleft.2]
      exact hboundary.2
  have hall : RuntimeNoDoubleSepFrom true
      (mid ++ List.replicate n (true, true)) := by
    rw [runtimeNoDoubleSepFrom_append, hmid.2]
    exact ⟨hmid.1, hpad.1⟩
  have hend : runtimeEntryPrev true
      (mid ++ List.replicate n (true, true)) = false := by
    rw [runtimeEntryPrev_append, hmid.2]
    exact hpadEnd
  simpa [runtimeWorkspaceFrontPairs, left, mid, List.append_assoc] using
    And.intro hall hend

/-- The complete physical nonterminal body followed by its reset-to-origin
entry scan.  Both components are fixed machines. -/
def outputWorkspaceArchiveReturnUnaryRebaseEntryMachine : Machine :=
  seqMachine outputWorkspaceArchiveReturnUnaryRebaseMachine
    runtimeRoundEntryLocatorMachine

def outputWorkspaceArchiveReturnUnaryRebaseEntryDone :
    outputWorkspaceArchiveReturnUnaryRebaseEntryMachine.State := by
  unfold outputWorkspaceArchiveReturnUnaryRebaseEntryMachine
  exact Sum.inr RuntimeRoundEntryState.done

/-- Generic exact reset-and-locate composition.  The left run may finish at
any head: the `seqMachine` handoff resets physically to zero before the fixed
locator begins. -/
theorem unaryRebaseEntry_run
    (T0 : List Bool) (pairs : List (Bool × Bool)) (tail : List Bool)
    (leftClock leftHead : Nat)
    (hsafe : RuntimeNoDoubleSepFrom false pairs)
    (tailLo tailHi : Bool)
    (htail : tail = tailLo :: tailHi :: tail.drop 2)
    (hnonsep : runtimePairIsSep (tailLo, tailHi) = false)
    (hleft : run outputWorkspaceArchiveReturnUnaryRebaseMachine leftClock
        (init outputWorkspaceArchiveReturnUnaryRebaseMachine T0) =
      ⟨outputWorkspaceArchiveReturnUnaryRebaseDone, leftHead,
        flattenPairs pairs ++ [false, true, false, true] ++ tail⟩) :
    run outputWorkspaceArchiveReturnUnaryRebaseEntryMachine
        (leftClock + 1 + (2 * pairs.length + 7))
        (init outputWorkspaceArchiveReturnUnaryRebaseEntryMachine T0) =
      ⟨outputWorkspaceArchiveReturnUnaryRebaseEntryDone,
        2 * pairs.length + 4,
        flattenPairs pairs ++ [false, true, false, true] ++ tail⟩ := by
  have hright := runtimeRoundEntryLocator_run pairs tail tailLo tailHi
    hsafe htail hnonsep
  have hleftHalt : outputWorkspaceArchiveReturnUnaryRebaseMachine.halt
      outputWorkspaceArchiveReturnUnaryRebaseDone = true := by
    rfl
  have hrightHalt : runtimeRoundEntryLocatorMachine.halt
      RuntimeRoundEntryState.done = true := by
    rfl
  have hjoin := seq_run outputWorkspaceArchiveReturnUnaryRebaseMachine
    runtimeRoundEntryLocatorMachine T0
    (flattenPairs pairs ++ [false, true, false, true] ++ tail)
    (flattenPairs pairs ++ [false, true, false, true] ++ tail)
    leftClock (2 * pairs.length + 7)
    outputWorkspaceArchiveReturnUnaryRebaseDone leftHead
    RuntimeRoundEntryState.done (2 * pairs.length + 4)
    hleft hleftHalt (by
      simpa [flattenPairs, List.append_assoc] using hright) hrightHalt
  simpa [outputWorkspaceArchiveReturnUnaryRebaseEntryMachine,
    outputWorkspaceArchiveReturnUnaryRebaseEntryDone] using hjoin

set_option maxHeartbeats 1000000 in
theorem scheduledRuntimeRelativeOutput_physicalUnaryRebaseEntry
    (x w : List Bool) {t : Nat}
    (ht : t < (decodedLiterals x).length)
    (htnext : t + 1 < (decodedLiterals x).length)
    (hgrammar : ∀ (residue : List Bool),
      ∃ pairs : List (Bool × Bool),
        outputCap (decodedLiterals x).length
            ((scheduledTruths x w).take (t + 1)) ++ residue =
            flattenPairs pairs ∧
        RuntimeNoDoubleSepFrom false pairs) :
    let B := (decodedLiterals x).length
    let schedule := literalTapeSchedule x w
    let preBlocks := schedule.take t
    let l := scheduledLiteral x t
    let rest := schedule.drop (t + 1)
    let pre := selectedPrefix (B - t) preBlocks
    let out := (scheduledTruths x w).take t
    let out' := (scheduledTruths x w).take (t + 1)
    let T := sourceSelectorInput B t schedule
    let lookupClock := sourceRuntimeLookupClock (B - t) preBlocks w l
    let M := runtimeRelativeOutputSourceMachine B
    let routeClock := runtimeRelativeOutputRouteClock B out T lookupClock
    let rcf := run (acceptRouteMachine M) routeClock
      (init (acceptRouteMachine M) (outputCap B out ++ T))
    let locateClock := outputSourceLocatorClock B out' + 1 +
      (pre.length + 2)
    let tailClock := 8 * l.1 + 22
    let prefixClock := locateClock + 1 + tailClock
    let seedClock := runtimeArchiveReturnSeedClock rest
    ∃ residue unaryClock pairs,
      outputCap B out' ++ residue = flattenPairs pairs ∧
      run outputWorkspaceArchiveReturnUnaryRebaseEntryMachine
          (((prefixClock + 1 + seedClock) + 1 + unaryClock) + 1 +
            (2 * pairs.length + 7))
          (init outputWorkspaceArchiveReturnUnaryRebaseEntryMachine rcf.tp) =
        ⟨outputWorkspaceArchiveReturnUnaryRebaseEntryDone,
          2 * pairs.length + 4,
          outputCap B out' ++ residue ++ [false, true, false, true] ++
            sourceSelectorInput rest.length 0 rest⟩ := by
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
  let lookupClock := sourceRuntimeLookupClock (B - t) preBlocks w l
  let M := runtimeRelativeOutputSourceMachine B
  let routeClock := runtimeRelativeOutputRouteClock B out T lookupClock
  let rcf := run (acceptRouteMachine M) routeClock
    (init (acceptRouteMachine M) (outputCap B out ++ T))
  let locateClock := outputSourceLocatorClock B out' + 1 +
    (pre.length + 2)
  let tailClock := 8 * l.1 + 22
  let prefixClock := locateClock + 1 + tailClock
  let seedClock := runtimeArchiveReturnSeedClock rest
  let R := 2 * B + 2 + pre.length + 2 * bits.length + 4
  obtain ⟨residue, unaryClock, hleft⟩ :=
    scheduledRuntimeRelativeOutput_physicalUnaryRebase x w ht htnext
  obtain ⟨pairs, hpairs, hsafe⟩ := hgrammar residue
  have hleft' : run outputWorkspaceArchiveReturnUnaryRebaseMachine
      ((prefixClock + 1 + seedClock) + 1 + unaryClock)
      (init outputWorkspaceArchiveReturnUnaryRebaseMachine rcf.tp) =
    ⟨outputWorkspaceArchiveReturnUnaryRebaseDone,
      R + (selectedTail rest).length,
      flattenPairs pairs ++ [false, true, false, true] ++
        sourceSelectorInput rest.length 0 rest⟩ := by
    rw [← hpairs]
    simpa [B, schedule, preBlocks, l, bits, rest, pre, out, out', T,
      lookupClock, M, routeClock, rcf, locateClock, tailClock,
      prefixClock, seedClock, R, List.append_assoc] using hleft
  have hrestlen : rest.length = B - (t + 1) := by
    have hslen : schedule.length = B := by
      simp [schedule, B, literalTapeSchedule]
    simp [rest, hslen]
  have hrestpos : 0 < rest.length := by
    rw [hrestlen]
    omega
  obtain ⟨selectorCount, hselectorCount⟩ :=
    Nat.exists_eq_succ_of_ne_zero (by omega : rest.length ≠ 0)
  have hselectorHead : sourceSelectorInput rest.length 0 rest =
      true :: true :: (sourceSelectorInput rest.length 0 rest).drop 2 := by
    rw [hselectorCount]
    simp [sourceSelectorInput, List.replicate_succ, flattenPairs,
      List.append_assoc]
  have hrun := unaryRebaseEntry_run rcf.tp pairs
    (sourceSelectorInput rest.length 0 rest)
    ((prefixClock + 1 + seedClock) + 1 + unaryClock)
    (R + (selectedTail rest).length) hsafe true true hselectorHead
    (by simp [runtimePairIsSep]) hleft'
  refine ⟨residue, unaryClock, pairs, hpairs, ?_⟩
  simpa [B, schedule, preBlocks, l, bits, rest, pre, out, out', T,
    lookupClock, M, routeClock, rcf, locateClock, tailClock,
    prefixClock, seedClock, R, hpairs, List.append_assoc] using hrun

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundEntryAdapter

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundEntryAdapter.unaryRebaseEntry_run
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundEntryAdapter.scheduledRuntimeRelativeOutput_physicalUnaryRebaseEntry
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundEntryAdapter.runtimeOutputCapPairs_safe
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundEntryAdapter.runtimeSelectedPrefixPairs_safe
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundEntryAdapter.runtimeWorkspaceFrontPairs_safe
