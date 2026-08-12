import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeProgressReturn

/-!
# Fixed progress-record clearer

For a `k`-pair workspace followed by the reserved two-pair marker, the
controller writes the length-preserving outer-loop layout

`01 · 10^k · 00`.

The first workspace pair becomes the permanent sentinel, the remaining
workspace pairs and first marker pair become ordinary progress words, and
the second marker pair is the initial hole.  No counter is kept in control.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeProgressRecordClear

set_option maxHeartbeats 4000000

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundEntryAdapter
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePreservedPassedCopy
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryTerminal

inductive RuntimeProgressRecordClearState
  | firstLo | firstHi (loBit : Bool)
  | lo | hi (loBit : Bool)
  | candidateLo | candidateHi (loBit : Bool)
  | rewriteCandidateLo | advanceCandidate
  | backOne | backTwo | done
  deriving DecidableEq, Fintype

/-- Fixed destructive scanner which emits the progress protocol while using
the same double-zero recognition rule as the certified locator. -/
def runtimeProgressRecordClearMachine : Machine where
  State := RuntimeProgressRecordClearState
  fin := inferInstance
  dec := inferInstance
  start := .firstLo
  halt := fun s => decide (s = .done)
  δ := fun s b =>
    match s with
    | .firstLo => (.firstHi b, some false, 1)
    | .firstHi loBit =>
        if !loBit && !b then (.candidateLo, some true, 1)
        else (.lo, some true, 1)
    | .lo => (.hi b, some true, 1)
    | .hi loBit =>
        if !loBit && !b then (.candidateLo, some false, 1)
        else (.lo, some false, 1)
    | .candidateLo => (.candidateHi b, some false, 1)
    | .candidateHi loBit =>
        if !loBit && !b then (.backOne, some false, 0)
        else (.rewriteCandidateLo, some false, 0)
    | .rewriteCandidateLo => (.advanceCandidate, some true, 1)
    | .advanceCandidate => (.lo, none, 1)
    | .backOne => (.backTwo, none, 2)
    | .backTwo => (.done, none, 2)
    | .done => (.done, none, 2)
  accept := fun _ => false

private theorem record_write (pre tail : List Bool) (old new : Bool) :
    writeAt (pre ++ old :: tail) pre.length new =
      pre ++ new :: tail := by
  rw [PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr.writeAt_of_lt
    new (by simp)]
  simp

private theorem record_firstLo_step (T T' : List Bool) (p : Nat) (b : Bool)
    (hr : T[p]?.getD false = b) (hw : writeAt T p false = T') :
    step runtimeProgressRecordClearMachine
        ⟨RuntimeProgressRecordClearState.firstLo, p, T⟩ =
      ⟨RuntimeProgressRecordClearState.firstHi b, p + 1, T'⟩ := by
  simp [step, runtimeProgressRecordClearMachine, moveHead, hr, hw]

private theorem record_firstHi_step (T T' : List Bool) (p : Nat)
    (lo hi : Bool) (hr : T[p]?.getD false = hi)
    (hw : writeAt T p true = T') (hnz : lo = true ∨ hi = true) :
    step runtimeProgressRecordClearMachine
        ⟨RuntimeProgressRecordClearState.firstHi lo, p, T⟩ =
      ⟨RuntimeProgressRecordClearState.lo, p + 1, T'⟩ := by
  cases lo <;> cases hi <;>
    simp_all [step, runtimeProgressRecordClearMachine, moveHead]

private theorem record_lo_step (T T' : List Bool) (p : Nat) (b : Bool)
    (hr : T[p]?.getD false = b) (hw : writeAt T p true = T') :
    step runtimeProgressRecordClearMachine
        ⟨RuntimeProgressRecordClearState.lo, p, T⟩ =
      ⟨RuntimeProgressRecordClearState.hi b, p + 1, T'⟩ := by
  simp [step, runtimeProgressRecordClearMachine, moveHead, hr, hw]

private theorem record_hi_nonzero_step (T T' : List Bool) (p : Nat)
    (lo hi : Bool) (hr : T[p]?.getD false = hi)
    (hw : writeAt T p false = T') (hnz : lo = true ∨ hi = true) :
    step runtimeProgressRecordClearMachine
        ⟨RuntimeProgressRecordClearState.hi lo, p, T⟩ =
      ⟨RuntimeProgressRecordClearState.lo, p + 1, T'⟩ := by
  cases lo <;> cases hi <;>
    simp_all [step, runtimeProgressRecordClearMachine, moveHead]

private theorem record_hi_zero_step (T T' : List Bool) (p : Nat)
    (hr : T[p]?.getD false = false) (hw : writeAt T p false = T') :
    step runtimeProgressRecordClearMachine
        ⟨RuntimeProgressRecordClearState.hi false, p, T⟩ =
      ⟨RuntimeProgressRecordClearState.candidateLo, p + 1, T'⟩ := by
  simp [step, runtimeProgressRecordClearMachine, moveHead, hr, hw]

private theorem record_candidateLo_step (T T' : List Bool) (p : Nat)
    (b : Bool) (hr : T[p]?.getD false = b)
    (hw : writeAt T p false = T') :
    step runtimeProgressRecordClearMachine
        ⟨RuntimeProgressRecordClearState.candidateLo, p, T⟩ =
      ⟨RuntimeProgressRecordClearState.candidateHi b, p + 1, T'⟩ := by
  simp [step, runtimeProgressRecordClearMachine, moveHead, hr, hw]

private theorem record_candidateHi_zero_step (T T' : List Bool) (p : Nat)
    (hr : T[p + 3]?.getD false = false)
    (hw : writeAt T (p + 3) false = T') :
    step runtimeProgressRecordClearMachine
        ⟨RuntimeProgressRecordClearState.candidateHi false, p + 3, T⟩ =
      ⟨RuntimeProgressRecordClearState.backOne, p + 2, T'⟩ := by
  simp [step, runtimeProgressRecordClearMachine, moveHead, hr, hw]

private theorem record_candidateHi_nonzero_step (T T' : List Bool) (p : Nat)
    (lo hi : Bool) (hr : T[p]?.getD false = hi)
    (hw : writeAt T p false = T') (hnz : lo = true ∨ hi = true) :
    step runtimeProgressRecordClearMachine
        ⟨RuntimeProgressRecordClearState.candidateHi lo, p, T⟩ =
      ⟨RuntimeProgressRecordClearState.rewriteCandidateLo, p - 1, T'⟩ := by
  cases lo <;> cases hi <;>
    simp_all [step, runtimeProgressRecordClearMachine, moveHead]

private theorem record_rewriteCandidateLo_step (T T' : List Bool) (p : Nat)
    (b : Bool) (hr : T[p]?.getD false = b)
    (hw : writeAt T p true = T') :
    step runtimeProgressRecordClearMachine
        ⟨RuntimeProgressRecordClearState.rewriteCandidateLo, p, T⟩ =
      ⟨RuntimeProgressRecordClearState.advanceCandidate, p + 1, T'⟩ := by
  simp [step, runtimeProgressRecordClearMachine, moveHead, hr, hw]

private theorem record_advanceCandidate_step (T : List Bool) (p : Nat) :
    step runtimeProgressRecordClearMachine
        ⟨RuntimeProgressRecordClearState.advanceCandidate, p, T⟩ =
      ⟨RuntimeProgressRecordClearState.lo, p + 1, T⟩ := by
  simp [step, runtimeProgressRecordClearMachine, moveHead]

private theorem record_backOne_step (T : List Bool) (p : Nat) :
    step runtimeProgressRecordClearMachine
        ⟨RuntimeProgressRecordClearState.backOne, p + 2, T⟩ =
      ⟨RuntimeProgressRecordClearState.backTwo, p + 2, T⟩ := by
  simp [step, runtimeProgressRecordClearMachine, moveHead]

private theorem record_backTwo_step (T : List Bool) (p : Nat) :
    step runtimeProgressRecordClearMachine
        ⟨RuntimeProgressRecordClearState.backTwo, p + 2, T⟩ =
      ⟨RuntimeProgressRecordClearState.done, p + 2, T⟩ := by
  simp [step, runtimeProgressRecordClearMachine, moveHead]

/-- The first arbitrary pair is rewritten to the permanent `01` sentinel. -/
theorem runtimeProgressRecordClear_first
    (pre tail : List Bool) (lo hi : Bool)
    (hnz : lo = true ∨ hi = true) :
    run runtimeProgressRecordClearMachine 2
        ⟨runtimeProgressRecordClearMachine.start, pre.length,
          pre ++ [lo, hi] ++ tail⟩ =
      ⟨RuntimeProgressRecordClearState.lo, pre.length + 2,
        pre ++ [false, true] ++ tail⟩ := by
  let T0 := pre ++ [lo, hi] ++ tail
  let T1 := pre ++ [false, hi] ++ tail
  let T2 := pre ++ [false, true] ++ tail
  have h0 : T0[pre.length]?.getD false = lo := by simp [T0]
  have h1 : T1[pre.length + 1]?.getD false = hi := by simp [T1]
  have hw0 : writeAt T0 pre.length false = T1 := by
    simpa [T0, T1, List.append_assoc] using record_write pre (hi :: tail) lo false
  have hw1 : writeAt T1 (pre.length + 1) true = T2 := by
    simpa [T1, T2, List.append_assoc] using
      record_write (pre ++ [false]) tail hi true
  change run runtimeProgressRecordClearMachine 2
      ⟨RuntimeProgressRecordClearState.firstLo, pre.length, T0⟩ =
    ⟨RuntimeProgressRecordClearState.lo, pre.length + 2, T2⟩
  rw [show run runtimeProgressRecordClearMachine 2 _ =
      step runtimeProgressRecordClearMachine
        (step runtimeProgressRecordClearMachine
          ⟨RuntimeProgressRecordClearState.firstLo, pre.length, T0⟩) by rfl]
  rw [record_firstLo_step T0 T1 pre.length lo h0 hw0,
    record_firstHi_step T1 T2 (pre.length + 1) lo hi h1 hw1 hnz]

/-- Every later ordinary nonzero pair is rewritten to one `10` progress
word and control remains in the pair-scan loop. -/
theorem runtimeProgressRecordClear_nonzero
    (pre tail : List Bool) (lo hi : Bool)
    (hnz : lo = true ∨ hi = true) :
    run runtimeProgressRecordClearMachine 2
        ⟨RuntimeProgressRecordClearState.lo, pre.length,
          pre ++ [lo, hi] ++ tail⟩ =
      ⟨RuntimeProgressRecordClearState.lo, pre.length + 2,
        pre ++ [true, false] ++ tail⟩ := by
  let T0 := pre ++ [lo, hi] ++ tail
  let T1 := pre ++ [true, hi] ++ tail
  let T2 := pre ++ [true, false] ++ tail
  have h0 : T0[pre.length]?.getD false = lo := by simp [T0]
  have h1 : T1[pre.length + 1]?.getD false = hi := by simp [T1]
  have hw0 : writeAt T0 pre.length true = T1 := by
    simpa [T0, T1, List.append_assoc] using record_write pre (hi :: tail) lo true
  have hw1 : writeAt T1 (pre.length + 1) false = T2 := by
    simpa [T1, T2, List.append_assoc] using
      record_write (pre ++ [true]) tail hi false
  rw [show run runtimeProgressRecordClearMachine 2 _ =
      step runtimeProgressRecordClearMachine
        (step runtimeProgressRecordClearMachine
          ⟨RuntimeProgressRecordClearState.lo, pre.length, T0⟩) by rfl]
  rw [record_lo_step T0 T1 pre.length lo h0 hw0,
    record_hi_nonzero_step T1 T2 (pre.length + 1) lo hi h1 hw1 hnz]

/-- An isolated zero pair followed by a nonzero pair produces two progress
words.  The extra two transitions are the fixed rewrite detour needed to
distinguish this legal zero pair from the reserved double-zero marker. -/
theorem runtimeProgressRecordClear_isolatedZero
    (pre tail : List Bool) (lo hi : Bool)
    (hnz : lo = true ∨ hi = true) :
    run runtimeProgressRecordClearMachine 6
        ⟨RuntimeProgressRecordClearState.lo, pre.length,
          pre ++ [false, false, lo, hi] ++ tail⟩ =
      ⟨RuntimeProgressRecordClearState.lo, pre.length + 4,
        pre ++ [true, false, true, false] ++ tail⟩ := by
  let T0 := pre ++ [false, false, lo, hi] ++ tail
  let T1 := pre ++ [true, false, lo, hi] ++ tail
  let T2 := pre ++ [true, false, false, hi] ++ tail
  let T3 := pre ++ [true, false, false, false] ++ tail
  let T4 := pre ++ [true, false, true, false] ++ tail
  have h0 : T0[pre.length]?.getD false = false := by simp [T0]
  have h1 : T1[pre.length + 1]?.getD false = false := by simp [T1]
  have h2 : T1[pre.length + 2]?.getD false = lo := by simp [T1]
  have h3 : T2[pre.length + 3]?.getD false = hi := by simp [T2]
  have hr : T3[pre.length + 2]?.getD false = false := by simp [T3]
  have hw0 : writeAt T0 pre.length true = T1 := by
    simpa [T0, T1, List.append_assoc] using
      record_write pre (false :: lo :: hi :: tail) false true
  have hw1 : writeAt T1 (pre.length + 1) false = T1 := by
    simpa [T1, List.append_assoc] using
      record_write (pre ++ [true]) (lo :: hi :: tail) false false
  have hw2 : writeAt T1 (pre.length + 2) false = T2 := by
    simpa [T1, T2, List.append_assoc] using
      record_write (pre ++ [true, false]) (hi :: tail) lo false
  have hw3 : writeAt T2 (pre.length + 3) false = T3 := by
    simpa [T2, T3, List.append_assoc] using
      record_write (pre ++ [true, false, false]) tail hi false
  have hw4 : writeAt T3 (pre.length + 2) true = T4 := by
    simpa [T3, T4, List.append_assoc] using
      record_write (pre ++ [true, false]) (false :: tail) false true
  have hp : pre.length + 3 - 1 = pre.length + 2 := by omega
  change run runtimeProgressRecordClearMachine 6
      ⟨RuntimeProgressRecordClearState.lo, pre.length, T0⟩ =
    ⟨RuntimeProgressRecordClearState.lo, pre.length + 4, T4⟩
  rw [show run runtimeProgressRecordClearMachine 6 _ =
      step runtimeProgressRecordClearMachine
        (step runtimeProgressRecordClearMachine
          (step runtimeProgressRecordClearMachine
            (step runtimeProgressRecordClearMachine
              (step runtimeProgressRecordClearMachine
                (step runtimeProgressRecordClearMachine
                  ⟨RuntimeProgressRecordClearState.lo, pre.length, T0⟩))))) by rfl]
  rw [record_lo_step T0 T1 pre.length false h0 hw0,
    record_hi_zero_step T1 T1 (pre.length + 1) h1 hw1,
    record_candidateLo_step T1 T2 (pre.length + 2) lo h2 hw2,
    record_candidateHi_nonzero_step T2 T3 (pre.length + 3) lo hi h3 hw3 hnz,
    hp,
    record_rewriteCandidateLo_step T3 T4 (pre.length + 2) false hr hw4,
    record_advanceCandidate_step T4 (pre.length + 3)]

/-- The reserved `00 00` marker becomes exactly `10 00`: the last ordinary
progress word followed by the initial hole, with a genuine halt at the
hole's low cell. -/
theorem runtimeProgressRecordClear_marker (pre tail : List Bool) :
    run runtimeProgressRecordClearMachine 6
        ⟨RuntimeProgressRecordClearState.lo, pre.length,
          pre ++ [false, false, false, false] ++ tail⟩ =
      ⟨RuntimeProgressRecordClearState.done, pre.length + 2,
        pre ++ [true, false, false, false] ++ tail⟩ := by
  let T0 := pre ++ [false, false, false, false] ++ tail
  let T1 := pre ++ [true, false, false, false] ++ tail
  have h0 : T0[pre.length]?.getD false = false := by simp [T0]
  have h1 : T1[pre.length + 1]?.getD false = false := by simp [T1]
  have h2 : T1[pre.length + 2]?.getD false = false := by simp [T1]
  have h3 : T1[pre.length + 3]?.getD false = false := by simp [T1]
  have hw0 : writeAt T0 pre.length true = T1 := by
    simpa [T0, T1, List.append_assoc] using
      record_write pre (false :: false :: false :: tail) false true
  have hw1 : writeAt T1 (pre.length + 1) false = T1 := by
    simpa [T1, List.append_assoc] using
      record_write (pre ++ [true]) (false :: false :: tail) false false
  have hw2 : writeAt T1 (pre.length + 2) false = T1 := by
    simpa [T1, List.append_assoc] using
      record_write (pre ++ [true, false]) (false :: tail) false false
  have hw3 : writeAt T1 (pre.length + 3) false = T1 := by
    simpa [T1, List.append_assoc] using
      record_write (pre ++ [true, false, false]) tail false false
  change run runtimeProgressRecordClearMachine 6
      ⟨RuntimeProgressRecordClearState.lo, pre.length, T0⟩ =
    ⟨RuntimeProgressRecordClearState.done, pre.length + 2, T1⟩
  rw [show run runtimeProgressRecordClearMachine 6 _ =
      step runtimeProgressRecordClearMachine
        (step runtimeProgressRecordClearMachine
          (step runtimeProgressRecordClearMachine
            (step runtimeProgressRecordClearMachine
              (step runtimeProgressRecordClearMachine
                (step runtimeProgressRecordClearMachine
                  ⟨RuntimeProgressRecordClearState.lo, pre.length, T0⟩))))) by rfl]
  rw [record_lo_step T0 T1 pre.length false h0 hw0,
    record_hi_zero_step T1 T1 (pre.length + 1) h1 hw1,
    record_candidateLo_step T1 T1 (pre.length + 2) false h2 hw2,
    record_candidateHi_zero_step T1 T1 pre.length h3 hw3,
    record_backOne_step T1 pre.length, record_backTwo_step T1 pre.length]

/-! ## Exact first-halt facts for local segments -/

/-- Symbol-independent lower bound on transitions remaining before `done` can
be reached from each clearer control state. -/
def runtimeProgressRecordClearDistance : RuntimeProgressRecordClearState → Nat
  | .done => 0
  | .backTwo => 1
  | .backOne => 2
  | .candidateHi _ => 3
  | .candidateLo => 4
  | .hi _ => 5
  | .firstHi _ => 5
  | .lo => 6
  | .firstLo => 6
  | .advanceCandidate => 7
  | .rewriteCandidateLo => 8

theorem runtimeProgressRecordClear_distance_step
    (c : Cfg runtimeProgressRecordClearMachine) :
    runtimeProgressRecordClearDistance c.st ≤
      runtimeProgressRecordClearDistance
        (step runtimeProgressRecordClearMachine c).st + 1 := by
  rcases c with ⟨st, hd, tp⟩
  cases st with
  | firstHi loBit | hi loBit | candidateHi loBit =>
      cases hbit : tp[hd]?.getD false <;> cases loBit <;>
        simp [runtimeProgressRecordClearDistance, step,
          runtimeProgressRecordClearMachine, hbit]
  | firstLo | lo | candidateLo | rewriteCandidateLo | advanceCandidate |
      backOne | backTwo | done =>
      simp [runtimeProgressRecordClearDistance, step,
        runtimeProgressRecordClearMachine]

theorem runtimeProgressRecordClear_distance_run
    (c : Cfg runtimeProgressRecordClearMachine) (n : Nat) :
    runtimeProgressRecordClearDistance c.st ≤
      runtimeProgressRecordClearDistance
        (run runtimeProgressRecordClearMachine n c).st + n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [run_succ]
      have hs := runtimeProgressRecordClear_distance_step
        (run runtimeProgressRecordClearMachine n c)
      omega

theorem runtimeProgressRecordClear_no_halt_before_distance
    (c : Cfg runtimeProgressRecordClearMachine) (n : Nat)
    (hn : n < runtimeProgressRecordClearDistance c.st) :
    runtimeProgressRecordClearMachine.halt
      (run runtimeProgressRecordClearMachine n c).st = false := by
  have hd := runtimeProgressRecordClear_distance_run c n
  have hpos : 0 < runtimeProgressRecordClearDistance
      (run runtimeProgressRecordClearMachine n c).st := by omega
  generalize hs : (run runtimeProgressRecordClearMachine n c).st = s at hpos ⊢
  cases s <;> simp_all [runtimeProgressRecordClearDistance,
    runtimeProgressRecordClearMachine]

/-- The initial sentinel rewrite cannot halt during either local transition. -/
theorem runtimeProgressRecordClear_first_no_early
    (pre tail : List Bool) (lo hi : Bool)
    (_hnz : lo = true ∨ hi = true) :
    ∀ i < 2, runtimeProgressRecordClearMachine.halt
      (run runtimeProgressRecordClearMachine i
        ⟨runtimeProgressRecordClearMachine.start, pre.length,
          pre ++ [lo, hi] ++ tail⟩).st = false := by
  intro i hi2
  apply runtimeProgressRecordClear_no_halt_before_distance
  simp [runtimeProgressRecordClearMachine,
    runtimeProgressRecordClearDistance]
  omega

/-- An ordinary nonzero pair cannot halt during its two-step rewrite. -/
theorem runtimeProgressRecordClear_nonzero_no_early
    (pre tail : List Bool) (lo hi : Bool)
    (_hnz : lo = true ∨ hi = true) :
    ∀ i < 2, runtimeProgressRecordClearMachine.halt
      (run runtimeProgressRecordClearMachine i
        ⟨RuntimeProgressRecordClearState.lo, pre.length,
          pre ++ [lo, hi] ++ tail⟩).st = false := by
  intro i hi2
  apply runtimeProgressRecordClear_no_halt_before_distance
  simp [runtimeProgressRecordClearDistance]
  omega

/-- The legal isolated-zero detour returns to scanning without entering
`done` at any strict prefix of its six-transition clock. -/
theorem runtimeProgressRecordClear_isolatedZero_no_early
    (pre tail : List Bool) (lo hi : Bool)
    (_hnz : lo = true ∨ hi = true) :
    ∀ i < 6, runtimeProgressRecordClearMachine.halt
      (run runtimeProgressRecordClearMachine i
        ⟨RuntimeProgressRecordClearState.lo, pre.length,
          pre ++ [false, false, lo, hi] ++ tail⟩).st = false := by
  intro i hi6
  apply runtimeProgressRecordClear_no_halt_before_distance
  simpa [runtimeProgressRecordClearDistance]

/-- The reserved double-zero marker first reaches `done` exactly on its
sixth transition; neither scan nor physical rewind routes early. -/
theorem runtimeProgressRecordClear_marker_no_early (pre tail : List Bool) :
    ∀ i < 6, runtimeProgressRecordClearMachine.halt
      (run runtimeProgressRecordClearMachine i
        ⟨RuntimeProgressRecordClearState.lo, pre.length,
          pre ++ [false, false, false, false] ++ tail⟩).st = false := by
  intro i hi6
  apply runtimeProgressRecordClear_no_halt_before_distance
  simpa [runtimeProgressRecordClearDistance]

theorem runtimeProgressRecordClear_no_early_append
    (c d : Cfg runtimeProgressRecordClearMachine) (a b : Nat)
    (hexact : run runtimeProgressRecordClearMachine a c = d)
    (ha : ∀ i < a, runtimeProgressRecordClearMachine.halt
      (run runtimeProgressRecordClearMachine i c).st = false)
    (hb : ∀ j < b, runtimeProgressRecordClearMachine.halt
      (run runtimeProgressRecordClearMachine j d).st = false) :
    ∀ i < a + b, runtimeProgressRecordClearMachine.halt
      (run runtimeProgressRecordClearMachine i c).st = false := by
  intro i hi
  by_cases hia : i < a
  · exact ha i hia
  · obtain ⟨j, rfl⟩ : ∃ j, i = a + j := ⟨i - a, by omega⟩
    rw [run_add, hexact]
    exact hb j (by omega)

/-! ## Structural lifts -/

private theorem progressWords_succ (n : Nat) :
    flattenPairs (List.replicate (n + 1) (true, false)) =
      flattenPairs (List.replicate n (true, false)) ++ [true, false] := by
  rw [List.replicate_add, flattenPairs_append]
  rfl

private theorem progressWords_commute (n : Nat) :
    flattenPairs (List.replicate n (true, false)) ++ [true, false] =
      [true, false] ++ flattenPairs (List.replicate n (true, false)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [List.replicate_succ, flattenPairs] at ih ⊢
      exact ih

private theorem progressWords_add (m n : Nat) :
    flattenPairs (List.replicate (m + n) (true, false)) =
      flattenPairs (List.replicate m (true, false)) ++
        flattenPairs (List.replicate n (true, false)) := by
  rw [List.replicate_add, flattenPairs_append]

/-- From the ordinary scan state, any nonzero pair prefix becomes a
contiguous list of `10` progress words in one uninterrupted run. -/
theorem runtimeProgressRecordClear_nonzeroPairs
    (pre tail : List Bool) (ps : List (Bool × Bool))
    (hnz : ∀ p ∈ ps, p.1 = true ∨ p.2 = true) :
    run runtimeProgressRecordClearMachine (2 * ps.length)
        ⟨RuntimeProgressRecordClearState.lo, pre.length,
          pre ++ flattenPairs ps ++ tail⟩ =
      ⟨RuntimeProgressRecordClearState.lo,
        pre.length + 2 * ps.length,
        pre ++ flattenPairs (List.replicate ps.length (true, false)) ++ tail⟩ := by
  induction ps generalizing pre with
  | nil => simp [flattenPairs]
  | cons p ps ih =>
      rcases p with ⟨lo, hi⟩
      have hp : lo = true ∨ hi = true := hnz (lo, hi) (by simp)
      have hrest : ∀ q ∈ ps, q.1 = true ∨ q.2 = true := by
        intro q hq
        exact hnz q (by simp [hq])
      rw [show 2 * ((lo, hi) :: ps).length = 2 + 2 * ps.length by
          simp; omega,
        run_add]
      have hfirst := runtimeProgressRecordClear_nonzero
        pre (flattenPairs ps ++ tail) lo hi hp
      have hfirst' : run runtimeProgressRecordClearMachine 2
          ⟨RuntimeProgressRecordClearState.lo, pre.length,
            pre ++ flattenPairs ((lo, hi) :: ps) ++ tail⟩ =
        ⟨RuntimeProgressRecordClearState.lo, pre.length + 2,
          pre ++ [true, false] ++ flattenPairs ps ++ tail⟩ := by
        simpa [flattenPairs, List.append_assoc] using hfirst
      rw [hfirst']
      have hih := ih (pre := pre ++ [true, false]) hrest
      convert hih using 1 <;>
        simp [progressWords_succ, progressWords_commute,
          List.append_assoc, Nat.add_assoc]

theorem runtimeProgressRecordClear_nonzeroPairs_no_early
    (pre tail : List Bool) (ps : List (Bool × Bool))
    (hnz : ∀ p ∈ ps, p.1 = true ∨ p.2 = true) :
    ∀ i < 2 * ps.length, runtimeProgressRecordClearMachine.halt
      (run runtimeProgressRecordClearMachine i
        ⟨RuntimeProgressRecordClearState.lo, pre.length,
          pre ++ flattenPairs ps ++ tail⟩).st = false := by
  induction ps generalizing pre with
  | nil => simp
  | cons p ps ih =>
      rcases p with ⟨lo, hi⟩
      have hp : lo = true ∨ hi = true := hnz (lo, hi) (by simp)
      have hrest : ∀ q ∈ ps, q.1 = true ∨ q.2 = true := by
        intro q hq
        exact hnz q (by simp [hq])
      have hexact := runtimeProgressRecordClear_nonzero
        pre (flattenPairs ps ++ tail) lo hi hp
      rw [show 2 * ((lo, hi) :: ps).length = 2 + 2 * ps.length by
        simp; omega]
      apply runtimeProgressRecordClear_no_early_append
        _ _ 2 (2 * ps.length)
      · simpa [flattenPairs, List.append_assoc] using hexact
      · simpa [flattenPairs, List.append_assoc] using
          runtimeProgressRecordClear_nonzero_no_early
            pre (flattenPairs ps ++ tail) lo hi hp
      · simpa [List.append_assoc, Nat.add_assoc] using
          ih (pre := pre ++ [true, false]) hrest

/-- A nonzero suffix is converted to progress words and the reserved marker
becomes the final progress word followed by the initial hole. -/
theorem runtimeProgressRecordClear_nonzeroPrefix_marker
    (pre tail : List Bool) (ps : List (Bool × Bool))
    (hnz : ∀ p ∈ ps, p.1 = true ∨ p.2 = true) :
    run runtimeProgressRecordClearMachine (2 * ps.length + 6)
        ⟨RuntimeProgressRecordClearState.lo, pre.length,
          pre ++ flattenPairs ps ++
            flattenPairs runtimePassedBoundaryMarker ++ tail⟩ =
      ⟨RuntimeProgressRecordClearState.done,
        pre.length + 2 * ps.length + 2,
        pre ++ flattenPairs (List.replicate (ps.length + 1) (true, false)) ++
          [false, false] ++ tail⟩ := by
  rw [run_add]
  have hp := runtimeProgressRecordClear_nonzeroPairs pre
    (flattenPairs runtimePassedBoundaryMarker ++ tail) ps hnz
  simp only [List.append_assoc] at hp ⊢
  rw [hp]
  have hm := runtimeProgressRecordClear_marker
    (pre ++ flattenPairs (List.replicate ps.length (true, false))) tail
  simpa [progressWords_succ, List.append_assoc,
    Nat.add_assoc] using hm

theorem runtimeProgressRecordClear_nonzeroPrefix_marker_no_early
    (pre tail : List Bool) (ps : List (Bool × Bool))
    (hnz : ∀ p ∈ ps, p.1 = true ∨ p.2 = true) :
    ∀ i < 2 * ps.length + 6, runtimeProgressRecordClearMachine.halt
      (run runtimeProgressRecordClearMachine i
        ⟨RuntimeProgressRecordClearState.lo, pre.length,
          pre ++ flattenPairs ps ++
            flattenPairs runtimePassedBoundaryMarker ++ tail⟩).st = false := by
  let mid : Cfg runtimeProgressRecordClearMachine :=
    ⟨RuntimeProgressRecordClearState.lo, pre.length + 2 * ps.length,
      pre ++ flattenPairs (List.replicate ps.length (true, false)) ++
        flattenPairs runtimePassedBoundaryMarker ++ tail⟩
  apply runtimeProgressRecordClear_no_early_append _ mid
    (2 * ps.length) 6
  · simpa [mid, List.append_assoc] using
      runtimeProgressRecordClear_nonzeroPairs pre
        (flattenPairs runtimePassedBoundaryMarker ++ tail) ps hnz
  · simpa [List.append_assoc] using
      runtimeProgressRecordClear_nonzeroPairs_no_early pre
        (flattenPairs runtimePassedBoundaryMarker ++ tail) ps hnz
  · simpa [mid, List.append_assoc, flattenPairs_length] using
      runtimeProgressRecordClear_marker_no_early
        (pre ++ flattenPairs (List.replicate ps.length (true, false))) tail

/-- Starting from the machine's genuine initial state, a nonzero first pair
becomes the sentinel and an all-nonzero remainder is lifted through the
marker to the initial hole. -/
theorem runtimeProgressRecordClear_nonzeroWorkspace
    (pre tail : List Bool) (q : Bool × Bool) (rest : List (Bool × Bool))
    (hq : q.1 = true ∨ q.2 = true)
    (hrest : ∀ p ∈ rest, p.1 = true ∨ p.2 = true) :
    run runtimeProgressRecordClearMachine (2 + (2 * rest.length + 6))
        ⟨runtimeProgressRecordClearMachine.start, pre.length,
          pre ++ flattenPairs (q :: rest) ++
            flattenPairs runtimePassedBoundaryMarker ++ tail⟩ =
      ⟨RuntimeProgressRecordClearState.done,
        pre.length + 2 + 2 * rest.length + 2,
        pre ++ [false, true] ++
          flattenPairs (List.replicate (rest.length + 1) (true, false)) ++
          [false, false] ++ tail⟩ := by
  rw [run_add]
  have hf := runtimeProgressRecordClear_first pre
    (flattenPairs rest ++ flattenPairs runtimePassedBoundaryMarker ++ tail)
    q.1 q.2 hq
  have hf' : run runtimeProgressRecordClearMachine 2
      ⟨runtimeProgressRecordClearMachine.start, pre.length,
        pre ++ flattenPairs (q :: rest) ++
          flattenPairs runtimePassedBoundaryMarker ++ tail⟩ =
    ⟨RuntimeProgressRecordClearState.lo, pre.length + 2,
      pre ++ [false, true] ++ flattenPairs rest ++
        flattenPairs runtimePassedBoundaryMarker ++ tail⟩ := by
    simpa [flattenPairs, List.append_assoc] using hf
  rw [hf']
  have hr := runtimeProgressRecordClear_nonzeroPrefix_marker
    (pre ++ [false, true]) tail rest hrest
  simpa only [List.length_append, List.length_cons, List.length_nil,
    Nat.add_zero, List.append_assoc] using hr

theorem runtimeProgressRecordClear_nonzeroWorkspace_no_early
    (pre tail : List Bool) (q : Bool × Bool) (rest : List (Bool × Bool))
    (hq : q.1 = true ∨ q.2 = true)
    (hrest : ∀ p ∈ rest, p.1 = true ∨ p.2 = true) :
    ∀ i < 2 + (2 * rest.length + 6),
      runtimeProgressRecordClearMachine.halt
        (run runtimeProgressRecordClearMachine i
          ⟨runtimeProgressRecordClearMachine.start, pre.length,
            pre ++ flattenPairs (q :: rest) ++
              flattenPairs runtimePassedBoundaryMarker ++ tail⟩).st = false := by
  let mid : Cfg runtimeProgressRecordClearMachine :=
    ⟨RuntimeProgressRecordClearState.lo, pre.length + 2,
      pre ++ [false, true] ++ flattenPairs rest ++
        flattenPairs runtimePassedBoundaryMarker ++ tail⟩
  apply runtimeProgressRecordClear_no_early_append _ mid 2
    (2 * rest.length + 6)
  · simpa [mid, flattenPairs, List.append_assoc] using
      runtimeProgressRecordClear_first pre
        (flattenPairs rest ++ flattenPairs runtimePassedBoundaryMarker ++ tail)
        q.1 q.2 hq
  · simpa [flattenPairs, List.append_assoc] using
      runtimeProgressRecordClear_first_no_early pre
        (flattenPairs rest ++ flattenPairs runtimePassedBoundaryMarker ++ tail)
        q.1 q.2 hq
  · simpa [mid, List.append_assoc] using
      runtimeProgressRecordClear_nonzeroPrefix_marker_no_early
        (pre ++ [false, true]) tail rest hrest

/-- The isolated-zero splice followed by an arbitrary nonzero remainder and
the reserved marker.  This is the distinctive core of the false branch. -/
theorem runtimeProgressRecordClear_isolatedZero_marker
    (pre tail : List Bool) (next : Bool × Bool)
    (rest : List (Bool × Bool))
    (hnext : next.1 = true ∨ next.2 = true)
    (hrest : ∀ p ∈ rest, p.1 = true ∨ p.2 = true) :
    run runtimeProgressRecordClearMachine (6 + (2 * rest.length + 6))
        ⟨RuntimeProgressRecordClearState.lo, pre.length,
          pre ++ flattenPairs ([(false, false), next] ++ rest) ++
            flattenPairs runtimePassedBoundaryMarker ++ tail⟩ =
      ⟨RuntimeProgressRecordClearState.done,
        pre.length + 4 + 2 * rest.length + 2,
        pre ++ [true, false, true, false] ++
          flattenPairs (List.replicate (rest.length + 1) (true, false)) ++
          [false, false] ++ tail⟩ := by
  rw [run_add]
  have hz := runtimeProgressRecordClear_isolatedZero pre
    (flattenPairs rest ++ flattenPairs runtimePassedBoundaryMarker ++ tail)
    next.1 next.2 hnext
  have hz' : run runtimeProgressRecordClearMachine 6
      ⟨RuntimeProgressRecordClearState.lo, pre.length,
        pre ++ flattenPairs ([(false, false), next] ++ rest) ++
          flattenPairs runtimePassedBoundaryMarker ++ tail⟩ =
    ⟨RuntimeProgressRecordClearState.lo, pre.length + 4,
      pre ++ [true, false, true, false] ++ flattenPairs rest ++
        flattenPairs runtimePassedBoundaryMarker ++ tail⟩ := by
    simpa [flattenPairs, List.append_assoc] using hz
  rw [hz']
  have hr := runtimeProgressRecordClear_nonzeroPrefix_marker
    (pre ++ [true, false, true, false]) tail rest hrest
  have hpre : (pre ++ [true, false, true, false]).length = pre.length + 4 := by
    simp
  rw [hpre] at hr
  have hend : pre.length + 4 + 2 * rest.length + 2 =
      pre.length + 4 + (2 * rest.length + 2) := by omega
  rw [hend]
  simpa only [List.append_assoc] using hr

theorem runtimeProgressRecordClear_isolatedZero_marker_no_early
    (pre tail : List Bool) (next : Bool × Bool)
    (rest : List (Bool × Bool))
    (hnext : next.1 = true ∨ next.2 = true)
    (hrest : ∀ p ∈ rest, p.1 = true ∨ p.2 = true) :
    ∀ i < 6 + (2 * rest.length + 6),
      runtimeProgressRecordClearMachine.halt
        (run runtimeProgressRecordClearMachine i
          ⟨RuntimeProgressRecordClearState.lo, pre.length,
            pre ++ flattenPairs ([(false, false), next] ++ rest) ++
              flattenPairs runtimePassedBoundaryMarker ++ tail⟩).st = false := by
  let mid : Cfg runtimeProgressRecordClearMachine :=
    ⟨RuntimeProgressRecordClearState.lo, pre.length + 4,
      pre ++ [true, false, true, false] ++ flattenPairs rest ++
        flattenPairs runtimePassedBoundaryMarker ++ tail⟩
  apply runtimeProgressRecordClear_no_early_append _ mid 6
    (2 * rest.length + 6)
  · simpa [mid, flattenPairs, List.append_assoc] using
      runtimeProgressRecordClear_isolatedZero pre
        (flattenPairs rest ++ flattenPairs runtimePassedBoundaryMarker ++ tail)
        next.1 next.2 hnext
  · simpa [flattenPairs, List.append_assoc] using
      runtimeProgressRecordClear_isolatedZero_no_early pre
        (flattenPairs rest ++ flattenPairs runtimePassedBoundaryMarker ++ tail)
        next.1 next.2 hnext
  · simpa [mid, List.append_assoc, Nat.add_assoc] using
      runtimeProgressRecordClear_nonzeroPrefix_marker_no_early
        (pre ++ [true, false, true, false]) tail rest hrest

/-- Add the genuine initial sentinel step and an arbitrary nonzero front to
the isolated-zero core. -/
theorem runtimeProgressRecordClear_first_front_isolatedZero_marker
    (pre tail : List Bool) (first next : Bool × Bool)
    (front rest : List (Bool × Bool))
    (hfirst : first.1 = true ∨ first.2 = true)
    (hfront : ∀ p ∈ front, p.1 = true ∨ p.2 = true)
    (hnext : next.1 = true ∨ next.2 = true)
    (hrest : ∀ p ∈ rest, p.1 = true ∨ p.2 = true) :
    run runtimeProgressRecordClearMachine
        (2 + (2 * front.length + (6 + (2 * rest.length + 6))))
        ⟨runtimeProgressRecordClearMachine.start, pre.length,
          pre ++ flattenPairs
            (first :: (front ++ [(false, false), next] ++ rest)) ++
            flattenPairs runtimePassedBoundaryMarker ++ tail⟩ =
      ⟨RuntimeProgressRecordClearState.done,
        pre.length + 2 + 2 * front.length + 4 + 2 * rest.length + 2,
        pre ++ [false, true] ++
          flattenPairs (List.replicate front.length (true, false)) ++
          [true, false, true, false] ++
          flattenPairs (List.replicate (rest.length + 1) (true, false)) ++
          [false, false] ++ tail⟩ := by
  rw [run_add]
  have hf := runtimeProgressRecordClear_first pre
    (flattenPairs (front ++ [(false, false), next] ++ rest) ++
      flattenPairs runtimePassedBoundaryMarker ++ tail)
    first.1 first.2 hfirst
  have hf' : run runtimeProgressRecordClearMachine 2
      ⟨runtimeProgressRecordClearMachine.start, pre.length,
        pre ++ flattenPairs
          (first :: (front ++ [(false, false), next] ++ rest)) ++
          flattenPairs runtimePassedBoundaryMarker ++ tail⟩ =
    ⟨RuntimeProgressRecordClearState.lo, pre.length + 2,
      pre ++ [false, true] ++
        flattenPairs (front ++ [(false, false), next] ++ rest) ++
        flattenPairs runtimePassedBoundaryMarker ++ tail⟩ := by
    simpa [flattenPairs, List.append_assoc] using hf
  rw [hf', run_add]
  have hp := runtimeProgressRecordClear_nonzeroPairs
    (pre ++ [false, true])
    (flattenPairs ([(false, false), next] ++ rest) ++
      flattenPairs runtimePassedBoundaryMarker ++ tail) front hfront
  have hp' : run runtimeProgressRecordClearMachine (2 * front.length)
      ⟨RuntimeProgressRecordClearState.lo, pre.length + 2,
        pre ++ [false, true] ++
          flattenPairs (front ++ [(false, false), next] ++ rest) ++
          flattenPairs runtimePassedBoundaryMarker ++ tail⟩ =
    ⟨RuntimeProgressRecordClearState.lo,
      pre.length + 2 + 2 * front.length,
      pre ++ [false, true] ++
        flattenPairs (List.replicate front.length (true, false)) ++
        flattenPairs ([(false, false), next] ++ rest) ++
        flattenPairs runtimePassedBoundaryMarker ++ tail⟩ := by
    simpa [flattenPairs_append, List.append_assoc, Nat.add_assoc] using hp
  rw [hp']
  have hz := runtimeProgressRecordClear_isolatedZero_marker
    (pre ++ [false, true] ++
      flattenPairs (List.replicate front.length (true, false)))
    tail next rest hnext hrest
  have hpre : (pre ++ [false, true] ++
      flattenPairs (List.replicate front.length (true, false))).length =
      pre.length + 2 + 2 * front.length := by
    simp [flattenPairs_length]
    omega
  rw [hpre] at hz
  have hend : pre.length + 2 + 2 * front.length + 4 +
      2 * rest.length + 2 =
      pre.length + 2 + 2 * front.length + (4 + 2 * rest.length + 2) := by omega
  convert hz using 1

theorem runtimeProgressRecordClear_first_front_isolatedZero_marker_no_early
    (pre tail : List Bool) (first next : Bool × Bool)
    (front rest : List (Bool × Bool))
    (hfirst : first.1 = true ∨ first.2 = true)
    (hfront : ∀ p ∈ front, p.1 = true ∨ p.2 = true)
    (hnext : next.1 = true ∨ next.2 = true)
    (hrest : ∀ p ∈ rest, p.1 = true ∨ p.2 = true) :
    ∀ i < 2 + (2 * front.length + (6 + (2 * rest.length + 6))),
      runtimeProgressRecordClearMachine.halt
        (run runtimeProgressRecordClearMachine i
          ⟨runtimeProgressRecordClearMachine.start, pre.length,
            pre ++ flattenPairs
              (first :: (front ++ [(false, false), next] ++ rest)) ++
              flattenPairs runtimePassedBoundaryMarker ++ tail⟩).st = false := by
  let mid1 : Cfg runtimeProgressRecordClearMachine :=
    ⟨RuntimeProgressRecordClearState.lo, pre.length + 2,
      pre ++ [false, true] ++
        flattenPairs (front ++ [(false, false), next] ++ rest) ++
        flattenPairs runtimePassedBoundaryMarker ++ tail⟩
  let mid2 : Cfg runtimeProgressRecordClearMachine :=
    ⟨RuntimeProgressRecordClearState.lo,
      pre.length + 2 + 2 * front.length,
      pre ++ [false, true] ++
        flattenPairs (List.replicate front.length (true, false)) ++
        flattenPairs ([(false, false), next] ++ rest) ++
        flattenPairs runtimePassedBoundaryMarker ++ tail⟩
  apply runtimeProgressRecordClear_no_early_append _ mid1 2
    (2 * front.length + (6 + (2 * rest.length + 6)))
  · simpa [mid1, flattenPairs, List.append_assoc] using
      runtimeProgressRecordClear_first pre
        (flattenPairs (front ++ [(false, false), next] ++ rest) ++
          flattenPairs runtimePassedBoundaryMarker ++ tail)
        first.1 first.2 hfirst
  · simpa [flattenPairs, List.append_assoc] using
      runtimeProgressRecordClear_first_no_early pre
        (flattenPairs (front ++ [(false, false), next] ++ rest) ++
          flattenPairs runtimePassedBoundaryMarker ++ tail)
        first.1 first.2 hfirst
  · apply runtimeProgressRecordClear_no_early_append mid1 mid2
      (2 * front.length) (6 + (2 * rest.length + 6))
    · simpa [mid1, mid2, flattenPairs_append, List.append_assoc,
        Nat.add_assoc] using
        runtimeProgressRecordClear_nonzeroPairs
          (pre ++ [false, true])
          (flattenPairs ([(false, false), next] ++ rest) ++
            flattenPairs runtimePassedBoundaryMarker ++ tail) front hfront
    · simpa [mid1, flattenPairs_append, List.append_assoc] using
        runtimeProgressRecordClear_nonzeroPairs_no_early
          (pre ++ [false, true])
          (flattenPairs ([(false, false), next] ++ rest) ++
            flattenPairs runtimePassedBoundaryMarker ++ tail) front hfront
    · have hz := runtimeProgressRecordClear_isolatedZero_marker_no_early
          (pre ++ [false, true] ++
            flattenPairs (List.replicate front.length (true, false)))
          tail next rest hnext hrest
      have hhead : (pre ++ [false, true] ++
          flattenPairs (List.replicate front.length (true, false))).length =
          pre.length + 2 + 2 * front.length := by
        simp [flattenPairs_length]
        omega
      rw [hhead] at hz
      simpa [mid2, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hz

/-- Complete progress-record production for the exact reachable workspace
grammar, including both Boolean values and all `m,n`. -/
theorem runtimeProgressRecordClear_workspace
    (pre tail : List Bool) (value : Bool) (m n : Nat) :
    let workspace := runtimeWorkspaceFrontPairs value m n
    let clock := 2 * workspace.length + 6 + if value then 0 else 2
    run runtimeProgressRecordClearMachine clock
        ⟨runtimeProgressRecordClearMachine.start, pre.length,
          pre ++ flattenPairs workspace ++
            flattenPairs runtimePassedBoundaryMarker ++ tail⟩ =
      ⟨RuntimeProgressRecordClearState.done,
        pre.length + 2 * workspace.length + 2,
        pre ++ [false, true] ++
          flattenPairs (List.replicate workspace.length (true, false)) ++
          [false, false] ++ tail⟩ := by
  dsimp only
  cases value
  · cases m with
    | zero =>
        let front : List (Bool × Bool) := [(false, true)]
        let rest : List (Bool × Bool) := List.replicate n (true, true)
        have hf : ∀ p ∈ front, p.1 = true ∨ p.2 = true := by
          intro p hp
          simp [front] at hp
          subst p
          simp
        have hr : ∀ p ∈ rest, p.1 = true ∨ p.2 = true := by
          intro p hp
          simp [rest] at hp
          rcases hp with ⟨_, rfl⟩
          simp
        have h := runtimeProgressRecordClear_first_front_isolatedZero_marker
          pre tail (true, false) (false, true) front rest
          (by simp) hf (by simp) hr
        have hc : 2 * (runtimeWorkspaceFrontPairs false 0 n).length + 6 + 2 =
            2 + (2 * front.length + (6 + (2 * rest.length + 6))) := by
          simp [runtimeWorkspaceFrontPairs, front, rest]
          omega
        simp only [Bool.false_eq_true, if_false]
        rw [hc]
        convert h using 1
        all_goals simp [runtimeWorkspaceFrontPairs, front, rest, progressWords_add,
          progressWords_commute, flattenPairs, List.append_assoc]
        all_goals omega
    | succ k =>
        let front : List (Bool × Bool) := [(false, true)]
        let rest : List (Bool × Bool) :=
          List.replicate k (true, false) ++ [(false, true)] ++
            List.replicate n (true, true)
        have hf : ∀ p ∈ front, p.1 = true ∨ p.2 = true := by
          intro p hp
          simp [front] at hp
          subst p
          simp
        have hr : ∀ p ∈ rest, p.1 = true ∨ p.2 = true := by
          intro p hp
          simp [rest] at hp
          rcases hp with h | h | h
          · rcases h with ⟨_, rfl⟩; simp
          · subst p; simp
          · rcases h with ⟨_, rfl⟩; simp
        have h := runtimeProgressRecordClear_first_front_isolatedZero_marker
          pre tail (true, false) (true, false) front rest
          (by simp) hf (by simp) hr
        have hc : 2 * (runtimeWorkspaceFrontPairs false (k + 1) n).length + 6 + 2 =
            2 + (2 * front.length + (6 + (2 * rest.length + 6))) := by
          simp [runtimeWorkspaceFrontPairs, front, rest]
          omega
        simp only [Bool.false_eq_true, if_false]
        rw [hc]
        convert h using 1
        all_goals simp [runtimeWorkspaceFrontPairs, front, rest,
          List.replicate_succ, flattenPairs, List.append_assoc]
        all_goals omega
  · let rest := (false, true) :: (true, true) ::
        (List.replicate m (true, false) ++ [(false, true)] ++
          List.replicate n (true, true))
    have hr : ∀ p ∈ rest, p.1 = true ∨ p.2 = true := by
      intro p hp
      simp [rest] at hp
      rcases hp with h | h | h | h
      · subst p; simp
      · subst p; simp
      · rcases h with ⟨_, rfl⟩; simp
      · rcases h with rfl | ⟨_, rfl⟩
        · simp
        · simp
    have h := runtimeProgressRecordClear_nonzeroWorkspace
      pre tail (true, false) rest (by simp) hr
    have hc : 2 * (runtimeWorkspaceFrontPairs true m n).length + 6 =
        2 + (2 * rest.length + 6) := by
      simp [runtimeWorkspaceFrontPairs, rest]
      omega
    rw [hc]
    convert h using 1
    all_goals simp [runtimeWorkspaceFrontPairs, rest, List.append_assoc]
    all_goals omega

theorem runtimeProgressRecordClear_workspace_no_early
    (pre tail : List Bool) (value : Bool) (m n : Nat) :
    let workspace := runtimeWorkspaceFrontPairs value m n
    let clock := 2 * workspace.length + 6 + if value then 0 else 2
    ∀ i < clock, runtimeProgressRecordClearMachine.halt
      (run runtimeProgressRecordClearMachine i
        ⟨runtimeProgressRecordClearMachine.start, pre.length,
          pre ++ flattenPairs workspace ++
            flattenPairs runtimePassedBoundaryMarker ++ tail⟩).st = false := by
  dsimp only
  cases value
  · cases m with
    | zero =>
        let front : List (Bool × Bool) := [(false, true)]
        let rest : List (Bool × Bool) := List.replicate n (true, true)
        have hf : ∀ p ∈ front, p.1 = true ∨ p.2 = true := by
          intro p hp
          simp [front] at hp
          subst p
          simp
        have hr : ∀ p ∈ rest, p.1 = true ∨ p.2 = true := by
          intro p hp
          simp [rest] at hp
          rcases hp with ⟨_, rfl⟩
          simp
        have h := runtimeProgressRecordClear_first_front_isolatedZero_marker_no_early
          pre tail (true, false) (false, true) front rest
          (by simp) hf (by simp) hr
        have hc : 2 * (runtimeWorkspaceFrontPairs false 0 n).length + 6 + 2 =
            2 + (2 * front.length + (6 + (2 * rest.length + 6))) := by
          simp [runtimeWorkspaceFrontPairs, front, rest]
          omega
        simp only [Bool.false_eq_true, if_false]
        rw [hc]
        simpa [runtimeWorkspaceFrontPairs, front, rest, flattenPairs,
          List.append_assoc] using h
    | succ k =>
        let front : List (Bool × Bool) := [(false, true)]
        let rest : List (Bool × Bool) :=
          List.replicate k (true, false) ++ [(false, true)] ++
            List.replicate n (true, true)
        have hf : ∀ p ∈ front, p.1 = true ∨ p.2 = true := by
          intro p hp
          simp [front] at hp
          subst p
          simp
        have hr : ∀ p ∈ rest, p.1 = true ∨ p.2 = true := by
          intro p hp
          simp [rest] at hp
          rcases hp with h | h | h
          · rcases h with ⟨_, rfl⟩; simp
          · subst p; simp
          · rcases h with ⟨_, rfl⟩; simp
        have h := runtimeProgressRecordClear_first_front_isolatedZero_marker_no_early
          pre tail (true, false) (true, false) front rest
          (by simp) hf (by simp) hr
        have hc : 2 * (runtimeWorkspaceFrontPairs false (k + 1) n).length + 6 + 2 =
            2 + (2 * front.length + (6 + (2 * rest.length + 6))) := by
          simp [runtimeWorkspaceFrontPairs, front, rest]
          omega
        simp only [Bool.false_eq_true, if_false]
        rw [hc]
        simpa [runtimeWorkspaceFrontPairs, front, rest,
          List.replicate_succ, flattenPairs, List.append_assoc] using h
  · let rest := (false, true) :: (true, true) ::
        (List.replicate m (true, false) ++ [(false, true)] ++
          List.replicate n (true, true))
    have hr : ∀ p ∈ rest, p.1 = true ∨ p.2 = true := by
      intro p hp
      simp [rest] at hp
      rcases hp with h | h | h | h
      · subst p; simp
      · subst p; simp
      · rcases h with ⟨_, rfl⟩; simp
      · rcases h with rfl | ⟨_, rfl⟩
        · simp
        · simp
    have h := runtimeProgressRecordClear_nonzeroWorkspace_no_early
      pre tail (true, false) rest (by simp) hr
    have hc : 2 * (runtimeWorkspaceFrontPairs true m n).length + 6 =
        2 + (2 * rest.length + 6) := by
      simp [runtimeWorkspaceFrontPairs, rest]
      omega
    rw [hc]
    simpa [runtimeWorkspaceFrontPairs, rest, List.append_assoc] using h

@[simp] theorem runtimeProgressRecordClear_done_halts :
    runtimeProgressRecordClearMachine.halt
      RuntimeProgressRecordClearState.done = true := by
  simp [runtimeProgressRecordClearMachine]

#print axioms runtimeProgressRecordClear_first
#print axioms runtimeProgressRecordClear_nonzero
#print axioms runtimeProgressRecordClear_isolatedZero
#print axioms runtimeProgressRecordClear_marker
#print axioms runtimeProgressRecordClear_nonzeroPairs
#print axioms runtimeProgressRecordClear_nonzeroPrefix_marker
#print axioms runtimeProgressRecordClear_nonzeroWorkspace
#print axioms runtimeProgressRecordClear_isolatedZero_marker
#print axioms runtimeProgressRecordClear_first_front_isolatedZero_marker
#print axioms runtimeProgressRecordClear_workspace
#print axioms runtimeProgressRecordClear_first_no_early
#print axioms runtimeProgressRecordClear_distance_step
#print axioms runtimeProgressRecordClear_no_halt_before_distance
#print axioms runtimeProgressRecordClear_nonzero_no_early
#print axioms runtimeProgressRecordClear_isolatedZero_no_early
#print axioms runtimeProgressRecordClear_marker_no_early
#print axioms runtimeProgressRecordClear_nonzeroPairs_no_early
#print axioms runtimeProgressRecordClear_nonzeroPrefix_marker_no_early
#print axioms runtimeProgressRecordClear_nonzeroWorkspace_no_early
#print axioms runtimeProgressRecordClear_isolatedZero_marker_no_early
#print axioms runtimeProgressRecordClear_first_front_isolatedZero_marker_no_early
#print axioms runtimeProgressRecordClear_workspace_no_early

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeProgressRecordClear
