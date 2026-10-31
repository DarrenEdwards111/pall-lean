import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeMarkedBoundaryScanner

/-!
# Fixed marker-driven workspace clearer

This is the destructive companion of the marked-boundary scanner.  It uses
the same constant control graph, but clears every inspected workspace cell.
The original bits needed to classify a pair are retained in finite control;
therefore cells already crossed may safely become zero.  The reserved second
`00` pair is still read before it is cleared, and the controller rewinds to
the first cell of the resulting zero block and halts.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeMarkerDrivenClear

set_option maxHeartbeats 4000000

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundEntryAdapter
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePreservedPassedCopy
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeMarkedBoundaryScanner
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryTerminal

inductive RuntimeMarkerDrivenClearState
  | lo
  | hi (loBit : Bool)
  | candidateLo
  | candidateHi (loBit : Bool)
  | backOne
  | backTwo
  | done
  deriving DecidableEq, Fintype

/-- One fixed controller simultaneously locates the first certified marker
and clears every cell it crosses. -/
def runtimeMarkerDrivenClearMachine : Machine where
  State := RuntimeMarkerDrivenClearState
  fin := inferInstance
  dec := inferInstance
  start := .lo
  halt := fun s => decide (s = .done)
  δ := fun s b =>
    match s with
    | .lo => (.hi b, some false, 1)
    | .hi loBit =>
        if !loBit && !b then (.candidateLo, some false, 1)
        else (.lo, some false, 1)
    | .candidateLo => (.candidateHi b, some false, 1)
    | .candidateHi loBit =>
        if !loBit && !b then (.backOne, some false, 0)
        else (.lo, some false, 1)
    | .backOne => (.backTwo, none, 0)
    | .backTwo => (.done, none, 0)
    | .done => (.done, none, 2)
  accept := fun _ => false

private theorem write0 (pre tail : List Bool) (b : Bool) :
    writeAt (pre ++ b :: tail) pre.length false =
      pre ++ false :: tail := by
  rw [PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr.writeAt_of_lt
    false (by simp)]
  simp

private theorem clear_lo_step (T T' : List Bool) (p : Nat) (b : Bool)
    (hread : T[p]?.getD false = b) (hwrite : writeAt T p false = T') :
    step runtimeMarkerDrivenClearMachine
        ⟨RuntimeMarkerDrivenClearState.lo, p, T⟩ =
      ⟨RuntimeMarkerDrivenClearState.hi b, p + 1, T'⟩ := by
  simp [step, runtimeMarkerDrivenClearMachine, moveHead, hread, hwrite]

private theorem clear_hi_nonzero_step (T T' : List Bool) (p : Nat)
    (lo hi : Bool) (hread : T[p]?.getD false = hi)
    (hwrite : writeAt T p false = T')
    (hnz : lo = true ∨ hi = true) :
    step runtimeMarkerDrivenClearMachine
        ⟨RuntimeMarkerDrivenClearState.hi lo, p, T⟩ =
      ⟨RuntimeMarkerDrivenClearState.lo, p + 1, T'⟩ := by
  cases lo <;> cases hi <;>
    simp_all [step, runtimeMarkerDrivenClearMachine, moveHead]

private theorem clear_hi_zero_step (T T' : List Bool) (p : Nat)
    (hread : T[p]?.getD false = false)
    (hwrite : writeAt T p false = T') :
    step runtimeMarkerDrivenClearMachine
        ⟨RuntimeMarkerDrivenClearState.hi false, p, T⟩ =
      ⟨RuntimeMarkerDrivenClearState.candidateLo, p + 1, T'⟩ := by
  simp [step, runtimeMarkerDrivenClearMachine, moveHead, hread, hwrite]

private theorem clear_candidateLo_step (T T' : List Bool) (p : Nat) (b : Bool)
    (hread : T[p]?.getD false = b) (hwrite : writeAt T p false = T') :
    step runtimeMarkerDrivenClearMachine
        ⟨RuntimeMarkerDrivenClearState.candidateLo, p, T⟩ =
      ⟨RuntimeMarkerDrivenClearState.candidateHi b, p + 1, T'⟩ := by
  simp [step, runtimeMarkerDrivenClearMachine, moveHead, hread, hwrite]

private theorem clear_candidateHi_nonzero_step (T T' : List Bool) (p : Nat)
    (lo hi : Bool) (hread : T[p]?.getD false = hi)
    (hwrite : writeAt T p false = T')
    (hnz : lo = true ∨ hi = true) :
    step runtimeMarkerDrivenClearMachine
        ⟨RuntimeMarkerDrivenClearState.candidateHi lo, p, T⟩ =
      ⟨RuntimeMarkerDrivenClearState.lo, p + 1, T'⟩ := by
  cases lo <;> cases hi <;>
    simp_all [step, runtimeMarkerDrivenClearMachine, moveHead]

private theorem clear_candidateHi_zero_step (T T' : List Bool) (p : Nat)
    (hread : T[p + 3]?.getD false = false)
    (hwrite : writeAt T (p + 3) false = T') :
    step runtimeMarkerDrivenClearMachine
        ⟨RuntimeMarkerDrivenClearState.candidateHi false, p + 3, T⟩ =
      ⟨RuntimeMarkerDrivenClearState.backOne, p + 2, T'⟩ := by
  simp [step, runtimeMarkerDrivenClearMachine, moveHead, hread, hwrite]

private theorem clear_backOne_step (T : List Bool) (p : Nat) :
    step runtimeMarkerDrivenClearMachine
        ⟨RuntimeMarkerDrivenClearState.backOne, p + 2, T⟩ =
      ⟨RuntimeMarkerDrivenClearState.backTwo, p + 1, T⟩ := by
  simp [step, runtimeMarkerDrivenClearMachine, moveHead]

private theorem clear_backTwo_step (T : List Bool) (p : Nat) :
    step runtimeMarkerDrivenClearMachine
        ⟨RuntimeMarkerDrivenClearState.backTwo, p + 1, T⟩ =
      ⟨RuntimeMarkerDrivenClearState.done, p, T⟩ := by
  simp [step, runtimeMarkerDrivenClearMachine, moveHead]

/-- One ordinary nonzero pair is read and destructively cleared in exactly
two transitions. -/
theorem runtimeMarkerDrivenClear_nonzero
    (pre tail : List Bool) (lo hi : Bool)
    (hnz : lo = true ∨ hi = true) :
    run runtimeMarkerDrivenClearMachine 2
        ⟨runtimeMarkerDrivenClearMachine.start, pre.length,
          pre ++ [lo, hi] ++ tail⟩ =
      ⟨runtimeMarkerDrivenClearMachine.start, pre.length + 2,
        pre ++ [false, false] ++ tail⟩ := by
  let T0 := pre ++ [lo, hi] ++ tail
  let T1 := pre ++ [false, hi] ++ tail
  let T2 := pre ++ [false, false] ++ tail
  have h0 : T0[pre.length]?.getD false = lo := by simp [T0]
  have h1 : T1[pre.length + 1]?.getD false = hi := by simp [T1]
  have hw0 : writeAt T0 pre.length false = T1 := by
    simpa [T0, T1, List.append_assoc] using
      write0 pre (hi :: tail) lo
  have hw1 : writeAt T1 (pre.length + 1) false = T2 := by
    simpa [T1, T2, List.append_assoc] using
      write0 (pre ++ [false]) tail hi
  change run runtimeMarkerDrivenClearMachine 2
      ⟨RuntimeMarkerDrivenClearState.lo, pre.length, T0⟩ =
    ⟨RuntimeMarkerDrivenClearState.lo, pre.length + 2, T2⟩
  rw [show run runtimeMarkerDrivenClearMachine 2
      ⟨RuntimeMarkerDrivenClearState.lo, pre.length, T0⟩ =
      step runtimeMarkerDrivenClearMachine
        (step runtimeMarkerDrivenClearMachine
          ⟨RuntimeMarkerDrivenClearState.lo, pre.length, T0⟩) by rfl]
  rw [clear_lo_step T0 T1 pre.length lo h0 hw0,
    clear_hi_nonzero_step T1 T2 (pre.length + 1) lo hi h1 hw1 hnz]

/-- A single `00` candidate followed by a nonzero pair is crossed and all
four inspected cells are cleared. -/
theorem runtimeMarkerDrivenClear_singleZero
    (pre tail : List Bool) (lo hi : Bool)
    (hnz : lo = true ∨ hi = true) :
    run runtimeMarkerDrivenClearMachine 4
        ⟨runtimeMarkerDrivenClearMachine.start, pre.length,
          pre ++ [false, false, lo, hi] ++ tail⟩ =
      ⟨runtimeMarkerDrivenClearMachine.start, pre.length + 4,
        pre ++ [false, false, false, false] ++ tail⟩ := by
  let T0 := pre ++ [false, false, lo, hi] ++ tail
  let T1 := pre ++ [false, false, false, hi] ++ tail
  let T2 := pre ++ [false, false, false, false] ++ tail
  have h0 : T0[pre.length]?.getD false = false := by simp [T0]
  have h1 : T0[pre.length + 1]?.getD false = false := by simp [T0]
  have h2 : T0[pre.length + 2]?.getD false = lo := by simp [T0]
  have h3 : T1[pre.length + 3]?.getD false = hi := by simp [T1]
  have hw0 : writeAt T0 pre.length false = T0 := by
    simpa [T0, List.append_assoc] using write0 pre
      (false :: lo :: hi :: tail) false
  have hw1 : writeAt T0 (pre.length + 1) false = T0 := by
    simpa [T0, List.append_assoc] using write0 (pre ++ [false])
      (lo :: hi :: tail) false
  have hw2 : writeAt T0 (pre.length + 2) false = T1 := by
    simpa [T0, T1, List.append_assoc] using write0
      (pre ++ [false, false]) (hi :: tail) lo
  have hw3 : writeAt T1 (pre.length + 3) false = T2 := by
    simpa [T1, T2, List.append_assoc] using write0
      (pre ++ [false, false, false]) tail hi
  change run runtimeMarkerDrivenClearMachine 4
      ⟨RuntimeMarkerDrivenClearState.lo, pre.length, T0⟩ =
    ⟨RuntimeMarkerDrivenClearState.lo, pre.length + 4, T2⟩
  rw [show run runtimeMarkerDrivenClearMachine 4
      ⟨RuntimeMarkerDrivenClearState.lo, pre.length, T0⟩ =
      step runtimeMarkerDrivenClearMachine
        (step runtimeMarkerDrivenClearMachine
          (step runtimeMarkerDrivenClearMachine
            (step runtimeMarkerDrivenClearMachine
              ⟨RuntimeMarkerDrivenClearState.lo, pre.length, T0⟩))) by rfl]
  rw [clear_lo_step T0 T0 pre.length false h0 hw0,
    clear_hi_zero_step T0 T0 (pre.length + 1) h1 hw1,
    clear_candidateLo_step T0 T1 (pre.length + 2) lo h2 hw2,
    clear_candidateHi_nonzero_step T1 T2 (pre.length + 3)
      lo hi h3 hw3 hnz]

/-- The reserved marker is cleared (idempotently), recognized, and the head
is returned to its first cell before the machine genuinely halts. -/
theorem runtimeMarkerDrivenClear_marker (pre tail : List Bool) :
    run runtimeMarkerDrivenClearMachine 6
        ⟨runtimeMarkerDrivenClearMachine.start, pre.length,
          pre ++ flattenPairs runtimePassedBoundaryMarker ++ tail⟩ =
      ⟨RuntimeMarkerDrivenClearState.done, pre.length,
        pre ++ flattenPairs runtimePassedBoundaryMarker ++ tail⟩ := by
  let T := pre ++ [false, false, false, false] ++ tail
  have h0 : T[pre.length]?.getD false = false := by simp [T]
  have h1 : T[pre.length + 1]?.getD false = false := by simp [T]
  have h2 : T[pre.length + 2]?.getD false = false := by simp [T]
  have h3 : T[pre.length + 3]?.getD false = false := by simp [T]
  have hw0 : writeAt T pre.length false = T := by
    simpa [T, List.append_assoc] using write0 pre
      (false :: false :: false :: tail) false
  have hw1 : writeAt T (pre.length + 1) false = T := by
    simpa [T, List.append_assoc] using write0 (pre ++ [false])
      (false :: false :: tail) false
  have hw2 : writeAt T (pre.length + 2) false = T := by
    simpa [T, List.append_assoc] using write0 (pre ++ [false, false])
      (false :: tail) false
  have hw3 : writeAt T (pre.length + 3) false = T := by
    simpa [T, List.append_assoc] using write0
      (pre ++ [false, false, false]) tail false
  change run runtimeMarkerDrivenClearMachine 6
      ⟨RuntimeMarkerDrivenClearState.lo, pre.length, T⟩ =
    ⟨RuntimeMarkerDrivenClearState.done, pre.length, T⟩
  rw [show run runtimeMarkerDrivenClearMachine 6
      ⟨RuntimeMarkerDrivenClearState.lo, pre.length, T⟩ =
      step runtimeMarkerDrivenClearMachine
        (step runtimeMarkerDrivenClearMachine
          (step runtimeMarkerDrivenClearMachine
            (step runtimeMarkerDrivenClearMachine
              (step runtimeMarkerDrivenClearMachine
                (step runtimeMarkerDrivenClearMachine
                  ⟨RuntimeMarkerDrivenClearState.lo, pre.length, T⟩))))) by rfl]
  rw [clear_lo_step T T pre.length false h0 hw0,
    clear_hi_zero_step T T (pre.length + 1) h1 hw1,
    clear_candidateLo_step T T (pre.length + 2) false h2 hw2,
    clear_candidateHi_zero_step T T pre.length h3 hw3,
    clear_backOne_step T pre.length, clear_backTwo_step T pre.length]

/-! ## Full pair-prefix runs -/

/-- A nonzero pair prefix is cleared by one uninterrupted run of the same
fixed controller. -/
theorem runtimeMarkerDrivenClear_nonzeroPairs
    (pre tail : List Bool) (ps : List (Bool × Bool))
    (hnz : ∀ p ∈ ps, p.1 = true ∨ p.2 = true) :
    run runtimeMarkerDrivenClearMachine (2 * ps.length)
        ⟨runtimeMarkerDrivenClearMachine.start, pre.length,
          pre ++ flattenPairs ps ++ tail⟩ =
      ⟨runtimeMarkerDrivenClearMachine.start,
        pre.length + 2 * ps.length,
        pre ++ List.replicate (2 * ps.length) false ++ tail⟩ := by
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
      have hfirst := runtimeMarkerDrivenClear_nonzero
        pre (flattenPairs ps ++ tail) lo hi hp
      have hfirst' : run runtimeMarkerDrivenClearMachine 2
          ⟨runtimeMarkerDrivenClearMachine.start, pre.length,
            pre ++ flattenPairs ((lo, hi) :: ps) ++ tail⟩ =
        ⟨runtimeMarkerDrivenClearMachine.start, pre.length + 2,
          pre ++ [false, false] ++ flattenPairs ps ++ tail⟩ := by
        simpa [flattenPairs, List.append_assoc] using hfirst
      rw [hfirst']
      have hih := ih (pre := pre ++ [false, false]) hrest
      convert hih using 1 <;>
        simp [List.replicate_add, List.append_assoc, Nat.add_assoc]

/-- A nonzero prefix is cleared and the following reserved marker is
recognized at the same exact clock as the read-only locator. -/
theorem runtimeMarkerDrivenClear_nonzeroPrefix_marker
    (pre tail : List Bool) (ps : List (Bool × Bool))
    (hnz : ∀ p ∈ ps, p.1 = true ∨ p.2 = true) :
    run runtimeMarkerDrivenClearMachine (2 * ps.length + 6)
        ⟨runtimeMarkerDrivenClearMachine.start, pre.length,
          pre ++ flattenPairs ps ++
            flattenPairs runtimePassedBoundaryMarker ++ tail⟩ =
      ⟨RuntimeMarkerDrivenClearState.done,
        pre.length + 2 * ps.length,
        pre ++ List.replicate (2 * ps.length) false ++
          flattenPairs runtimePassedBoundaryMarker ++ tail⟩ := by
  rw [run_add]
  have hp := runtimeMarkerDrivenClear_nonzeroPairs pre
    (flattenPairs runtimePassedBoundaryMarker ++ tail) ps hnz
  simp only [List.append_assoc] at hp ⊢
  rw [hp]
  have hm := runtimeMarkerDrivenClear_marker
    (pre ++ List.replicate (2 * ps.length) false) tail
  simpa [List.append_assoc, Nat.add_assoc] using hm

/-- The reachable false-value splice: an isolated zero pair is consumed
together with its guaranteed nonzero successor; every crossed cell becomes
part of one contiguous on-tape zero record. -/
theorem runtimeMarkerDrivenClear_isolatedZero_marker
    (pre tail : List Bool) (front rest : List (Bool × Bool))
    (q : Bool × Bool)
    (hfront : ∀ p ∈ front, p.1 = true ∨ p.2 = true)
    (hq : q.1 = true ∨ q.2 = true)
    (hrest : ∀ p ∈ rest, p.1 = true ∨ p.2 = true) :
    let ps := front ++ [(false, false), q] ++ rest
    run runtimeMarkerDrivenClearMachine (2 * ps.length + 6)
        ⟨runtimeMarkerDrivenClearMachine.start, pre.length,
          pre ++ flattenPairs ps ++
            flattenPairs runtimePassedBoundaryMarker ++ tail⟩ =
      ⟨RuntimeMarkerDrivenClearState.done,
        pre.length + 2 * ps.length,
        pre ++ List.replicate (2 * ps.length) false ++
          flattenPairs runtimePassedBoundaryMarker ++ tail⟩ := by
  dsimp only
  let Ttail := flattenPairs rest ++
    flattenPairs runtimePassedBoundaryMarker ++ tail
  rw [show 2 * (front ++ [(false, false), q] ++ rest).length + 6 =
      2 * front.length + (4 + (2 * rest.length + 6)) by simp; omega,
    run_add]
  have hp := runtimeMarkerDrivenClear_nonzeroPairs pre
    (flattenPairs [(false, false), q] ++ Ttail) front hfront
  have hp' : run runtimeMarkerDrivenClearMachine (2 * front.length)
      ⟨runtimeMarkerDrivenClearMachine.start, pre.length,
        pre ++ flattenPairs (front ++ [(false, false), q] ++ rest) ++
          flattenPairs runtimePassedBoundaryMarker ++ tail⟩ =
    ⟨runtimeMarkerDrivenClearMachine.start,
      pre.length + 2 * front.length,
      pre ++ List.replicate (2 * front.length) false ++
        flattenPairs [(false, false), q] ++ Ttail⟩ := by
    simpa [Ttail, flattenPairs_append, List.append_assoc] using hp
  rw [hp', run_add]
  have hz := runtimeMarkerDrivenClear_singleZero
    (pre ++ List.replicate (2 * front.length) false)
    (flattenPairs rest ++ flattenPairs runtimePassedBoundaryMarker ++ tail)
    q.1 q.2 hq
  rw [show run runtimeMarkerDrivenClearMachine 4
      ⟨runtimeMarkerDrivenClearMachine.start,
        pre.length + 2 * front.length,
        pre ++ List.replicate (2 * front.length) false ++
          flattenPairs [(false, false), q] ++ Ttail⟩ =
      ⟨runtimeMarkerDrivenClearMachine.start,
        pre.length + 2 * front.length + 4,
        pre ++ List.replicate (2 * front.length + 4) false ++ Ttail⟩ by
    rw [show List.replicate (2 * front.length + 4) false =
        List.replicate (2 * front.length) false ++
          [false, false, false, false] by
      rw [List.replicate_add]
      rfl]
    simpa [Ttail, flattenPairs, List.append_assoc, Nat.add_assoc] using hz]
  have hr := runtimeMarkerDrivenClear_nonzeroPrefix_marker
    (pre ++ List.replicate (2 * front.length + 4) false)
    tail rest hrest
  convert hr using 1 <;>
    simp [Ttail, List.append_assoc,
      Nat.add_assoc] <;> omega

/-- Complete destructive scan of the reachable workspace grammar.  At the
halt point the workspace is exactly a unary on-tape record of its own cell
length, while the reserved marker and everything to its right are intact. -/
theorem runtimeMarkerDrivenClear_workspace
    (pre tail : List Bool) (value : Bool) (m n : Nat) :
    let workspace := runtimeWorkspaceFrontPairs value m n
    run runtimeMarkerDrivenClearMachine (2 * workspace.length + 6)
        ⟨runtimeMarkerDrivenClearMachine.start, pre.length,
          pre ++ flattenPairs workspace ++
            flattenPairs runtimePassedBoundaryMarker ++ tail⟩ =
      ⟨RuntimeMarkerDrivenClearState.done,
        pre.length + 2 * workspace.length,
        pre ++ List.replicate (2 * workspace.length) false ++
          flattenPairs runtimePassedBoundaryMarker ++ tail⟩ := by
  dsimp only
  cases value
  · cases m with
    | zero =>
        let front : List (Bool × Bool) :=
          [(true, false), (false, true)]
        let q : Bool × Bool := (false, true)
        let rest := List.replicate n (true, true)
        have hf : ∀ p ∈ front, p.1 = true ∨ p.2 = true := by
          intro p hp
          simp [front] at hp
          rcases hp with rfl | rfl <;> simp
        have hq : q.1 = true ∨ q.2 = true := by simp [q]
        have hr : ∀ p ∈ rest, p.1 = true ∨ p.2 = true := by
          intro p hp
          simp [rest] at hp
          rcases hp with ⟨_, rfl⟩
          simp
        simpa [runtimeWorkspaceFrontPairs, front, q, rest,
          List.append_assoc] using
          runtimeMarkerDrivenClear_isolatedZero_marker
            pre tail front rest q hf hq hr
    | succ k =>
        let front : List (Bool × Bool) :=
          [(true, false), (false, true)]
        let q : Bool × Bool := (true, false)
        let rest := List.replicate k (true, false) ++
          [(false, true)] ++ List.replicate n (true, true)
        have hf : ∀ p ∈ front, p.1 = true ∨ p.2 = true := by
          intro p hp
          simp [front] at hp
          rcases hp with rfl | rfl <;> simp
        have hq : q.1 = true ∨ q.2 = true := by simp [q]
        have hr : ∀ p ∈ rest, p.1 = true ∨ p.2 = true := by
          intro p hp
          simp [rest] at hp
          rcases hp with h | h | h
          · rcases h with ⟨_, rfl⟩; simp
          · subst p; simp
          · rcases h with ⟨_, rfl⟩; simp
        simpa [runtimeWorkspaceFrontPairs, front, q, rest,
          List.replicate_succ, List.append_assoc] using
          runtimeMarkerDrivenClear_isolatedZero_marker
            pre tail front rest q hf hq hr
  · have hall : ∀ p ∈ runtimeWorkspaceFrontPairs true m n,
        p.1 = true ∨ p.2 = true := by
      intro p hp
      simp [runtimeWorkspaceFrontPairs] at hp
      rcases hp with h | h | h | h
      · subst p; simp
      · subst p; simp
      · subst p; simp
      · rcases h with ⟨_, rfl⟩ | rfl | ⟨_, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact Or.inl rfl
    exact runtimeMarkerDrivenClear_nonzeroPrefix_marker pre tail
      (runtimeWorkspaceFrontPairs true m n) hall

/-! ## Structural left safety -/

def RuntimeMarkerDrivenClearHeadInvariant
    (c : Cfg runtimeMarkerDrivenClearMachine) : Prop :=
  match c.st with
  | .lo | .done => True
  | .hi _ => 1 ≤ c.hd
  | .candidateLo => 2 ≤ c.hd
  | .candidateHi _ => 3 ≤ c.hd
  | .backOne => 2 ≤ c.hd
  | .backTwo => 1 ≤ c.hd

theorem runtimeMarkerDrivenClear_invariant_step
    (c : Cfg runtimeMarkerDrivenClearMachine)
    (h : RuntimeMarkerDrivenClearHeadInvariant c) :
    RuntimeMarkerDrivenClearHeadInvariant
      (step runtimeMarkerDrivenClearMachine c) := by
  cases hs : c.st with
  | lo | candidateLo | done =>
      simp_all [RuntimeMarkerDrivenClearHeadInvariant, step,
        runtimeMarkerDrivenClearMachine, moveHead]
  | backOne =>
      simp_all [RuntimeMarkerDrivenClearHeadInvariant, step,
        runtimeMarkerDrivenClearMachine, moveHead]
      omega
  | backTwo =>
      simp_all [RuntimeMarkerDrivenClearHeadInvariant, step,
        runtimeMarkerDrivenClearMachine, moveHead]
  | hi loBit | candidateHi loBit =>
      generalize hb : c.tp[c.hd]?.getD false = b
      cases loBit <;> cases b <;>
        simp_all [RuntimeMarkerDrivenClearHeadInvariant, step,
          runtimeMarkerDrivenClearMachine, moveHead] <;> omega

theorem runtimeMarkerDrivenClear_invariant_run
    (c : Cfg runtimeMarkerDrivenClearMachine)
    (h : RuntimeMarkerDrivenClearHeadInvariant c) (n : Nat) :
    RuntimeMarkerDrivenClearHeadInvariant
      (run runtimeMarkerDrivenClearMachine n c) := by
  induction n with
  | zero => simpa
  | succ n ih =>
      rw [run_succ]
      exact runtimeMarkerDrivenClear_invariant_step _ ih

theorem runtimeMarkerDrivenClear_leftSafe
    (c : Cfg runtimeMarkerDrivenClearMachine)
    (h : RuntimeMarkerDrivenClearHeadInvariant c) (n : Nat) :
    LeftSafeRun runtimeMarkerDrivenClearMachine c n := by
  intro i hi hhalt hmove
  have hinv := runtimeMarkerDrivenClear_invariant_run c h i
  generalize hs : (run runtimeMarkerDrivenClearMachine i c).st = s at hinv hmove
  cases s <;>
    simp_all [RuntimeMarkerDrivenClearHeadInvariant,
      runtimeMarkerDrivenClearMachine] <;> omega

theorem runtimeMarkerDrivenClear_workspace_leftSafe
    (pre tail : List Bool) (value : Bool) (m n : Nat) :
    let workspace := runtimeWorkspaceFrontPairs value m n
    LeftSafeRun runtimeMarkerDrivenClearMachine
      ⟨runtimeMarkerDrivenClearMachine.start, pre.length,
        pre ++ flattenPairs workspace ++
          flattenPairs runtimePassedBoundaryMarker ++ tail⟩
      (2 * workspace.length + 6) := by
  dsimp only
  apply runtimeMarkerDrivenClear_leftSafe
  simp [RuntimeMarkerDrivenClearHeadInvariant,
    runtimeMarkerDrivenClearMachine]

@[simp] theorem runtimeMarkerDrivenClear_done_halts :
    runtimeMarkerDrivenClearMachine.halt
      RuntimeMarkerDrivenClearState.done = true := by
  simp [runtimeMarkerDrivenClearMachine]

#print axioms runtimeMarkerDrivenClear_nonzero
#print axioms runtimeMarkerDrivenClear_singleZero
#print axioms runtimeMarkerDrivenClear_marker
#print axioms runtimeMarkerDrivenClear_nonzeroPairs
#print axioms runtimeMarkerDrivenClear_nonzeroPrefix_marker
#print axioms runtimeMarkerDrivenClear_isolatedZero_marker
#print axioms runtimeMarkerDrivenClear_workspace
#print axioms runtimeMarkerDrivenClear_invariant_step
#print axioms runtimeMarkerDrivenClear_leftSafe
#print axioms runtimeMarkerDrivenClear_workspace_leftSafe

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeMarkerDrivenClear
