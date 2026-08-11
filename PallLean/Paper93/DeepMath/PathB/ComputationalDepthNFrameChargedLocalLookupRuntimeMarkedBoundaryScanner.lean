import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimePreservedPassedCopy

/-!
# Fixed scanner for the preserved passed-block boundary

This controller scans aligned pairs without writing.  A single `00` is held
as a candidate and checked against the following pair.  Two consecutive
`00` pairs are the reserved boundary; the scanner rewinds to its first cell
and halts there.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeMarkedBoundaryScanner

set_option maxHeartbeats 4000000

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundEntryAdapter
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePreservedPassedCopy
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryTerminal

inductive RuntimeMarkedBoundaryScanState
  | lo
  | hi (loBit : Bool)
  | candidateLo
  | candidateHi (loBit : Bool)
  | backOne
  | backTwo
  | done
  deriving DecidableEq, Fintype

/-- Fixed finite-state pair scanner.  Its state type is independent of every
payload, offset, schedule, round, and tape length. -/
def runtimeMarkedBoundaryScanMachine : Machine where
  State := RuntimeMarkedBoundaryScanState
  fin := inferInstance
  dec := inferInstance
  start := .lo
  halt := fun s => decide (s = .done)
  δ := fun s b =>
    match s with
    | .lo => (.hi b, none, 1)
    | .hi loBit =>
        if !loBit && !b then (.candidateLo, none, 1)
        else (.lo, none, 1)
    | .candidateLo => (.candidateHi b, none, 1)
    | .candidateHi loBit =>
        if !loBit && !b then (.backOne, none, 0)
        else (.lo, none, 1)
    | .backOne => (.backTwo, none, 0)
    | .backTwo => (.done, none, 0)
    | .done => (.done, none, 2)
  accept := fun _ => false

private theorem scan_lo_step (T : List Bool) (p : Nat) (b : Bool)
    (h : T[p]?.getD false = b) :
    step runtimeMarkedBoundaryScanMachine
        ⟨RuntimeMarkedBoundaryScanState.lo, p, T⟩ =
      ⟨RuntimeMarkedBoundaryScanState.hi b, p + 1, T⟩ := by
  simp [step, runtimeMarkedBoundaryScanMachine, moveHead, h]

private theorem scan_hi_nonzero_step (T : List Bool) (p : Nat)
    (lo hi : Bool) (hread : T[p]?.getD false = hi)
    (hnz : lo = true ∨ hi = true) :
    step runtimeMarkedBoundaryScanMachine
        ⟨RuntimeMarkedBoundaryScanState.hi lo, p, T⟩ =
      ⟨RuntimeMarkedBoundaryScanState.lo, p + 1, T⟩ := by
  cases lo <;> cases hi <;>
    simp_all [step, runtimeMarkedBoundaryScanMachine, moveHead]

private theorem scan_hi_zero_step (T : List Bool) (p : Nat)
    (hread : T[p]?.getD false = false) :
    step runtimeMarkedBoundaryScanMachine
        ⟨RuntimeMarkedBoundaryScanState.hi false, p, T⟩ =
      ⟨RuntimeMarkedBoundaryScanState.candidateLo, p + 1, T⟩ := by
  simp [step, runtimeMarkedBoundaryScanMachine, moveHead, hread]

private theorem scan_candidateLo_step (T : List Bool) (p : Nat) (b : Bool)
    (hread : T[p]?.getD false = b) :
    step runtimeMarkedBoundaryScanMachine
        ⟨RuntimeMarkedBoundaryScanState.candidateLo, p, T⟩ =
      ⟨RuntimeMarkedBoundaryScanState.candidateHi b, p + 1, T⟩ := by
  simp [step, runtimeMarkedBoundaryScanMachine, moveHead, hread]

private theorem scan_candidateHi_nonzero_step (T : List Bool) (p : Nat)
    (lo hi : Bool) (hread : T[p]?.getD false = hi)
    (hnz : lo = true ∨ hi = true) :
    step runtimeMarkedBoundaryScanMachine
        ⟨RuntimeMarkedBoundaryScanState.candidateHi lo, p, T⟩ =
      ⟨RuntimeMarkedBoundaryScanState.lo, p + 1, T⟩ := by
  cases lo <;> cases hi <;>
    simp_all [step, runtimeMarkedBoundaryScanMachine, moveHead]

private theorem scan_candidateHi_zero_step (T : List Bool) (p : Nat)
    (hread : T[p + 3]?.getD false = false) :
    step runtimeMarkedBoundaryScanMachine
        ⟨RuntimeMarkedBoundaryScanState.candidateHi false, p + 3, T⟩ =
      ⟨RuntimeMarkedBoundaryScanState.backOne, p + 2, T⟩ := by
  simp [step, runtimeMarkedBoundaryScanMachine, moveHead, hread]

private theorem scan_backOne_step (T : List Bool) (p : Nat) :
    step runtimeMarkedBoundaryScanMachine
        ⟨RuntimeMarkedBoundaryScanState.backOne, p + 2, T⟩ =
      ⟨RuntimeMarkedBoundaryScanState.backTwo, p + 1, T⟩ := by
  simp [step, runtimeMarkedBoundaryScanMachine, moveHead]

private theorem scan_backTwo_step (T : List Bool) (p : Nat) :
    step runtimeMarkedBoundaryScanMachine
        ⟨RuntimeMarkedBoundaryScanState.backTwo, p + 1, T⟩ =
      ⟨RuntimeMarkedBoundaryScanState.done, p, T⟩ := by
  simp [step, runtimeMarkedBoundaryScanMachine, moveHead]

/-- One ordinary nonzero pair is crossed in two transitions. -/
theorem runtimeMarkedBoundaryScan_nonzero
    (pre tail : List Bool) (lo hi : Bool) (hnz : lo = true ∨ hi = true) :
    run runtimeMarkedBoundaryScanMachine 2
        ⟨runtimeMarkedBoundaryScanMachine.start, pre.length,
          pre ++ [lo, hi] ++ tail⟩ =
      ⟨runtimeMarkedBoundaryScanMachine.start, pre.length + 2,
        pre ++ [lo, hi] ++ tail⟩ := by
  let T := pre ++ [lo, hi] ++ tail
  have hlo : T[pre.length]?.getD false = lo := by simp [T]
  have hhi : T[pre.length + 1]?.getD false = hi := by simp [T]
  rw [show run runtimeMarkedBoundaryScanMachine 2
      ⟨runtimeMarkedBoundaryScanMachine.start, pre.length, T⟩ =
      step runtimeMarkedBoundaryScanMachine
        (step runtimeMarkedBoundaryScanMachine
          ⟨RuntimeMarkedBoundaryScanState.lo, pre.length, T⟩) by rfl]
  rw [scan_lo_step T pre.length lo hlo,
    scan_hi_nonzero_step T (pre.length + 1) lo hi hhi hnz]
  rfl

/-- A single zero pair followed by a nonzero pair is crossed as one
four-transition candidate-check segment. -/
theorem runtimeMarkedBoundaryScan_singleZero
    (pre tail : List Bool) (lo hi : Bool) (hnz : lo = true ∨ hi = true) :
    run runtimeMarkedBoundaryScanMachine 4
        ⟨runtimeMarkedBoundaryScanMachine.start, pre.length,
          pre ++ [false, false, lo, hi] ++ tail⟩ =
      ⟨runtimeMarkedBoundaryScanMachine.start, pre.length + 4,
        pre ++ [false, false, lo, hi] ++ tail⟩ := by
  let T := pre ++ [false, false, lo, hi] ++ tail
  have h0 : T[pre.length]?.getD false = false := by simp [T]
  have h1 : T[pre.length + 1]?.getD false = false := by simp [T]
  have hlo : T[pre.length + 2]?.getD false = lo := by simp [T]
  have hhi : T[pre.length + 3]?.getD false = hi := by simp [T]
  rw [show run runtimeMarkedBoundaryScanMachine 4
      ⟨runtimeMarkedBoundaryScanMachine.start, pre.length, T⟩ =
      step runtimeMarkedBoundaryScanMachine
        (step runtimeMarkedBoundaryScanMachine
          (step runtimeMarkedBoundaryScanMachine
            (step runtimeMarkedBoundaryScanMachine
              ⟨RuntimeMarkedBoundaryScanState.lo, pre.length, T⟩))) by rfl]
  rw [scan_lo_step T pre.length false h0,
    scan_hi_zero_step T (pre.length + 1) h1,
    scan_candidateLo_step T (pre.length + 2) lo hlo,
    scan_candidateHi_nonzero_step T (pre.length + 3) lo hi hhi hnz]
  rfl

/-- On the reserved marker the scanner genuinely halts, with the head
returned to the marker's first low cell and the entire tape unchanged. -/
theorem runtimeMarkedBoundaryScan_marker (pre tail : List Bool) :
    run runtimeMarkedBoundaryScanMachine 6
        ⟨runtimeMarkedBoundaryScanMachine.start, pre.length,
          pre ++ flattenPairs runtimePassedBoundaryMarker ++ tail⟩ =
      ⟨RuntimeMarkedBoundaryScanState.done, pre.length,
        pre ++ flattenPairs runtimePassedBoundaryMarker ++ tail⟩ := by
  let T := pre ++ [false, false, false, false] ++ tail
  have h0 : T[pre.length]?.getD false = false := by simp [T]
  have h1 : T[pre.length + 1]?.getD false = false := by simp [T]
  have h2 : T[pre.length + 2]?.getD false = false := by simp [T]
  have h3 : T[pre.length + 3]?.getD false = false := by simp [T]
  change run runtimeMarkedBoundaryScanMachine 6
      ⟨RuntimeMarkedBoundaryScanState.lo, pre.length, T⟩ =
    ⟨RuntimeMarkedBoundaryScanState.done, pre.length, T⟩
  rw [show run runtimeMarkedBoundaryScanMachine 6
      ⟨RuntimeMarkedBoundaryScanState.lo, pre.length, T⟩ =
      step runtimeMarkedBoundaryScanMachine
        (step runtimeMarkedBoundaryScanMachine
          (step runtimeMarkedBoundaryScanMachine
            (step runtimeMarkedBoundaryScanMachine
              (step runtimeMarkedBoundaryScanMachine
                (step runtimeMarkedBoundaryScanMachine
                  ⟨RuntimeMarkedBoundaryScanState.lo, pre.length, T⟩))))) by rfl]
  rw [scan_lo_step T pre.length false h0,
    scan_hi_zero_step T (pre.length + 1) h1,
    scan_candidateLo_step T (pre.length + 2) false h2,
    scan_candidateHi_zero_step T pre.length h3,
    scan_backOne_step T pre.length, scan_backTwo_step T pre.length]

/-! ## Complete fixed scan over the workspace grammar -/

/-- A list containing no zero pair is crossed at exactly two transitions per
pair, with one fixed scanner state reused at every boundary. -/
theorem runtimeMarkedBoundaryScan_nonzeroPairs
    (pre tail : List Bool) (ps : List (Bool × Bool))
    (hnz : ∀ p ∈ ps, p.1 = true ∨ p.2 = true) :
    run runtimeMarkedBoundaryScanMachine (2 * ps.length)
        ⟨runtimeMarkedBoundaryScanMachine.start, pre.length,
          pre ++ flattenPairs ps ++ tail⟩ =
      ⟨runtimeMarkedBoundaryScanMachine.start,
        pre.length + 2 * ps.length,
        pre ++ flattenPairs ps ++ tail⟩ := by
  induction ps generalizing pre with
  | nil => simp
  | cons p ps ih =>
      have hp : p.1 = true ∨ p.2 = true := hnz p (by simp)
      have hrest : ∀ q ∈ ps, q.1 = true ∨ q.2 = true := by
        intro q hq
        exact hnz q (by simp [hq])
      rw [show 2 * (p :: ps).length = 2 + 2 * ps.length by simp; omega,
        run_add]
      have hfirst := runtimeMarkedBoundaryScan_nonzero
        pre (flattenPairs ps ++ tail) p.1 p.2 hp
      rw [show flattenPairs (p :: ps) = [p.1, p.2] ++
          flattenPairs ps by cases p; rfl]
      simp only [List.append_assoc] at hfirst ⊢
      rw [hfirst]
      have hih := ih (pre := pre ++ [p.1, p.2]) hrest
      simpa [List.append_assoc, Nat.add_assoc] using hih

/-- Nonzero pairs followed by the reserved marker scan to one genuine halt
at the marker origin. -/
theorem runtimeMarkedBoundaryScan_nonzeroPrefix_marker
    (pre tail : List Bool) (ps : List (Bool × Bool))
    (hnz : ∀ p ∈ ps, p.1 = true ∨ p.2 = true) :
    run runtimeMarkedBoundaryScanMachine (2 * ps.length + 6)
        ⟨runtimeMarkedBoundaryScanMachine.start, pre.length,
          pre ++ flattenPairs ps ++
            flattenPairs runtimePassedBoundaryMarker ++ tail⟩ =
      ⟨RuntimeMarkedBoundaryScanState.done,
        pre.length + 2 * ps.length,
        pre ++ flattenPairs ps ++
          flattenPairs runtimePassedBoundaryMarker ++ tail⟩ := by
  rw [run_add]
  have hp := runtimeMarkedBoundaryScan_nonzeroPairs pre
    (flattenPairs runtimePassedBoundaryMarker ++ tail) ps hnz
  simp only [List.append_assoc] at hp ⊢
  rw [hp]
  have hm := runtimeMarkedBoundaryScan_marker
    (pre ++ flattenPairs ps) tail
  simpa [List.append_assoc, Nat.add_assoc] using hm

@[simp] theorem runtimeMarkedBoundaryScan_done_halts :
    runtimeMarkedBoundaryScanMachine.halt
      RuntimeMarkedBoundaryScanState.done = true := by
  simp [runtimeMarkedBoundaryScanMachine]

#print axioms runtimeMarkedBoundaryScan_nonzero
#print axioms runtimeMarkedBoundaryScan_singleZero
#print axioms runtimeMarkedBoundaryScan_marker
#print axioms runtimeMarkedBoundaryScan_nonzeroPairs
#print axioms runtimeMarkedBoundaryScan_nonzeroPrefix_marker

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeMarkedBoundaryScanner
