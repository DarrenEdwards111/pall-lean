import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeFixedCleanupScheduled
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeSourceCompact

/-!
# Fixed relocation from compacted cleanup to the remaining archive

The fixed cleanup controller halts near the new left edge.  The archive-return
controller starts at the first cell of the remaining `selectedTail`.  This
module supplies the missing fixed, tape-driven relocation.  It crosses the
canonical passed block and the physical `00` hole record, then recognizes the
unique `10` header of the first fresh archive block and backs up to its low
cell.  No length or schedule index occurs in finite control.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeFixedContinuationRelocator

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceCompact
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryTerminal

inductive RuntimeFixedContinuationRelocatorState
  | boot1 | boot2 | boot3
  | lo
  | hi (loBit : Bool)
  | back
  | done
  deriving DecidableEq, Fintype

open RuntimeFixedContinuationRelocatorState

/-- Constant-state scanner from the cleanup halt geometry to the first fresh
archive header. -/
def runtimeFixedContinuationRelocatorMachine : Machine where
  State := RuntimeFixedContinuationRelocatorState
  fin := inferInstance
  dec := inferInstance
  start := .boot1
  halt := fun s => decide (s = .done)
  δ := fun s b =>
    match s with
    | .boot1 => (.boot2, none, 1)
    | .boot2 => (.boot3, none, 1)
    | .boot3 => (.lo, none, 1)
    | .lo => (.hi b, none, 1)
    | .hi loBit =>
        if loBit && !b then (.back, none, 0)
        else (.lo, none, 1)
    | .back => (.done, none, 2)
    | .done => (.done, none, 2)
  accept := fun _ => false

def runtimeFixedContinuationRelocatorClock
    (bits : List Bool) (holes : Nat) : Nat :=
  3 + 2 * (passedSourceBlock bits).length + 2 * holes + 3

theorem runtimeFixedContinuationRelocator_boot
    (T : List Bool) (p : Nat) :
    run runtimeFixedContinuationRelocatorMachine 3
        ⟨boot1, p, T⟩ = ⟨lo, p + 3, T⟩ := by
  simp [run_succ, step, runtimeFixedContinuationRelocatorMachine, moveHead]

theorem runtimeFixedContinuationRelocator_pair
    (pre tail : List Bool) (pair : Bool × Bool)
    (hpair : pair ≠ (true, false)) :
    run runtimeFixedContinuationRelocatorMachine 2
        ⟨lo, pre.length, pre ++ flattenPairs [pair] ++ tail⟩ =
      ⟨lo, pre.length + 2, pre ++ flattenPairs [pair] ++ tail⟩ := by
  rcases pair with ⟨a, b⟩
  cases a <;> cases b <;>
    simp_all [run_succ, step, runtimeFixedContinuationRelocatorMachine,
      moveHead, flattenPairs, List.getD_eq_getElem?_getD]

theorem runtimeFixedContinuationRelocator_pairs
    (pre tail : List Bool) (pairs : List (Bool × Bool))
    (hno : ∀ p ∈ pairs, p ≠ (true, false)) :
    run runtimeFixedContinuationRelocatorMachine (2 * pairs.length)
        ⟨lo, pre.length, pre ++ flattenPairs pairs ++ tail⟩ =
      ⟨lo, pre.length + 2 * pairs.length,
        pre ++ flattenPairs pairs ++ tail⟩ := by
  induction pairs generalizing pre with
  | nil => simp
  | cons p ps ih =>
      have hp := hno p (by simp)
      have hps : ∀ q ∈ ps, q ≠ (true, false) := by
        intro q hq
        exact hno q (by simp [hq])
      rw [show 2 * (p :: ps).length = 2 + 2 * ps.length by simp; omega,
        run_add]
      have hone := runtimeFixedContinuationRelocator_pair pre
        (flattenPairs ps ++ tail) p hp
      have hone' : run runtimeFixedContinuationRelocatorMachine 2
          ⟨lo, pre.length,
            pre ++ flattenPairs [p] ++ flattenPairs ps ++ tail⟩ =
        ⟨lo, pre.length + 2,
          pre ++ flattenPairs [p] ++ flattenPairs ps ++ tail⟩ := by
        simpa [List.append_assoc] using hone
      rw [show pre ++ flattenPairs (p :: ps) ++ tail =
          (pre ++ flattenPairs [p]) ++ flattenPairs ps ++ tail by
        simp [flattenPairs, List.append_assoc], hone']
      have hrec := ih (pre ++ flattenPairs [p]) hps
      simpa [flattenPairs, List.append_assoc, Nat.add_assoc] using hrec

theorem passedSourceBlock_has_no_freshHeader (bits : List Bool) :
    ∀ p ∈ passedSourceBlock bits, p ≠ (true, false) := by
  intro p hp heq
  subst p
  simp [passedSourceBlock, dataPairs] at hp

theorem runtimeFixedContinuationRelocator_header
    (pre tail : List Bool) :
    run runtimeFixedContinuationRelocatorMachine 3
        ⟨lo, pre.length, pre ++ [true, false] ++ tail⟩ =
      ⟨done, pre.length, pre ++ [true, false] ++ tail⟩ := by
  simp [run_succ, step, runtimeFixedContinuationRelocatorMachine, moveHead,
    List.getD_eq_getElem?_getD]

/-- Exact relocation across the canonical passed block and every physical
cleanup hole, stopping at the low cell of the first fresh archive header. -/
theorem runtimeFixedContinuationRelocator_passed_holes
    (pre bits first : List Bool) (more : List (List Bool)) (holes : Nat) :
    let prefixPairs := passedSourceBlock bits ++
      List.replicate holes (false, false)
    let tape := pre ++ [false, false, false, false] ++
      flattenPairs prefixPairs ++ selectedTail (first :: more)
    run runtimeFixedContinuationRelocatorMachine
        (runtimeFixedContinuationRelocatorClock bits holes)
        ⟨runtimeFixedContinuationRelocatorMachine.start,
          pre.length + 1, tape⟩ =
      ⟨done, pre.length + 4 + 2 * prefixPairs.length, tape⟩ := by
  dsimp only
  let prefixPairs := passedSourceBlock bits ++
    List.replicate holes (false, false)
  let physicalPrefix := pre ++ [false, false, false, false]
  let tail := selectedTail (first :: more)
  have hno : ∀ p ∈ prefixPairs, p ≠ (true, false) := by
    intro p hp
    simp only [prefixPairs, List.mem_append] at hp
    rcases hp with hp | hp
    · exact passedSourceBlock_has_no_freshHeader bits p hp
    · have : p = (false, false) := (List.mem_replicate.mp hp).2
      simp [this]
  rw [show runtimeFixedContinuationRelocatorClock bits holes =
      3 + (2 * prefixPairs.length + 3) by
    simp [runtimeFixedContinuationRelocatorClock, prefixPairs]; omega,
    run_add]
  have hboot : run runtimeFixedContinuationRelocatorMachine 3
      ⟨runtimeFixedContinuationRelocatorMachine.start,
        pre.length + 1,
        pre ++ [false, false, false, false] ++
          flattenPairs prefixPairs ++ tail⟩ =
    ⟨lo, physicalPrefix.length,
      physicalPrefix ++ flattenPairs prefixPairs ++ tail⟩ := by
    simpa [runtimeFixedContinuationRelocatorMachine, physicalPrefix,
      List.append_assoc] using
      runtimeFixedContinuationRelocator_boot
        (pre ++ [false, false, false, false] ++
          flattenPairs prefixPairs ++ tail) (pre.length + 1)
  rw [hboot]
  have hpairs := runtimeFixedContinuationRelocator_pairs physicalPrefix tail
    prefixPairs hno
  rw [show 2 * prefixPairs.length + 3 =
      2 * prefixPairs.length + 3 by rfl,
    run_add, hpairs]
  have hheader := runtimeFixedContinuationRelocator_header
    (physicalPrefix ++ flattenPairs prefixPairs)
    (flattenPairs (dataPairs first ++ [(false, true)]) ++ selectedTail more)
  convert hheader using 1 <;>
    simp [tail, selectedTail, freshSourceBlock, flattenPairs,
      flattenPairs_append, prefixPairs, List.append_assoc, physicalPrefix,
      flattenPairs_length, Nat.add_assoc] <;> try omega
  congr 2
  omega

/-! ## Structural left safety -/

def RuntimeFixedContinuationRelocatorHeadInvariant
    (c : Cfg runtimeFixedContinuationRelocatorMachine) : Prop :=
  match c.st with
  | .hi _ => 0 < c.hd
  | _ => True

theorem runtimeFixedContinuationRelocator_invariant_step
    (c : Cfg runtimeFixedContinuationRelocatorMachine)
    (h : RuntimeFixedContinuationRelocatorHeadInvariant c) :
    RuntimeFixedContinuationRelocatorHeadInvariant
      (step runtimeFixedContinuationRelocatorMachine c) := by
  rcases c with ⟨st, hd, tp⟩
  cases st with
  | hi loBit =>
      cases hb : tp[hd]?.getD false <;> cases loBit <;>
        simp_all [RuntimeFixedContinuationRelocatorHeadInvariant, step,
          runtimeFixedContinuationRelocatorMachine, moveHead]
  | boot1 | boot2 | boot3 | lo | back | done =>
      simp_all [RuntimeFixedContinuationRelocatorHeadInvariant, step,
        runtimeFixedContinuationRelocatorMachine, moveHead]

theorem runtimeFixedContinuationRelocator_invariant_run
    (c : Cfg runtimeFixedContinuationRelocatorMachine)
    (h : RuntimeFixedContinuationRelocatorHeadInvariant c) (n : Nat) :
    RuntimeFixedContinuationRelocatorHeadInvariant
      (run runtimeFixedContinuationRelocatorMachine n c) := by
  induction n with
  | zero => simpa
  | succ n ih =>
      rw [run_succ]
      exact runtimeFixedContinuationRelocator_invariant_step _ ih

theorem runtimeFixedContinuationRelocator_leftSafe
    (c : Cfg runtimeFixedContinuationRelocatorMachine)
    (h : RuntimeFixedContinuationRelocatorHeadInvariant c) (n : Nat) :
    LeftSafeRun runtimeFixedContinuationRelocatorMachine c n := by
  intro i hi hhalt hmove
  have hinv := runtimeFixedContinuationRelocator_invariant_run c h i
  generalize hs : (run runtimeFixedContinuationRelocatorMachine i c).st = s
    at hinv hhalt hmove
  generalize hb : (run runtimeFixedContinuationRelocatorMachine i c).tp.getD
      (run runtimeFixedContinuationRelocatorMachine i c).hd false = b at hmove
  cases b <;> cases s <;>
    simp_all [RuntimeFixedContinuationRelocatorHeadInvariant,
      runtimeFixedContinuationRelocatorMachine]

theorem runtimeFixedContinuationRelocator_passed_holes_leftSafe
    (pre bits first : List Bool) (more : List (List Bool)) (holes : Nat) :
    let prefixPairs := passedSourceBlock bits ++
      List.replicate holes (false, false)
    let tape := pre ++ [false, false, false, false] ++
      flattenPairs prefixPairs ++ selectedTail (first :: more)
    LeftSafeRun runtimeFixedContinuationRelocatorMachine
      ⟨runtimeFixedContinuationRelocatorMachine.start,
        pre.length + 1, tape⟩
      (runtimeFixedContinuationRelocatorClock bits holes) := by
  dsimp only
  apply runtimeFixedContinuationRelocator_leftSafe
  simp [RuntimeFixedContinuationRelocatorHeadInvariant,
    runtimeFixedContinuationRelocatorMachine]

#print axioms runtimeFixedContinuationRelocator_passed_holes
#print axioms runtimeFixedContinuationRelocator_passed_holes_leftSafe

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeFixedContinuationRelocator
