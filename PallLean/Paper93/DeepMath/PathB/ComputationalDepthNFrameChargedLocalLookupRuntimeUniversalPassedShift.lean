import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeMarkerDrivenClear
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeCompactChain

/-!
# Universal passed-block hole pass

The canonical passed block is self-delimiting in pair grammar:
`11 · (00|11)* · 01`.  This controller bubbles one aligned `00` hole right
through the block and halts only after moving the terminal `01` pair.  Thus
the block length is read from tape and is absent from the finite state type.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeUniversalPassedShift

set_option maxHeartbeats 4000000

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeCompactChain
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryTerminal

inductive RuntimeUniversalPassedShiftState
  | holeLo | holeHi | readLo | readHi (lo : Bool)
  | clearLo (lo hi terminal : Bool)
  | writeHi (lo hi terminal : Bool)
  | writeLo (lo terminal : Bool)
  | advance (terminal : Bool)
  | done
  deriving DecidableEq, Fintype

/-- Fixed one-hole pass.  The terminal flag records whether the pair just
read was the canonical closing `01`; it is one bit, not a span counter. -/
def runtimeUniversalPassedShiftMachine : Machine where
  State := RuntimeUniversalPassedShiftState
  fin := inferInstance
  dec := inferInstance
  start := .holeLo
  halt := fun s => decide (s = .done)
  δ := fun s b =>
    match s with
    | .holeLo => (.holeHi, none, 1)
    | .holeHi => (.readLo, none, 1)
    | .readLo => (.readHi b, none, 1)
    | .readHi lo =>
        let terminal := !lo && b
        (.clearLo lo b terminal, some false, 0)
    | .clearLo lo hi terminal =>
        (.writeHi lo hi terminal, some false, 0)
    | .writeHi lo hi terminal =>
        (.writeLo lo terminal, some hi, 0)
    | .writeLo lo terminal =>
        (.advance terminal, some lo, 1)
    | .advance terminal =>
        if terminal then (.done, none, 1) else (.holeLo, none, 1)
    | .done => (.done, none, 2)
  accept := fun _ => false

private theorem shift_write0 (pre tail : List Bool) (lo hi : Bool) :
    writeAt (pre ++ [false, false, lo, hi] ++ tail)
      (pre.length + 3) false =
      pre ++ [false, false, lo, false] ++ tail := by
  rw [PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr.writeAt_of_lt
    false (by simp)]
  simp

private theorem shift_write1 (pre tail : List Bool) (lo : Bool) :
    writeAt (pre ++ [false, false, lo, false] ++ tail)
      (pre.length + 2) false =
      pre ++ [false, false, false, false] ++ tail := by
  rw [PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr.writeAt_of_lt
    false (by simp)]
  simp

private theorem shift_write2 (pre tail : List Bool) (_lo hi : Bool) :
    writeAt (pre ++ [false, false, false, false] ++ tail)
      (pre.length + 1) hi =
      pre ++ [false, hi, false, false] ++ tail := by
  rw [PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr.writeAt_of_lt
    hi (by simp)]
  simp

private theorem shift_write3 (pre tail : List Bool) (lo hi : Bool) :
    writeAt (pre ++ [false, hi, false, false] ++ tail)
      pre.length lo =
      pre ++ [lo, hi, false, false] ++ tail := by
  rw [PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr.writeAt_of_lt
    lo (by simp)]
  simp

private theorem shift_holeLo_step (T : List Bool) (p : Nat) :
    step runtimeUniversalPassedShiftMachine
        ⟨RuntimeUniversalPassedShiftState.holeLo, p, T⟩ =
      ⟨RuntimeUniversalPassedShiftState.holeHi, p + 1, T⟩ := by
  simp [step, runtimeUniversalPassedShiftMachine, moveHead]

private theorem shift_holeHi_step (T : List Bool) (p : Nat) :
    step runtimeUniversalPassedShiftMachine
        ⟨RuntimeUniversalPassedShiftState.holeHi, p + 1, T⟩ =
      ⟨RuntimeUniversalPassedShiftState.readLo, p + 2, T⟩ := by
  simp [step, runtimeUniversalPassedShiftMachine, moveHead]

private theorem shift_readLo_step (T : List Bool) (p : Nat) (lo : Bool)
    (hr : T[p + 2]?.getD false = lo) :
    step runtimeUniversalPassedShiftMachine
        ⟨RuntimeUniversalPassedShiftState.readLo, p + 2, T⟩ =
      ⟨RuntimeUniversalPassedShiftState.readHi lo, p + 3, T⟩ := by
  simp [step, runtimeUniversalPassedShiftMachine, moveHead, hr]

private theorem shift_readHi_step (T T' : List Bool) (p : Nat) (lo hi : Bool)
    (hr : T[p + 3]?.getD false = hi)
    (hw : writeAt T (p + 3) false = T') :
    step runtimeUniversalPassedShiftMachine
        ⟨RuntimeUniversalPassedShiftState.readHi lo, p + 3, T⟩ =
      ⟨RuntimeUniversalPassedShiftState.clearLo lo hi (!lo && hi), p + 2, T'⟩ := by
  simp [step, runtimeUniversalPassedShiftMachine, moveHead, hr, hw]

private theorem shift_clearLo_step (T T' : List Bool) (p : Nat)
    (lo hi terminal : Bool) (hw : writeAt T (p + 2) false = T') :
    step runtimeUniversalPassedShiftMachine
        ⟨RuntimeUniversalPassedShiftState.clearLo lo hi terminal, p + 2, T⟩ =
      ⟨RuntimeUniversalPassedShiftState.writeHi lo hi terminal, p + 1, T'⟩ := by
  simp [step, runtimeUniversalPassedShiftMachine, moveHead, hw]

private theorem shift_writeHi_step (T T' : List Bool) (p : Nat)
    (lo hi terminal : Bool) (hw : writeAt T (p + 1) hi = T') :
    step runtimeUniversalPassedShiftMachine
        ⟨RuntimeUniversalPassedShiftState.writeHi lo hi terminal, p + 1, T⟩ =
      ⟨RuntimeUniversalPassedShiftState.writeLo lo terminal, p, T'⟩ := by
  simp [step, runtimeUniversalPassedShiftMachine, moveHead, hw]

private theorem shift_writeLo_step (T T' : List Bool) (p : Nat)
    (lo terminal : Bool) (hw : writeAt T p lo = T') :
    step runtimeUniversalPassedShiftMachine
        ⟨RuntimeUniversalPassedShiftState.writeLo lo terminal, p, T⟩ =
      ⟨RuntimeUniversalPassedShiftState.advance terminal, p + 1, T'⟩ := by
  simp [step, runtimeUniversalPassedShiftMachine, moveHead, hw]

private theorem shift_advance_nonterminal_step (T : List Bool) (p : Nat) :
    step runtimeUniversalPassedShiftMachine
        ⟨RuntimeUniversalPassedShiftState.advance false, p + 1, T⟩ =
      ⟨RuntimeUniversalPassedShiftState.holeLo, p + 2, T⟩ := by
  simp [step, runtimeUniversalPassedShiftMachine, moveHead]

private theorem shift_advance_terminal_step (T : List Bool) (p : Nat) :
    step runtimeUniversalPassedShiftMachine
        ⟨RuntimeUniversalPassedShiftState.advance true, p + 1, T⟩ =
      ⟨RuntimeUniversalPassedShiftState.done, p + 2, T⟩ := by
  simp [step, runtimeUniversalPassedShiftMachine, moveHead]

/-- One nonterminal pair is moved left over the hole in eight transitions;
control continues at the moved hole. -/
theorem runtimeUniversalPassedShift_nonterminal
    (pre tail : List Bool) (lo hi : Bool)
    (hterm : ¬ (lo = false ∧ hi = true)) :
    run runtimeUniversalPassedShiftMachine 8
        ⟨runtimeUniversalPassedShiftMachine.start, pre.length,
          pre ++ [false, false, lo, hi] ++ tail⟩ =
      ⟨runtimeUniversalPassedShiftMachine.start, pre.length + 2,
        pre ++ [lo, hi, false, false] ++ tail⟩ := by
  let T0 := pre ++ [false, false, lo, hi] ++ tail
  let T1 := pre ++ [false, false, lo, false] ++ tail
  let T2 := pre ++ [false, false, false, false] ++ tail
  let T3 := pre ++ [false, hi, false, false] ++ tail
  let T4 := pre ++ [lo, hi, false, false] ++ tail
  have hr0 : T0[pre.length + 2]?.getD false = lo := by simp [T0]
  have hr1 : T0[pre.length + 3]?.getD false = hi := by simp [T0]
  have hw0 : writeAt T0 (pre.length + 3) false = T1 := by
    simpa [T0, T1] using shift_write0 pre tail lo hi
  have hw1 : writeAt T1 (pre.length + 2) false = T2 := by
    simpa [T1, T2] using shift_write1 pre tail lo
  have hw2 : writeAt T2 (pre.length + 1) hi = T3 := by
    simpa [T2, T3] using shift_write2 pre tail lo hi
  have hw3 : writeAt T3 pre.length lo = T4 := by
    simpa [T3, T4] using shift_write3 pre tail lo hi
  have ht : (!lo && hi) = false := by
    cases lo <;> cases hi <;> simp_all
  change run runtimeUniversalPassedShiftMachine 8
      ⟨RuntimeUniversalPassedShiftState.holeLo, pre.length, T0⟩ =
    ⟨RuntimeUniversalPassedShiftState.holeLo, pre.length + 2, T4⟩
  rw [show run runtimeUniversalPassedShiftMachine 8 _ =
      step runtimeUniversalPassedShiftMachine
        (step runtimeUniversalPassedShiftMachine
          (step runtimeUniversalPassedShiftMachine
            (step runtimeUniversalPassedShiftMachine
              (step runtimeUniversalPassedShiftMachine
                (step runtimeUniversalPassedShiftMachine
                  (step runtimeUniversalPassedShiftMachine
                    (step runtimeUniversalPassedShiftMachine
                      ⟨RuntimeUniversalPassedShiftState.holeLo, pre.length, T0⟩))))))) by rfl]
  rw [shift_holeLo_step T0 pre.length, shift_holeHi_step T0 pre.length,
    shift_readLo_step T0 pre.length lo hr0,
    shift_readHi_step T0 T1 pre.length lo hi hr1 hw0, ht,
    shift_clearLo_step T1 T2 pre.length lo hi false hw1,
    shift_writeHi_step T2 T3 pre.length lo hi false hw2,
    shift_writeLo_step T3 T4 pre.length lo false hw3,
    shift_advance_nonterminal_step T4 pre.length]

/-- The canonical closing pair `01` is moved left over the hole and the
same fixed controller genuinely halts immediately afterward. -/
theorem runtimeUniversalPassedShift_terminal
    (pre tail : List Bool) :
    run runtimeUniversalPassedShiftMachine 8
        ⟨runtimeUniversalPassedShiftMachine.start, pre.length,
          pre ++ [false, false, false, true] ++ tail⟩ =
      ⟨RuntimeUniversalPassedShiftState.done, pre.length + 2,
        pre ++ [false, true, false, false] ++ tail⟩ := by
  let T0 := pre ++ [false, false, false, true] ++ tail
  let T1 := pre ++ [false, false, false, false] ++ tail
  let T2 := pre ++ [false, true, false, false] ++ tail
  have hr0 : T0[pre.length + 2]?.getD false = false := by simp [T0]
  have hr1 : T0[pre.length + 3]?.getD false = true := by simp [T0]
  have hw0 : writeAt T0 (pre.length + 3) false = T1 := by
    simpa [T0, T1] using shift_write0 pre tail false true
  have hw1 : writeAt T1 (pre.length + 2) false = T1 := by
    simpa [T1] using shift_write1 pre tail false
  have hw2 : writeAt T1 (pre.length + 1) true = T2 := by
    simpa [T1, T2] using shift_write2 pre tail false true
  have hw3 : writeAt T2 pre.length false = T2 := by
    simpa [T2] using shift_write3 pre tail false true
  change run runtimeUniversalPassedShiftMachine 8
      ⟨RuntimeUniversalPassedShiftState.holeLo, pre.length, T0⟩ =
    ⟨RuntimeUniversalPassedShiftState.done, pre.length + 2, T2⟩
  rw [show run runtimeUniversalPassedShiftMachine 8 _ =
      step runtimeUniversalPassedShiftMachine
        (step runtimeUniversalPassedShiftMachine
          (step runtimeUniversalPassedShiftMachine
            (step runtimeUniversalPassedShiftMachine
              (step runtimeUniversalPassedShiftMachine
                (step runtimeUniversalPassedShiftMachine
                  (step runtimeUniversalPassedShiftMachine
                    (step runtimeUniversalPassedShiftMachine
                      ⟨RuntimeUniversalPassedShiftState.holeLo, pre.length, T0⟩))))))) by rfl]
  rw [shift_holeLo_step T0 pre.length, shift_holeHi_step T0 pre.length,
    shift_readLo_step T0 pre.length false hr0,
    shift_readHi_step T0 T1 pre.length false true hr1 hw0,
    show (!false && true) = true by decide,
    shift_clearLo_step T1 T1 pre.length false true true hw1,
    shift_writeHi_step T1 T2 pre.length false true true hw2,
    shift_writeLo_step T2 T2 pre.length false true hw3,
    shift_advance_terminal_step T2 pre.length]

theorem runtimeUniversalPassedShift_dataPairs
    (pre tail : List Bool) (bits : List Bool) :
    run runtimeUniversalPassedShiftMachine (8 * bits.length)
        ⟨runtimeUniversalPassedShiftMachine.start, pre.length,
          pre ++ [false, false] ++ flattenPairs (dataPairs bits) ++ tail⟩ =
      ⟨runtimeUniversalPassedShiftMachine.start,
        pre.length + 2 * bits.length,
        pre ++ flattenPairs (dataPairs bits) ++ [false, false] ++ tail⟩ := by
  induction bits generalizing pre with
  | nil => simp [dataPairs, flattenPairs]
  | cons b bits ih =>
      rw [show 8 * (b :: bits).length = 8 + 8 * bits.length by simp; omega,
        run_add]
      have hfirst := runtimeUniversalPassedShift_nonterminal pre
        (flattenPairs (dataPairs bits) ++ tail) b b (by cases b <;> simp)
      have hfirst' : run runtimeUniversalPassedShiftMachine 8
          ⟨runtimeUniversalPassedShiftMachine.start, pre.length,
            pre ++ [false, false] ++ flattenPairs (dataPairs (b :: bits)) ++ tail⟩ =
        ⟨runtimeUniversalPassedShiftMachine.start, pre.length + 2,
          pre ++ [b, b, false, false] ++
            flattenPairs (dataPairs bits) ++ tail⟩ := by
        simpa [dataPairs, flattenPairs, List.append_assoc] using hfirst
      rw [hfirst']
      have hih := ih (pre := pre ++ [b, b])
      convert hih using 1 <;>
        simp [dataPairs, flattenPairs, List.append_assoc, Nat.add_assoc,
          Nat.mul_add, Nat.add_comm]

/-- Full self-delimiting passed-block pass.  Its clock appears only in the
run theorem; the machine itself contains no length parameter. -/
theorem runtimeUniversalPassedShift_passedSourceBlock
    (pre tail : List Bool) (bits : List Bool) :
    run runtimeUniversalPassedShiftMachine
        (8 * (passedSourceBlock bits).length)
        ⟨runtimeUniversalPassedShiftMachine.start, pre.length,
          pre ++ [false, false] ++
            flattenPairs (passedSourceBlock bits) ++ tail⟩ =
      ⟨RuntimeUniversalPassedShiftState.done,
        pre.length + 2 * (passedSourceBlock bits).length,
        pre ++ flattenPairs (passedSourceBlock bits) ++
          [false, false] ++ tail⟩ := by
  rw [show 8 * (passedSourceBlock bits).length =
      8 + (8 * bits.length + 8) by
    simp [passedSourceBlock, dataPairs, Nat.mul_add, Nat.add_comm,
      Nat.add_left_comm]
    ring_nf,
    run_add]
  have hhead := runtimeUniversalPassedShift_nonterminal pre
    (flattenPairs (dataPairs bits) ++ [false, true] ++ tail)
    true true (by simp)
  rw [show run runtimeUniversalPassedShiftMachine 8
      ⟨runtimeUniversalPassedShiftMachine.start, pre.length,
        pre ++ [false, false] ++ flattenPairs (passedSourceBlock bits) ++ tail⟩ =
      ⟨runtimeUniversalPassedShiftMachine.start, pre.length + 2,
        pre ++ [true, true, false, false] ++
          flattenPairs (dataPairs bits) ++ [false, true] ++ tail⟩ by
    simpa [passedSourceBlock, flattenPairs, flattenPairs_append,
      List.append_assoc] using hhead,
    run_add]
  have hdata := runtimeUniversalPassedShift_dataPairs
    (pre ++ [true, true]) ([false, true] ++ tail) bits
  rw [show run runtimeUniversalPassedShiftMachine (8 * bits.length)
      ⟨runtimeUniversalPassedShiftMachine.start, pre.length + 2,
        pre ++ [true, true, false, false] ++
          flattenPairs (dataPairs bits) ++ [false, true] ++ tail⟩ =
      ⟨runtimeUniversalPassedShiftMachine.start,
        pre.length + 2 + 2 * bits.length,
        pre ++ [true, true] ++ flattenPairs (dataPairs bits) ++
          [false, false, false, true] ++ tail⟩ by
    simpa [List.append_assoc, Nat.add_assoc] using hdata]
  have hend := runtimeUniversalPassedShift_terminal
    (pre ++ [true, true] ++ flattenPairs (dataPairs bits)) tail
  convert hend using 1 <;>
    simp [passedSourceBlock, flattenPairs, flattenPairs_append,
      dataPairs, List.append_assoc, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] <;> ring_nf

/-! ## Structural left safety -/

def RuntimeUniversalPassedShiftHeadInvariant
    (c : Cfg runtimeUniversalPassedShiftMachine) : Prop :=
  match c.st with
  | .holeLo | .writeLo _ _ | .done => True
  | .holeHi | .writeHi _ _ _ | .advance _ => 1 ≤ c.hd
  | .readLo | .clearLo _ _ _ => 2 ≤ c.hd
  | .readHi _ => 3 ≤ c.hd

theorem runtimeUniversalPassedShift_invariant_step
    (c : Cfg runtimeUniversalPassedShiftMachine)
    (h : RuntimeUniversalPassedShiftHeadInvariant c) :
    RuntimeUniversalPassedShiftHeadInvariant
      (step runtimeUniversalPassedShiftMachine c) := by
  rcases c with ⟨st, hd, tp⟩
  cases st <;>
    simp_all [RuntimeUniversalPassedShiftHeadInvariant, step,
      runtimeUniversalPassedShiftMachine, moveHead] <;> try omega
  case advance terminal =>
    cases terminal <;> simp

theorem runtimeUniversalPassedShift_invariant_run
    (c : Cfg runtimeUniversalPassedShiftMachine)
    (h : RuntimeUniversalPassedShiftHeadInvariant c) (n : Nat) :
    RuntimeUniversalPassedShiftHeadInvariant
      (run runtimeUniversalPassedShiftMachine n c) := by
  induction n with
  | zero => simpa
  | succ n ih =>
      rw [run_succ]
      exact runtimeUniversalPassedShift_invariant_step _ ih

theorem runtimeUniversalPassedShift_leftSafe
    (c : Cfg runtimeUniversalPassedShiftMachine)
    (h : RuntimeUniversalPassedShiftHeadInvariant c) (n : Nat) :
    LeftSafeRun runtimeUniversalPassedShiftMachine c n := by
  intro i hi hhalt hmove
  have hinv := runtimeUniversalPassedShift_invariant_run c h i
  generalize hs : (run runtimeUniversalPassedShiftMachine i c).st = s
    at hinv hmove
  cases s <;>
    simp_all [RuntimeUniversalPassedShiftHeadInvariant,
      runtimeUniversalPassedShiftMachine] <;> omega

theorem runtimeUniversalPassedShift_passedSourceBlock_leftSafe
    (pre tail : List Bool) (bits : List Bool) :
    LeftSafeRun runtimeUniversalPassedShiftMachine
      ⟨runtimeUniversalPassedShiftMachine.start, pre.length,
        pre ++ [false, false] ++
          flattenPairs (passedSourceBlock bits) ++ tail⟩
      (8 * (passedSourceBlock bits).length) := by
  apply runtimeUniversalPassedShift_leftSafe
  simp [RuntimeUniversalPassedShiftHeadInvariant,
    runtimeUniversalPassedShiftMachine]

@[simp] theorem runtimeUniversalPassedShift_done_halts :
    runtimeUniversalPassedShiftMachine.halt
      RuntimeUniversalPassedShiftState.done = true := by
  simp [runtimeUniversalPassedShiftMachine]

#print axioms runtimeUniversalPassedShift_nonterminal
#print axioms runtimeUniversalPassedShift_terminal
#print axioms runtimeUniversalPassedShift_dataPairs
#print axioms runtimeUniversalPassedShift_passedSourceBlock
#print axioms runtimeUniversalPassedShift_invariant_step
#print axioms runtimeUniversalPassedShift_leftSafe
#print axioms runtimeUniversalPassedShift_passedSourceBlock_leftSafe

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeUniversalPassedShift
