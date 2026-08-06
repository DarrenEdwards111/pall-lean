import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeRendCorridor
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeArchiveLocator

/-!
# Fixed completed-workspace to future-archive locator

The reachable completed workspace has grammar

`10 01 (00|11) 10* 01 11* 10 ...`

where the final `10` is the first untouched future source-block header.  The
two starred lengths depend on the live literal address, but their pair tokens
are locally distinguishable.  This file defines one constant-state parser for
that grammar and proves it reaches the future archive without an offset.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeWorkspaceTailLocator

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinMaster
open PallLean.Paper93.DeepMath.PathB.CookLevinInP
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLiteralWeld
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixRun
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceCompact
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeTailPreservation
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeArchiveLocator
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRendCorridor

inductive RuntimeWorkspaceTailLocatorState
  | boot0 | boot1 | boot2 | boot3 | boot4 | boot5
  | corridorLo
  | corridorHi (lo : Bool)
  | paddingLo
  | paddingHi (lo : Bool)
  | done
  deriving DecidableEq, Fintype

open RuntimeWorkspaceTailLocatorState

/-- One fixed parser for the completed lookup workspace and padding. -/
def runtimeWorkspaceTailLocatorMachine : Machine where
  State := RuntimeWorkspaceTailLocatorState
  fin := inferInstance
  dec := inferInstance
  start := .boot0
  halt := fun s => decide (s = .done)
  δ := fun s b =>
    match s with
    | .boot0 => (.boot1, none, 1)
    | .boot1 => (.boot2, none, 1)
    | .boot2 => (.boot3, none, 1)
    | .boot3 => (.boot4, none, 1)
    | .boot4 => (.boot5, none, 1)
    | .boot5 => (.corridorLo, none, 1)
    | .corridorLo => (.corridorHi b, none, 1)
    | .corridorHi lo =>
        if lo && !b then (.corridorLo, none, 1)
        else if !lo && b then (.paddingLo, none, 1)
        else (.done, none, 2)
    | .paddingLo => (.paddingHi b, none, 1)
    | .paddingHi lo =>
        if lo && b then (.paddingLo, none, 1)
        else if lo && !b then (.done, none, 0)
        else (.done, none, 2)
    | .done => (.done, none, 2)
  accept := fun _ => false

theorem workspaceTail_run_boot (T : List Bool) (p : Nat) :
    run runtimeWorkspaceTailLocatorMachine 6 ⟨boot0, p, T⟩ =
      ⟨corridorLo, p + 6, T⟩ := by
  simp [run_succ, step, runtimeWorkspaceTailLocatorMachine, moveHead]

theorem workspaceTail_run_rendPair (T : List Bool) (p : Nat)
    (h0 : T.getD p false = true)
    (h1 : T.getD (p + 1) false = false) :
    run runtimeWorkspaceTailLocatorMachine 2 ⟨corridorLo, p, T⟩ =
      ⟨corridorLo, p + 2, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h0 h1
  simp [run_succ, step, runtimeWorkspaceTailLocatorMachine, moveHead, h0, h1]

theorem workspaceTail_run_rendPairs (T : List Bool) (q m : Nat)
    (h : RendCorridor T q m) :
    run runtimeWorkspaceTailLocatorMachine (2 * m) ⟨corridorLo, q, T⟩ =
      ⟨corridorLo, q + 2 * m, T⟩ := by
  induction m with
  | zero => rfl
  | succ m ih =>
      have hm := h m (by omega)
      rw [show 2 * (m + 1) = 2 * m + 2 by omega, run_add,
        ih (fun i hi => h i (by omega)),
        workspaceTail_run_rendPair T (q + 2 * m) hm.1 (by
          simpa [Nat.add_assoc] using hm.2)]
      congr 1

theorem workspaceTail_run_boundary (T : List Bool) (p : Nat)
    (h0 : T.getD p false = false)
    (h1 : T.getD (p + 1) false = true) :
    run runtimeWorkspaceTailLocatorMachine 2 ⟨corridorLo, p, T⟩ =
      ⟨paddingLo, p + 2, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h0 h1
  simp [run_succ, step, runtimeWorkspaceTailLocatorMachine, moveHead, h0, h1]

theorem workspaceTail_run_paddingPair (T : List Bool) (p : Nat)
    (h0 : T.getD p false = true)
    (h1 : T.getD (p + 1) false = true) :
    run runtimeWorkspaceTailLocatorMachine 2 ⟨paddingLo, p, T⟩ =
      ⟨paddingLo, p + 2, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h0 h1
  simp [run_succ, step, runtimeWorkspaceTailLocatorMachine, moveHead, h0, h1]

theorem workspaceTail_run_paddingPairs (T : List Bool) (q n : Nat)
    (h : ∀ i, i < n →
      T.getD (q + 2 * i) false = true ∧
      T.getD (q + 2 * i + 1) false = true) :
    run runtimeWorkspaceTailLocatorMachine (2 * n) ⟨paddingLo, q, T⟩ =
      ⟨paddingLo, q + 2 * n, T⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hn := h n (by omega)
      rw [show 2 * (n + 1) = 2 * n + 2 by omega, run_add,
        ih (fun i hi => h i (by omega)),
        workspaceTail_run_paddingPair T (q + 2 * n) hn.1 (by
          simpa [Nat.add_assoc] using hn.2)]
      congr 1

theorem workspaceTail_run_futureHeader (T : List Bool) (p : Nat)
    (h0 : T.getD p false = true)
    (h1 : T.getD (p + 1) false = false) :
    run runtimeWorkspaceTailLocatorMachine 2 ⟨paddingLo, p, T⟩ =
      ⟨done, p, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h0 h1
  simp [run_succ, step, runtimeWorkspaceTailLocatorMachine, moveHead, h0, h1]

/-- Generic exact run for the reachable workspace-tail grammar. -/
theorem runtimeWorkspaceTailLocator_run (T : List Bool) (p m n : Nat)
    (hcorr : RendCorridor T (p + 6) m)
    (hb0 : T.getD (p + 6 + 2 * m) false = false)
    (hb1 : T.getD (p + 6 + 2 * m + 1) false = true)
    (hpad : ∀ i, i < n →
      T.getD (p + 8 + 2 * m + 2 * i) false = true ∧
      T.getD (p + 8 + 2 * m + 2 * i + 1) false = true)
    (hh0 : T.getD (p + 8 + 2 * m + 2 * n) false = true)
    (hh1 : T.getD (p + 8 + 2 * m + 2 * n + 1) false = false) :
    run runtimeWorkspaceTailLocatorMachine
        (6 + 2 * m + 2 + 2 * n + 2)
        ⟨boot0, p, T⟩ =
      ⟨done, p + 8 + 2 * m + 2 * n, T⟩ := by
  have hpadrun : run runtimeWorkspaceTailLocatorMachine (2 * n)
      ⟨paddingLo, p + 6 + 2 * m + 2, T⟩ =
      ⟨paddingLo, p + 8 + 2 * m + 2 * n, T⟩ := by
    rw [show p + 6 + 2 * m + 2 = p + 8 + 2 * m by omega]
    exact workspaceTail_run_paddingPairs T (p + 8 + 2 * m) n hpad
  rw [show 6 + 2 * m + 2 + 2 * n + 2 =
      6 + (2 * m + (2 + (2 * n + 2))) by omega,
    run_add, workspaceTail_run_boot,
    run_add, workspaceTail_run_rendPairs T (p + 6) m hcorr,
    run_add, workspaceTail_run_boundary T (p + 6 + 2 * m) hb0 hb1,
    run_add, hpadrun,
    workspaceTail_run_futureHeader T (p + 8 + 2 * m + 2 * n) hh0 hh1]

/-- The fixed parser runs on the actual completed canonical literal workspace
and halts at the first untouched future source block. -/
theorem masterM_literal_workspaceTailLocate (w : List Bool) (l : Lit)
    (next : List Bool) (more : List (List Bool)) :
    let bits := literalLookupTape w l
    let rest := next :: more
    let trailer := [true, false, false, true] ++
      List.replicate bits.length true ++ selectedTail rest
    let cf := run masterM (literalLookupClock w l)
      (init masterM (bits ++ trailer))
    run runtimeWorkspaceTailLocatorMachine (8 * l.1 + 22)
        ⟨boot0, 0, cf.tp⟩ =
      ⟨done, 2 * bits.length + 4, cf.tp⟩ := by
  dsimp only
  let bits := literalLookupTape w l
  let rest := next :: more
  let trailer := [true, false, false, true] ++
    List.replicate bits.length true ++ selectedTail rest
  let cf := run masterM (literalLookupClock w l)
    (init masterM (bits ++ trailer))
  let m := 2 * l.1 + 2
  let n := 2 * l.1 + 4
  have hbitslen : bits.length = 4 * l.1 + 8 := by
    simp [bits, literalLookupTape, CookLevinInP.encode,
      signedLookupAssignment_length, CookLevinInP.double_length]
    ring
  have hcorr : RendCorridor cf.tp 6 m := by
    simpa [cf, bits, trailer, m] using
      masterM_literal_rendCorridor w l
        (List.replicate bits.length true ++ selectedTail rest)
  have hdrop : cf.tp.drop bits.length = trailer := by
    simpa [cf, bits, trailer] using masterM_literal_trailer w l trailer
  have hlenDrop := congrArg List.length hdrop
  have hle : bits.length ≤ cf.tp.length := by
    simp only [List.length_drop] at hlenDrop
    have hpos : 0 < trailer.length := by simp [trailer]
    omega
  let front := cf.tp.take bits.length
  have hfront : front.length = bits.length := by
    dsimp [front]
    rw [List.length_take, Nat.min_eq_left hle]
  have hshape : cf.tp = front ++ trailer := by
    rw [← List.take_append_drop bits.length cf.tp, hdrop]
  have hget (j : Nat) :
      cf.tp.getD (bits.length + j) false = trailer.getD j false := by
    rw [hshape, show bits.length + j = front.length + j by rw [hfront],
      List.getD_append_right (h := by omega)]
    rw [show front.length + j - front.length = j by omega]
  have htrailerPad (j : Nat) (hj : j < bits.length) :
      trailer.getD (4 + j) false = true := by
    change (true :: false :: false :: true ::
      (List.replicate bits.length true ++ selectedTail rest)).getD
        (4 + j) false = true
    rw [show 4 + j = j + 1 + 1 + 1 + 1 by omega]
    simp only [List.getD_cons_succ]
    rw [List.getD_append (h := by simpa using hj)]
    exact getD_replicate_true hj
  have htrailerHead0 : trailer.getD (4 + bits.length) false = true := by
    change (true :: false :: false :: true ::
      (List.replicate bits.length true ++ selectedTail rest)).getD
        (4 + bits.length) false = true
    rw [show 4 + bits.length = bits.length + 1 + 1 + 1 + 1 by omega]
    simp only [List.getD_cons_succ]
    rw [List.getD_append_right (h := by simp)]
    simp [rest, selectedTail_cons]
  have htrailerHead1 : trailer.getD (4 + bits.length + 1) false = false := by
    change (true :: false :: false :: true ::
      (List.replicate bits.length true ++ selectedTail rest)).getD
        (4 + bits.length + 1) false = false
    rw [show 4 + bits.length + 1 = (bits.length + 1) + 1 + 1 + 1 + 1 by omega]
    simp only [List.getD_cons_succ]
    rw [List.getD_append_right (h := by simp)]
    simp [rest, selectedTail_cons]
  have hb0 : cf.tp.getD (6 + 2 * m) false = false := by
    rw [show 6 + 2 * m = bits.length + 2 by simp [m, hbitslen]; omega,
      hget]
    simp [trailer]
  have hb1 : cf.tp.getD (6 + 2 * m + 1) false = true := by
    rw [show 6 + 2 * m + 1 = bits.length + 3 by simp [m, hbitslen]; omega,
      hget]
    simp [trailer]
  have hpad : ∀ i, i < n →
      cf.tp.getD (8 + 2 * m + 2 * i) false = true ∧
      cf.tp.getD (8 + 2 * m + 2 * i + 1) false = true := by
    intro i hi
    have hbase : 8 + 2 * m = bits.length + 4 := by simp [m, hbitslen]; omega
    have hj0 : 2 * i < bits.length := by simp [n, hbitslen] at hi ⊢; omega
    have hj1 : 2 * i + 1 < bits.length := by simp [n, hbitslen] at hi ⊢; omega
    constructor
    · rw [hbase, show bits.length + 4 + 2 * i =
          bits.length + (4 + 2 * i) by omega, hget]
      exact htrailerPad (2 * i) hj0
    · rw [hbase, show bits.length + 4 + 2 * i + 1 =
          bits.length + (4 + (2 * i + 1)) by omega, hget]
      exact htrailerPad (2 * i + 1) hj1
  have hh0 : cf.tp.getD (8 + 2 * m + 2 * n) false = true := by
    rw [show 8 + 2 * m + 2 * n = 2 * bits.length + 4 by
      simp [m, n, hbitslen]; omega,
      show 2 * bits.length + 4 = bits.length + (4 + bits.length) by omega,
      hget]
    exact htrailerHead0
  have hh1 : cf.tp.getD (8 + 2 * m + 2 * n + 1) false = false := by
    rw [show 8 + 2 * m + 2 * n + 1 = 2 * bits.length + 5 by
      simp [m, n, hbitslen]; omega,
      show 2 * bits.length + 5 = bits.length + (4 + bits.length + 1) by omega,
      hget]
    exact htrailerHead1
  have hr := runtimeWorkspaceTailLocator_run cf.tp 0 m n hcorr hb0 hb1
    (by simpa using hpad) (by simpa using hh0) (by simpa using hh1)
  rw [show 8 * l.1 + 22 = 6 + 2 * m + 2 + 2 * n + 2 by
      simp [m, n]; omega,
    show 2 * bits.length + 4 = 0 + 8 + 2 * m + 2 * n by
      simp [m, n, hbitslen]; omega]
  exact hr

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeWorkspaceTailLocator

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeWorkspaceTailLocator.runtimeWorkspaceTailLocator_run
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeWorkspaceTailLocator.masterM_literal_workspaceTailLocate
