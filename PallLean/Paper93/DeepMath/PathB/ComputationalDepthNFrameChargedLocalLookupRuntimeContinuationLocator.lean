import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeFrontOutput

/-!
# Charged local lookup: terminal-aware continuation discovery

After a rebased-front lookup and output cashout, the doubled entry marker and
the completed lookup tape remain in place.  This file defines one reset-free
classifier which starts at the rebased selector, crosses

`11* 01 | workspace-prefix | 10* 01 11*`

and then distinguishes a future archive header `10` from the terminal blank
`00`.  Its accept bit is exactly the continuation decision.  The classifier
is then placed behind the robust doubled-marker locator.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeContinuationLocator

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinMaster
open PallLean.Paper93.DeepMath.PathB.CookLevinInP
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLiteralWeld
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupOutputCapacity
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixRun
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeTailPreservation
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRendCorridor
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundEntryLocator
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeMarkedEntry
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceLookup
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeFrontLookup
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeFrontOutput

inductive RuntimeContinuationLocatorState
  | selectorLo
  | selectorHi (lo : Bool)
  | boot (i : Fin 7)
  | corridorLo
  | corridorHi (lo : Bool)
  | paddingLo
  | paddingHi (lo : Bool)
  | done (hasFuture : Bool)
  deriving DecidableEq, Fintype

open RuntimeContinuationLocatorState

/-- Reset-free terminal-aware parser.  `done true` means a future `10`
archive header was found; `done false` means the reachable terminal `00`
blank was found. -/
def runtimeContinuationLocatorMachine : Machine where
  State := RuntimeContinuationLocatorState
  fin := inferInstance
  dec := inferInstance
  start := .selectorLo
  halt := fun s => match s with
    | .done _ => true
    | _ => false
  δ := fun s b => match s with
    | .selectorLo => (.selectorHi b, none, 1)
    | .selectorHi lo =>
        if lo && b then (.selectorLo, none, 1)
        else if !lo && b then (.boot ⟨0, by omega⟩, none, 1)
        else (.done false, none, 2)
    | .boot i =>
        if hi : i.val < 6 then (.boot ⟨i.val + 1, by omega⟩, none, 1)
        else (.corridorLo, none, 2)
    | .corridorLo => (.corridorHi b, none, 1)
    | .corridorHi lo =>
        if lo && !b then (.corridorLo, none, 1)
        else if !lo && b then (.paddingLo, none, 1)
        else (.done false, none, 2)
    | .paddingLo => (.paddingHi b, none, 1)
    | .paddingHi lo =>
        if lo && b then (.paddingLo, none, 1)
        else if !b then (.done lo, none, 1)
        else (.done false, none, 2)
    | .done z => (.done z, none, 2)
  accept := fun s => match s with
    | .done z => z
    | _ => false

def runtimeContinuationLocatorClock (d : Nat) (l : Lit) : Nat :=
  2 * d + 8 * l.1 + 25

theorem continuation_run_selectorPair (T : List Bool) (p : Nat)
    (h0 : T.getD p false = true)
    (h1 : T.getD (p + 1) false = true) :
    run runtimeContinuationLocatorMachine 2 ⟨selectorLo, p, T⟩ =
      ⟨selectorLo, p + 2, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h0 h1
  simp [run_succ, step, runtimeContinuationLocatorMachine, moveHead, h0, h1]

theorem continuation_run_selectorPairs (T : List Bool) (q d : Nat)
    (h : ∀ i, i < d →
      T.getD (q + 2 * i) false = true ∧
      T.getD (q + 2 * i + 1) false = true) :
    run runtimeContinuationLocatorMachine (2 * d) ⟨selectorLo, q, T⟩ =
      ⟨selectorLo, q + 2 * d, T⟩ := by
  induction d with
  | zero => rfl
  | succ d ih =>
      have hd := h d (by omega)
      rw [show 2 * (d + 1) = 2 * d + 2 by omega, run_add,
        ih (fun i hi => h i (by omega)),
        continuation_run_selectorPair T (q + 2 * d) hd.1 (by
          simpa [Nat.add_assoc] using hd.2)]
      congr 1

theorem continuation_run_selectorBoundary (T : List Bool) (p : Nat)
    (h0 : T.getD p false = false)
    (h1 : T.getD (p + 1) false = true) :
    run runtimeContinuationLocatorMachine 2 ⟨selectorLo, p, T⟩ =
      ⟨boot ⟨0, by omega⟩, p + 2, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h0 h1
  simp [run_succ, step, runtimeContinuationLocatorMachine, moveHead, h0, h1]

theorem continuation_run_boot (T : List Bool) (p : Nat) :
    run runtimeContinuationLocatorMachine 7
      ⟨boot ⟨0, by omega⟩, p, T⟩ =
      ⟨corridorLo, p + 6, T⟩ := by
  simp [run_succ, step, runtimeContinuationLocatorMachine, moveHead]

theorem continuation_run_rendPair (T : List Bool) (p : Nat)
    (h0 : T.getD p false = true)
    (h1 : T.getD (p + 1) false = false) :
    run runtimeContinuationLocatorMachine 2 ⟨corridorLo, p, T⟩ =
      ⟨corridorLo, p + 2, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h0 h1
  simp [run_succ, step, runtimeContinuationLocatorMachine, moveHead, h0, h1]

theorem continuation_run_rendPairs (T : List Bool) (q m : Nat)
    (h : RendCorridor T q m) :
    run runtimeContinuationLocatorMachine (2 * m) ⟨corridorLo, q, T⟩ =
      ⟨corridorLo, q + 2 * m, T⟩ := by
  induction m with
  | zero => rfl
  | succ m ih =>
      have hm := h m (by omega)
      rw [show 2 * (m + 1) = 2 * m + 2 by omega, run_add,
        ih (fun i hi => h i (by omega)),
        continuation_run_rendPair T (q + 2 * m) hm.1 (by
          simpa [Nat.add_assoc] using hm.2)]
      congr 1

theorem continuation_run_corridorBoundary (T : List Bool) (p : Nat)
    (h0 : T.getD p false = false)
    (h1 : T.getD (p + 1) false = true) :
    run runtimeContinuationLocatorMachine 2 ⟨corridorLo, p, T⟩ =
      ⟨paddingLo, p + 2, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h0 h1
  simp [run_succ, step, runtimeContinuationLocatorMachine, moveHead, h0, h1]

theorem continuation_run_paddingPair (T : List Bool) (p : Nat)
    (h0 : T.getD p false = true)
    (h1 : T.getD (p + 1) false = true) :
    run runtimeContinuationLocatorMachine 2 ⟨paddingLo, p, T⟩ =
      ⟨paddingLo, p + 2, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h0 h1
  simp [run_succ, step, runtimeContinuationLocatorMachine, moveHead, h0, h1]

theorem continuation_run_paddingPairs (T : List Bool) (q n : Nat)
    (h : ∀ i, i < n →
      T.getD (q + 2 * i) false = true ∧
      T.getD (q + 2 * i + 1) false = true) :
    run runtimeContinuationLocatorMachine (2 * n) ⟨paddingLo, q, T⟩ =
      ⟨paddingLo, q + 2 * n, T⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hn := h n (by omega)
      rw [show 2 * (n + 1) = 2 * n + 2 by omega, run_add,
        ih (fun i hi => h i (by omega)),
        continuation_run_paddingPair T (q + 2 * n) hn.1 (by
          simpa [Nat.add_assoc] using hn.2)]
      congr 1

theorem continuation_run_decide (T : List Bool) (p : Nat) (z : Bool)
    (h0 : T.getD p false = z)
    (h1 : T.getD (p + 1) false = false) :
    run runtimeContinuationLocatorMachine 2 ⟨paddingLo, p, T⟩ =
      ⟨done z, p + 2, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h0 h1
  cases z <;>
    simp [run_succ, step, runtimeContinuationLocatorMachine, moveHead, h0, h1]

/-- Generic exact classification from the rebased selector origin. -/
theorem runtimeContinuationLocator_run (T : List Bool)
    (d p m n : Nat) (z : Bool)
    (hselector : ∀ i, i < d →
      T.getD (p + 2 * i) false = true ∧
      T.getD (p + 2 * i + 1) false = true)
    (hs0 : T.getD (p + 2 * d) false = false)
    (hs1 : T.getD (p + 2 * d + 1) false = true)
    (hcorr : RendCorridor T (p + 2 * d + 8) m)
    (hb0 : T.getD (p + 2 * d + 8 + 2 * m) false = false)
    (hb1 : T.getD (p + 2 * d + 8 + 2 * m + 1) false = true)
    (hpad : ∀ i, i < n →
      T.getD (p + 2 * d + 10 + 2 * m + 2 * i) false = true ∧
      T.getD (p + 2 * d + 10 + 2 * m + 2 * i + 1) false = true)
    (hz0 : T.getD (p + 2 * d + 10 + 2 * m + 2 * n) false = z)
    (hz1 : T.getD (p + 2 * d + 10 + 2 * m + 2 * n + 1) false = false) :
    run runtimeContinuationLocatorMachine
        (2 * d + 2 + 7 + 2 * m + 2 + 2 * n + 2)
        ⟨selectorLo, p, T⟩ =
      ⟨done z, p + 2 * d + 10 + 2 * m + 2 * n + 2, T⟩ := by
  have hpadrun : run runtimeContinuationLocatorMachine (2 * n)
      ⟨paddingLo, p + 2 * d + 8 + 2 * m + 2, T⟩ =
      ⟨paddingLo, p + 2 * d + 10 + 2 * m + 2 * n, T⟩ := by
    simpa only [show p + 2 * d + 8 + 2 * m + 2 =
        p + 2 * d + 10 + 2 * m by omega] using
      continuation_run_paddingPairs T
        (p + 2 * d + 10 + 2 * m) n hpad
  rw [show 2 * d + 2 + 7 + 2 * m + 2 + 2 * n + 2 =
      2 * d + (2 + (7 + (2 * m + (2 + (2 * n + 2))))) by omega,
    run_add, continuation_run_selectorPairs T p d hselector,
    run_add, continuation_run_selectorBoundary T (p + 2 * d) hs0 hs1,
    run_add, continuation_run_boot,
    run_add, continuation_run_rendPairs T (p + 2 * d + 8) m hcorr,
    run_add, continuation_run_corridorBoundary T
      (p + 2 * d + 8 + 2 * m) hb0 hb1,
    run_add, hpadrun,
    continuation_run_decide T
      (p + 2 * d + 10 + 2 * m + 2 * n) z hz0 hz1]

theorem runtimeContinuationLocator_move_ne_reset
    (s : RuntimeContinuationLocatorState) (b : Bool) :
    (runtimeContinuationLocatorMachine.δ s b).2.2 ≠ 3 := by
  cases s <;> simp [runtimeContinuationLocatorMachine] <;>
    split_ifs <;> simp

theorem runtimeContinuationLocator_move_ne_left
    (s : RuntimeContinuationLocatorState) (b : Bool) :
    (runtimeContinuationLocatorMachine.δ s b).2.2 ≠ 0 := by
  cases s <;> simp [runtimeContinuationLocatorMachine] <;>
    split_ifs <;> simp

theorem runtimeContinuationLocator_prefixSafe (T : List Bool) (n : Nat) :
    PrefixSafeRun runtimeContinuationLocatorMachine
      (init runtimeContinuationLocatorMachine T) n := by
  intro _ _
  constructor
  · intro _
    exact runtimeContinuationLocator_move_ne_reset _ _
  · intro _ hleft
    exact False.elim (runtimeContinuationLocator_move_ne_left _ _ hleft)

/-! ## Reachable completed-lookup specialization -/

set_option maxHeartbeats 1000000
theorem masterM_literal_continuationLocate (w : List Bool) (l : Lit)
    (rest : List (List Bool)) :
    let bits := literalLookupTape w l
    let d := (bits :: rest).length
    let sourcePre := flattenPairs (List.replicate d (true, true)) ++
      [false, true]
    let archiveTail := flattenPairs (rest.flatMap freshSourceBlock)
    let trailer := [true, false, false, true] ++
      List.replicate bits.length true ++ archiveTail
    let mcf := run masterM (literalLookupClock w l)
      (init masterM (bits ++ trailer))
    let z := decide (rest ≠ [])
    run runtimeContinuationLocatorMachine
        (runtimeContinuationLocatorClock d l)
        (init runtimeContinuationLocatorMachine (sourcePre ++ mcf.tp)) =
      ⟨done z, sourcePre.length + 2 * bits.length + 6,
        sourcePre ++ mcf.tp⟩ := by
  dsimp only
  let bits := literalLookupTape w l
  let d := (bits :: rest).length
  let sourcePre := flattenPairs (List.replicate d (true, true)) ++
    [false, true]
  let archiveTail := flattenPairs (rest.flatMap freshSourceBlock)
  let trailer := [true, false, false, true] ++
    List.replicate bits.length true ++ archiveTail
  let mcf := run masterM (literalLookupClock w l)
    (init masterM (bits ++ trailer))
  let z := decide (rest ≠ [])
  let T := sourcePre ++ mcf.tp
  let m := 2 * l.1 + 2
  let n := 2 * l.1 + 4
  have hbitslen : bits.length = 4 * l.1 + 8 := by
    simp [bits, literalLookupTape, CookLevinInP.encode,
      signedLookupAssignment_length, CookLevinInP.double_length]
    ring
  have hprelen : sourcePre.length = 2 * d + 2 := by
    simp [sourcePre, flattenPairs_length]
  have hTget (j : Nat) :
      T.getD (sourcePre.length + j) false = mcf.tp.getD j false := by
    dsimp [T]
    rw [List.getD_append_right (h := by omega)]
    simp
  have hselector : ∀ i, i < d →
      T.getD (2 * i) false = true ∧
      T.getD (2 * i + 1) false = true := by
    intro i hi
    have hflat : (flattenPairs (List.replicate d (true, true))).length =
        2 * d := by simp [flattenPairs_length]
    have hrp : (List.replicate d (true, true)).getD i (false, false) =
        (true, true) := List.getD_replicate _ (h := hi)
    rw [List.getD_eq_getElem?_getD] at hrp
    constructor
    · change (sourcePre ++ mcf.tp).getD (2 * i) false = true
      rw [List.getD_append (h := by simp [sourcePre, hflat]; omega)]
      dsimp [sourcePre]
      rw [List.getD_append (h := by rw [hflat]; omega),
        flattenPairs_getD_lo _ i (by simp; omega)]
      exact congrArg Prod.fst hrp
    · change (sourcePre ++ mcf.tp).getD (2 * i + 1) false = true
      rw [List.getD_append (h := by simp [sourcePre, hflat]; omega)]
      dsimp [sourcePre]
      rw [List.getD_append (h := by rw [hflat]; omega),
        flattenPairs_getD_hi _ i (by simp; omega)]
      exact congrArg Prod.snd hrp
  have hs0 : T.getD (2 * d) false = false := by
    simp [T, sourcePre, flattenPairs_length]
  have hs1 : T.getD (2 * d + 1) false = true := by
    simp [T, sourcePre, flattenPairs_length]
  have hcorr0 : RendCorridor mcf.tp 6 m := by
    simpa [mcf, bits, trailer, m] using
      masterM_literal_rendCorridor w l
        (List.replicate bits.length true ++ archiveTail)
  have hcorr : RendCorridor T (2 * d + 8) m := by
    intro i hi
    have hc := hcorr0 i hi
    rw [show 2 * d + 8 + 2 * i =
      sourcePre.length + (6 + 2 * i) by rw [hprelen]; omega]
    rw [show sourcePre.length + (6 + 2 * i) + 1 =
      sourcePre.length + (6 + 2 * i + 1) by omega,
      hTget, hTget]
    exact hc
  have hdrop : mcf.tp.drop bits.length = trailer := by
    simpa [mcf, bits, trailer] using masterM_literal_trailer w l trailer
  have hlenDrop := congrArg List.length hdrop
  have hle : bits.length ≤ mcf.tp.length := by
    simp only [List.length_drop] at hlenDrop
    have hpos : 0 < trailer.length := by simp [trailer]
    omega
  let front := mcf.tp.take bits.length
  have hfront : front.length = bits.length := by
    dsimp [front]
    rw [List.length_take, Nat.min_eq_left hle]
  have hshape : mcf.tp = front ++ trailer := by
    rw [← List.take_append_drop bits.length mcf.tp, hdrop]
  have hget (j : Nat) :
      mcf.tp.getD (bits.length + j) false = trailer.getD j false := by
    rw [hshape, show bits.length + j = front.length + j by rw [hfront],
      List.getD_append_right (h := by omega)]
    rw [show front.length + j - front.length = j by omega]
  have htrailerPad (j : Nat) (hj : j < bits.length) :
      trailer.getD (4 + j) false = true := by
    change (true :: false :: false :: true ::
      (List.replicate bits.length true ++ archiveTail)).getD
        (4 + j) false = true
    rw [show 4 + j = j + 1 + 1 + 1 + 1 by omega]
    simp only [List.getD_cons_succ]
    rw [List.getD_append (h := by simpa using hj)]
    exact getD_replicate_true hj
  have hfinal0 : trailer.getD (4 + bits.length) false = z := by
    change (true :: false :: false :: true ::
      (List.replicate bits.length true ++ archiveTail)).getD
        (4 + bits.length) false = z
    rw [show 4 + bits.length = bits.length + 1 + 1 + 1 + 1 by omega]
    simp only [List.getD_cons_succ]
    have happ : (List.replicate bits.length true ++ archiveTail).getD
        bits.length false = archiveTail.getD 0 false := by
      rw [List.getD_append_right (h := by simp)]
      simp
    rw [happ]
    rcases rest with _ | ⟨next, more⟩
    · simp [archiveTail, z]
    · simp [archiveTail, z, freshSourceBlock,
        flattenPairs_append, flattenPairs]
  have hfinal1 : trailer.getD (4 + bits.length + 1) false = false := by
    change (true :: false :: false :: true ::
      (List.replicate bits.length true ++ archiveTail)).getD
        (4 + bits.length + 1) false = false
    rw [show 4 + bits.length + 1 =
      (bits.length + 1) + 1 + 1 + 1 + 1 by omega]
    simp only [List.getD_cons_succ]
    have happ : (List.replicate bits.length true ++ archiveTail).getD
        (bits.length + 1) false = archiveTail.getD 1 false := by
      rw [List.getD_append_right (h := by simp)]
      simp
    rw [happ]
    rcases rest with _ | ⟨next, more⟩
    · simp [archiveTail]
    · simp [archiveTail, freshSourceBlock,
        flattenPairs_append, flattenPairs]
  have hb0 : T.getD (2 * d + 8 + 2 * m) false = false := by
    rw [show 2 * d + 8 + 2 * m = sourcePre.length + (6 + 2 * m) by
      rw [hprelen]; omega, hTget,
      show 6 + 2 * m = bits.length + 2 by simp [m, hbitslen]; omega,
      hget]
    simp [trailer]
  have hb1 : T.getD (2 * d + 8 + 2 * m + 1) false = true := by
    rw [show 2 * d + 8 + 2 * m + 1 =
      sourcePre.length + (6 + 2 * m + 1) by rw [hprelen]; omega,
      hTget,
      show 6 + 2 * m + 1 = bits.length + 3 by simp [m, hbitslen]; omega,
      hget]
    simp [trailer]
  have hpad : ∀ i, i < n →
      T.getD (2 * d + 10 + 2 * m + 2 * i) false = true ∧
      T.getD (2 * d + 10 + 2 * m + 2 * i + 1) false = true := by
    intro i hi
    have hj0 : 2 * i < bits.length := by simp [n, hbitslen] at hi ⊢; omega
    have hj1 : 2 * i + 1 < bits.length := by
      simp [n, hbitslen] at hi ⊢
      omega
    constructor
    · rw [show 2 * d + 10 + 2 * m + 2 * i =
        sourcePre.length + (8 + 2 * m + 2 * i) by rw [hprelen]; omega,
        hTget,
        show 8 + 2 * m + 2 * i = bits.length + (4 + 2 * i) by
          simp [m, hbitslen]; omega,
        hget]
      exact htrailerPad (2 * i) hj0
    · rw [show 2 * d + 10 + 2 * m + 2 * i + 1 =
        sourcePre.length + (8 + 2 * m + 2 * i + 1) by rw [hprelen]; omega,
        hTget,
        show 8 + 2 * m + 2 * i + 1 =
          bits.length + (4 + (2 * i + 1)) by simp [m, hbitslen]; omega,
        hget]
      exact htrailerPad (2 * i + 1) hj1
  have hz0 : T.getD (2 * d + 10 + 2 * m + 2 * n) false = z := by
    rw [show 2 * d + 10 + 2 * m + 2 * n =
      sourcePre.length + (2 * bits.length + 4) by
        rw [hprelen]; simp [m, n, hbitslen]; omega,
      hTget,
      show 2 * bits.length + 4 = bits.length + (4 + bits.length) by omega,
      hget]
    exact hfinal0
  have hz1 : T.getD (2 * d + 10 + 2 * m + 2 * n + 1) false = false := by
    rw [show 2 * d + 10 + 2 * m + 2 * n + 1 =
      sourcePre.length + (2 * bits.length + 4 + 1) by
        rw [hprelen]; simp [m, n, hbitslen]; omega,
      hTget,
      show 2 * bits.length + 4 + 1 =
        bits.length + (4 + bits.length + 1) by omega,
      hget]
    exact hfinal1
  have hr := runtimeContinuationLocator_run T d 0 m n z
    (by simpa using hselector) (by simpa using hs0) (by simpa using hs1)
    (by simpa using hcorr) (by simpa using hb0) (by simpa using hb1)
    (by simpa using hpad) (by simpa using hz0) (by simpa using hz1)
  have hclock : 2 * d + 2 + 7 + 2 * m + 2 + 2 * n + 2 =
      runtimeContinuationLocatorClock d l := by
    simp [runtimeContinuationLocatorClock, m, n]
    omega
  have hhead : 0 + 2 * d + 10 + 2 * m + 2 * n + 2 =
      sourcePre.length + 2 * bits.length + 6 := by
    rw [hprelen, hbitslen]
    simp [m, n]
    omega
  rw [hclock, hhead] at hr
  simpa [T, bits, d, sourcePre, archiveTail, trailer, mcf, z] using hr

def runtimeMarkedContinuationMachine : Machine :=
  runtimeMarkedAcceptBody runtimeContinuationLocatorMachine

def runtimeMarkedContinuationClock (pairs : List (Bool × Bool))
    (d : Nat) (l : Lit) : Nat :=
  runtimeMarkedAcceptClock pairs (runtimeContinuationLocatorClock d l)

/-- The robust marker locator and terminal-aware classifier are one accepting
controller.  Its accept bit is true exactly when the completed lookup still
has a future archive block. -/
theorem runtimeMarkedContinuation_run
    (pairs : List (Bool × Bool)) (w : List Bool) (l : Lit)
    (rest : List (List Bool))
    (hsafe : RuntimeNoDoubleSepFrom false pairs) :
    let bits := literalLookupTape w l
    let d := (bits :: rest).length
    let sourcePre := flattenPairs (List.replicate d (true, true)) ++
      [false, true]
    let archiveTail := flattenPairs (rest.flatMap freshSourceBlock)
    let trailer := [true, false, false, true] ++
      List.replicate bits.length true ++ archiveTail
    let mcf := run masterM (literalLookupClock w l)
      (init masterM (bits ++ trailer))
    let z := decide (rest ≠ [])
    let markerPre := flattenPairs pairs ++ [false, true, false, true]
    run runtimeMarkedContinuationMachine
        (runtimeMarkedContinuationClock pairs d l)
        (init runtimeMarkedContinuationMachine
          (markerPre ++ sourcePre ++ mcf.tp)) =
      ⟨Sum.inr (done z),
        markerPre.length + (sourcePre.length + 2 * bits.length + 6),
        markerPre ++ sourcePre ++ mcf.tp⟩ := by
  dsimp only
  let bits := literalLookupTape w l
  let d := (bits :: rest).length
  let sourcePre := flattenPairs (List.replicate d (true, true)) ++
    [false, true]
  let archiveTail := flattenPairs (rest.flatMap freshSourceBlock)
  let trailer := [true, false, false, true] ++
    List.replicate bits.length true ++ archiveTail
  let mcf := run masterM (literalLookupClock w l)
    (init masterM (bits ++ trailer))
  let z := decide (rest ≠ [])
  let tail := sourcePre ++ mcf.tp
  have htail : tail = true :: true :: tail.drop 2 := by
    simp [tail, sourcePre, d, List.replicate_succ, flattenPairs,
      List.append_assoc]
  have hrun := masterM_literal_continuationLocate w l rest
  have hrun' : run runtimeContinuationLocatorMachine
      (runtimeContinuationLocatorClock d l)
      (init runtimeContinuationLocatorMachine tail) =
      ⟨done z, sourcePre.length + 2 * bits.length + 6, tail⟩ := by
    simpa [bits, d, sourcePre, archiveTail, trailer, mcf, z, tail] using hrun
  have hjoined := runtimeMarkedAcceptBody_run
    runtimeContinuationLocatorMachine pairs tail tail true true hsafe htail
    (by simp [runtimePairIsSep])
    (runtimeContinuationLocatorClock d l) (done z)
    (sourcePre.length + 2 * bits.length + 6) hrun' rfl
    (runtimeContinuationLocator_prefixSafe tail _)
  simpa [runtimeMarkedContinuationMachine, runtimeMarkedContinuationClock,
    bits, d, sourcePre, archiveTail, trailer, mcf, z, tail,
    List.append_assoc] using hjoined

theorem runtimeMarkedContinuation_accept (z : Bool) :
    runtimeMarkedContinuationMachine.accept (Sum.inr (done z)) = z := by
  rfl

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeContinuationLocator

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeContinuationLocator.runtimeContinuationLocator_run
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeContinuationLocator.runtimeContinuationLocator_prefixSafe
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeContinuationLocator.masterM_literal_continuationLocate
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeContinuationLocator.runtimeMarkedContinuation_run
