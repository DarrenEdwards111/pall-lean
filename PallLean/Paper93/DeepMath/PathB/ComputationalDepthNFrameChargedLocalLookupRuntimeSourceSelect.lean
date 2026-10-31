import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeStage

/-!
# Charged local lookup: fixed runtime source selector

The runtime stager still received a finite-control schedule table.  This file
moves that table to tape.  A single fixed machine consumes one marked
countdown pair at a time and marks one archive entry as passed.  After all
countdown marks are consumed it halts at the payload of the selected archive
entry.

Payloads are stored doubled.  Consequently `10` is available as an entry
marker, while payload pairs are only `00`/`11` and their terminators are `01`.
Changing a passed entry marker from `10` to `11` never changes any source
payload cell.  The transition table is independent of the capacity, source,
assignment, schedule, and round number.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCompare
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLiteralWeld
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupScheduleBound
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRepeatController
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeStage

/-! ## Pair-level physical layout -/

def flattenPairs : List (Bool × Bool) → List Bool
  | [] => []
  | (a, b) :: ps => a :: b :: flattenPairs ps

@[simp] theorem flattenPairs_length (ps : List (Bool × Bool)) :
    (flattenPairs ps).length = 2 * ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih => cases p; simp [flattenPairs, ih]; omega

@[simp] theorem flattenPairs_append (ps qs : List (Bool × Bool)) :
    flattenPairs (ps ++ qs) = flattenPairs ps ++ flattenPairs qs := by
  induction ps with
  | nil => rfl
  | cons p ps ih => cases p; simp [flattenPairs, ih]

theorem flattenPairs_getD_lo (ps : List (Bool × Bool)) (i : Nat)
    (hi : i < ps.length) :
    (flattenPairs ps).getD (2 * i) false = (ps.getD i (false, false)).1 := by
  induction ps generalizing i with
  | nil => simp at hi
  | cons p ps ih =>
      cases p with
      | mk a b =>
          cases i with
          | zero => rfl
          | succ i =>
              simpa [flattenPairs, show 2 * (i + 1) = 2 * i + 2 by omega]
                using ih i (by simpa using hi)

theorem flattenPairs_getD_hi (ps : List (Bool × Bool)) (i : Nat)
    (hi : i < ps.length) :
    (flattenPairs ps).getD (2 * i + 1) false =
      (ps.getD i (false, false)).2 := by
  induction ps generalizing i with
  | nil => simp at hi
  | cons p ps ih =>
      cases p with
      | mk a b =>
          cases i with
          | zero => rfl
          | succ i =>
              simpa [flattenPairs, show 2 * (i + 1) + 1 = 2 * i + 3 by omega]
                using ih i (by simpa using hi)

theorem writeAt_flattenPairs_hi (ps : List (Bool × Bool)) (i : Nat)
    (hi : i < ps.length) (b : Bool) :
    writeAt (flattenPairs ps) (2 * i + 1) b =
      flattenPairs (ps.set i ((ps.getD i (false, false)).1, b)) := by
  induction ps generalizing i with
  | nil => simp at hi
  | cons p ps ih =>
      cases p with
      | mk a c =>
          cases i with
          | zero => simp [flattenPairs, writeAt]
          | succ i =>
              rw [writeAt_of_lt b (by rw [flattenPairs_length]; omega)]
              rw [show 2 * (i + 1) + 1 = (2 * i + 1) + 2 by omega]
              simp only [flattenPairs, List.getD_cons_succ,
                List.set_cons_succ]
              have hi' : i < ps.length := by
                simp only [List.length_cons] at hi
                omega
              have hw := ih i hi'
              rw [writeAt_of_lt b (by rw [flattenPairs_length]; omega)] at hw
              exact congrArg (fun xs => a :: c :: xs) hw

def dataPairs (bits : List Bool) : List (Bool × Bool) :=
  bits.map fun b => (b, b)

def freshSourceBlock (bits : List Bool) : List (Bool × Bool) :=
  (true, false) :: dataPairs bits ++ [(false, true)]

def passedSourceBlock (bits : List Bool) : List (Bool × Bool) :=
  (true, true) :: dataPairs bits ++ [(false, true)]

def sourceArchive (schedule : List (List Bool)) : List (Bool × Bool) :=
  schedule.flatMap freshSourceBlock

def archiveProgress (schedule : List (List Bool)) (k : Nat) :
    List (Bool × Bool) :=
  (schedule.take k).flatMap passedSourceBlock ++
    (schedule.drop k).flatMap freshSourceBlock

def selectorCount (B j k : Nat) : List (Bool × Bool) :=
  List.replicate k (true, true) ++
    List.replicate (j - k) (true, false) ++
    List.replicate (B - j) (true, true) ++ [(false, true)]

def selectorPairs (B j : Nat) (schedule : List (List Bool)) (k : Nat) :
    List (Bool × Bool) :=
  selectorCount B j k ++ archiveProgress schedule k

def selectorTape (B j : Nat) (schedule : List (List Bool)) (k : Nat) :
    List Bool :=
  flattenPairs (selectorPairs B j schedule k)

def archivePrefixPairs (schedule : List (List Bool)) (k : Nat) : Nat :=
  ((schedule.take k).map fun bits => bits.length + 2).sum

/-! ## The fixed selector machine -/

inductive SourceSelectState
  | cntLo
  | cntHi (lo : Bool)
  | boundaryLo
  | boundaryHi (lo : Bool)
  | advanceLo
  | advanceHi (lo : Bool)
  | selectLo
  | selectHi (lo : Bool)
  | done
  deriving Fintype, DecidableEq

open SourceSelectState

/-- Fixed transition table: no input-dependent finite-state parameters. -/
def sourceSelectMachine : Machine where
  State := SourceSelectState
  fin := inferInstance
  dec := inferInstance
  start := cntLo
  halt
    | done => true
    | _ => false
  δ s b := match s with
    | cntLo => (cntHi b, none, 1)
    | cntHi lo =>
        if lo then
          if !b then (boundaryLo, some true, 3)
          else (cntLo, none, 1)
        else (selectLo, none, 1)
    | boundaryLo => (boundaryHi b, none, 1)
    | boundaryHi lo =>
        if lo then (boundaryLo, none, 1)
        else (advanceLo, none, 1)
    | advanceLo => (advanceHi b, none, 1)
    | advanceHi lo =>
        if lo && !b then (cntLo, some true, 3)
        else (advanceLo, none, 1)
    | selectLo => (selectHi b, none, 1)
    | selectHi lo =>
        if lo && !b then (done, none, 1)
        else (selectLo, none, 1)
    | done => (done, none, 2)
  accept := fun _ => false

theorem cnt_skip_pair (T : List Bool) (p : Nat) (lo hi : Bool)
    (hlo : T.getD p false = lo) (hhi : T.getD (p + 1) false = hi)
    (hl : lo = true) (hn : ¬(lo && !hi)) :
    run sourceSelectMachine 2 ⟨cntLo, p, T⟩ =
      ⟨cntLo, p + 2, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at hlo hhi
  rw [run_succ, run_succ, run_zero]
  have hh : hi = true := by
    cases hi <;> simp_all
  simp [step, sourceSelectMachine, moveHead, hlo, hhi, hl, hh]

theorem cnt_take_mark (T : List Bool) (p : Nat)
    (hlo : T.getD p false = true) (hhi : T.getD (p + 1) false = false) :
    run sourceSelectMachine 2 ⟨cntLo, p, T⟩ =
      ⟨boundaryLo, 0, writeAt T (p + 1) true⟩ := by
  rw [List.getD_eq_getElem?_getD] at hlo hhi
  rw [run_succ, run_succ, run_zero]
  simp [step, sourceSelectMachine, moveHead, hlo, hhi]

theorem cnt_finish (T : List Bool) (p : Nat)
    (hlo : T.getD p false = false) :
    run sourceSelectMachine 2 ⟨cntLo, p, T⟩ =
      ⟨selectLo, p + 2, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at hlo
  rw [run_succ, run_succ, run_zero]
  simp [step, sourceSelectMachine, moveHead, hlo]

theorem boundary_skip_true_pair (T : List Bool) (p : Nat)
    (hlo : T.getD p false = true) :
    run sourceSelectMachine 2 ⟨boundaryLo, p, T⟩ =
      ⟨boundaryLo, p + 2, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at hlo
  rw [run_succ, run_succ, run_zero]
  simp [step, sourceSelectMachine, moveHead, hlo]

theorem boundary_finish (T : List Bool) (p : Nat)
    (hlo : T.getD p false = false) :
    run sourceSelectMachine 2 ⟨boundaryLo, p, T⟩ =
      ⟨advanceLo, p + 2, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at hlo
  rw [run_succ, run_succ, run_zero]
  simp [step, sourceSelectMachine, moveHead, hlo]

theorem advance_skip_pair (T : List Bool) (p : Nat) (lo hi : Bool)
    (hlo : T.getD p false = lo) (hhi : T.getD (p + 1) false = hi)
    (hn : ¬(lo && !hi)) :
    run sourceSelectMachine 2 ⟨advanceLo, p, T⟩ =
      ⟨advanceLo, p + 2, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at hlo hhi
  rw [run_succ, run_succ, run_zero]
  simp [step, sourceSelectMachine, moveHead, hlo, hhi, hn]

theorem advance_take_mark (T : List Bool) (p : Nat)
    (hlo : T.getD p false = true) (hhi : T.getD (p + 1) false = false) :
    run sourceSelectMachine 2 ⟨advanceLo, p, T⟩ =
      ⟨cntLo, 0, writeAt T (p + 1) true⟩ := by
  rw [List.getD_eq_getElem?_getD] at hlo hhi
  rw [run_succ, run_succ, run_zero]
  simp [step, sourceSelectMachine, moveHead, hlo, hhi]

theorem select_skip_pair (T : List Bool) (p : Nat) (lo hi : Bool)
    (hlo : T.getD p false = lo) (hhi : T.getD (p + 1) false = hi)
    (hn : ¬(lo && !hi)) :
    run sourceSelectMachine 2 ⟨selectLo, p, T⟩ =
      ⟨selectLo, p + 2, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at hlo hhi
  rw [run_succ, run_succ, run_zero]
  simp [step, sourceSelectMachine, moveHead, hlo, hhi, hn]

theorem select_take_mark (T : List Bool) (p : Nat)
    (hlo : T.getD p false = true) (hhi : T.getD (p + 1) false = false) :
    run sourceSelectMachine 2 ⟨selectLo, p, T⟩ =
      ⟨done, p + 2, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at hlo hhi
  rw [run_succ, run_succ, run_zero]
  simp [step, sourceSelectMachine, moveHead, hlo, hhi]

/-! ## Pair-stream scans -/

def NoFreshMark (ps : List (Bool × Bool)) : Prop :=
  ∀ p ∈ ps, ¬(p.1 && !p.2)

theorem pair_start_lo (pre : List (Bool × Bool)) (lo hi : Bool)
    (rest : List (Bool × Bool)) :
    (flattenPairs (pre ++ (lo, hi) :: rest)).getD (2 * pre.length) false = lo := by
  rw [flattenPairs_append,
    List.getD_append_right (h := by rw [flattenPairs_length]),
    flattenPairs_length, Nat.sub_self]
  rfl

theorem pair_start_hi (pre : List (Bool × Bool)) (lo hi : Bool)
    (rest : List (Bool × Bool)) :
    (flattenPairs (pre ++ (lo, hi) :: rest)).getD
        (2 * pre.length + 1) false = hi := by
  rw [flattenPairs_append,
    List.getD_append_right (h := by rw [flattenPairs_length]; omega),
    flattenPairs_length]
  rw [show 2 * pre.length + 1 - 2 * pre.length = 1 by omega]
  rfl

theorem cnt_skip_pairStream (pre ps post : List (Bool × Bool))
    (hn : NoFreshMark ps) (hl : ∀ p ∈ ps, p.1 = true) :
    run sourceSelectMachine (2 * ps.length)
        ⟨cntLo, 2 * pre.length, flattenPairs (pre ++ ps ++ post)⟩ =
      ⟨cntLo, 2 * (pre.length + ps.length),
        flattenPairs (pre ++ ps ++ post)⟩ := by
  induction ps generalizing pre with
  | nil => simp
  | cons p ps ih =>
      rcases p with ⟨lo, hi⟩
      have hpair : ¬(lo && !hi) := hn (lo, hi) (by simp)
      have hlpair : lo = true := hl (lo, hi) (by simp)
      have htail : NoFreshMark ps := by
        intro q hq
        exact hn q (by simp [hq])
      have hltail : ∀ p ∈ ps, p.1 = true := by
        intro q hq
        exact hl q (by simp [hq])
      rw [show 2 * ((lo, hi) :: ps).length = 2 + 2 * ps.length by simp; omega,
        run_add]
      have hlo' :
          (flattenPairs (pre ++ (lo, hi) :: ps ++ post)).getD
            (2 * pre.length) false = lo := by
        simpa [List.append_assoc] using pair_start_lo pre lo hi (ps ++ post)
      have hhi' :
          (flattenPairs (pre ++ (lo, hi) :: ps ++ post)).getD
            (2 * pre.length + 1) false = hi := by
        simpa [List.append_assoc] using pair_start_hi pre lo hi (ps ++ post)
      have hstep := cnt_skip_pair
        (flattenPairs (pre ++ (lo, hi) :: ps ++ post))
        (2 * pre.length) lo hi hlo' hhi' hlpair hpair
      rw [hstep]
      have hs : 2 * pre.length + 2 = 2 * (pre.length + 1) := by omega
      have he : 2 * (pre.length + ((lo, hi) :: ps).length) =
          2 * (pre.length + 1 + ps.length) := by simp; omega
      rw [hs, he]
      simpa [List.append_assoc] using ih (pre ++ [(lo, hi)]) htail hltail

theorem boundary_skip_pairStream (pre ps post : List (Bool × Bool))
    (hlo : ∀ p ∈ ps, p.1 = true) :
    run sourceSelectMachine (2 * ps.length)
        ⟨boundaryLo, 2 * pre.length, flattenPairs (pre ++ ps ++ post)⟩ =
      ⟨boundaryLo, 2 * (pre.length + ps.length),
        flattenPairs (pre ++ ps ++ post)⟩ := by
  induction ps generalizing pre with
  | nil => simp
  | cons p ps ih =>
      rcases p with ⟨lo, hi⟩
      have hp : lo = true := hlo (lo, hi) (by simp)
      have htail : ∀ p ∈ ps, p.1 = true := by
        intro q hq
        exact hlo q (by simp [hq])
      rw [show 2 * ((lo, hi) :: ps).length = 2 + 2 * ps.length by simp; omega,
        run_add]
      have hread :
          (flattenPairs (pre ++ (lo, hi) :: ps ++ post)).getD
            (2 * pre.length) false = true := by
        simpa [List.append_assoc, hp] using pair_start_lo pre lo hi (ps ++ post)
      have hstep := boundary_skip_true_pair
        (flattenPairs (pre ++ (lo, hi) :: ps ++ post))
        (2 * pre.length) hread
      rw [hstep]
      have hs : 2 * pre.length + 2 = 2 * (pre.length + 1) := by omega
      have he : 2 * (pre.length + ((lo, hi) :: ps).length) =
          2 * (pre.length + 1 + ps.length) := by simp; omega
      rw [hs, he]
      simpa [List.append_assoc] using ih (pre ++ [(lo, hi)]) htail

theorem advance_skip_pairStream (pre ps post : List (Bool × Bool))
    (hn : NoFreshMark ps) :
    run sourceSelectMachine (2 * ps.length)
        ⟨advanceLo, 2 * pre.length, flattenPairs (pre ++ ps ++ post)⟩ =
      ⟨advanceLo, 2 * (pre.length + ps.length),
        flattenPairs (pre ++ ps ++ post)⟩ := by
  induction ps generalizing pre with
  | nil => simp
  | cons p ps ih =>
      rcases p with ⟨lo, hi⟩
      have hpair : ¬(lo && !hi) := hn (lo, hi) (by simp)
      have htail : NoFreshMark ps := by
        intro q hq
        exact hn q (by simp [hq])
      rw [show 2 * ((lo, hi) :: ps).length = 2 + 2 * ps.length by simp; omega,
        run_add]
      have hlo' :
          (flattenPairs (pre ++ (lo, hi) :: ps ++ post)).getD
            (2 * pre.length) false = lo := by
        simpa [List.append_assoc] using pair_start_lo pre lo hi (ps ++ post)
      have hhi' :
          (flattenPairs (pre ++ (lo, hi) :: ps ++ post)).getD
            (2 * pre.length + 1) false = hi := by
        simpa [List.append_assoc] using pair_start_hi pre lo hi (ps ++ post)
      have hstep := advance_skip_pair
        (flattenPairs (pre ++ (lo, hi) :: ps ++ post))
        (2 * pre.length) lo hi hlo' hhi' hpair
      rw [hstep]
      have hs : 2 * pre.length + 2 = 2 * (pre.length + 1) := by omega
      have he : 2 * (pre.length + ((lo, hi) :: ps).length) =
          2 * (pre.length + 1 + ps.length) := by simp; omega
      rw [hs, he]
      simpa [List.append_assoc] using ih (pre ++ [(lo, hi)]) htail

theorem select_skip_pairStream (pre ps post : List (Bool × Bool))
    (hn : NoFreshMark ps) :
    run sourceSelectMachine (2 * ps.length)
        ⟨selectLo, 2 * pre.length, flattenPairs (pre ++ ps ++ post)⟩ =
      ⟨selectLo, 2 * (pre.length + ps.length),
        flattenPairs (pre ++ ps ++ post)⟩ := by
  induction ps generalizing pre with
  | nil => simp
  | cons p ps ih =>
      rcases p with ⟨lo, hi⟩
      have hpair : ¬(lo && !hi) := hn (lo, hi) (by simp)
      have htail : NoFreshMark ps := by
        intro q hq
        exact hn q (by simp [hq])
      rw [show 2 * ((lo, hi) :: ps).length = 2 + 2 * ps.length by simp; omega,
        run_add]
      have hlo' :
          (flattenPairs (pre ++ (lo, hi) :: ps ++ post)).getD
            (2 * pre.length) false = lo := by
        simpa [List.append_assoc] using pair_start_lo pre lo hi (ps ++ post)
      have hhi' :
          (flattenPairs (pre ++ (lo, hi) :: ps ++ post)).getD
            (2 * pre.length + 1) false = hi := by
        simpa [List.append_assoc] using pair_start_hi pre lo hi (ps ++ post)
      have hstep := select_skip_pair
        (flattenPairs (pre ++ (lo, hi) :: ps ++ post))
        (2 * pre.length) lo hi hlo' hhi' hpair
      rw [hstep]
      have hs : 2 * pre.length + 2 = 2 * (pre.length + 1) := by omega
      have he : 2 * (pre.length + ((lo, hi) :: ps).length) =
          2 * (pre.length + 1 + ps.length) := by simp; omega
      rw [hs, he]
      simpa [List.append_assoc] using ih (pre ++ [(lo, hi)]) htail

/-! ## Exact source-selection cycles -/

theorem dataPairs_noFresh (bits : List Bool) : NoFreshMark (dataPairs bits) := by
  intro p hp
  simp only [dataPairs, List.mem_map] at hp
  obtain ⟨b, _, rfl⟩ := hp
  cases b <;> simp

theorem passedSourceBlock_noFresh (bits : List Bool) :
    NoFreshMark (passedSourceBlock bits) := by
  intro p hp
  rw [passedSourceBlock] at hp
  rcases List.mem_cons.mp hp with rfl | hp
  · simp
  · rcases List.mem_append.mp hp with hp | hp
    · exact dataPairs_noFresh bits p hp
    · rcases List.mem_singleton.mp hp with rfl
      simp

theorem passedArchive_noFresh (done : List (List Bool)) :
    NoFreshMark (done.flatMap passedSourceBlock) := by
  intro p hp
  simp only [List.mem_flatMap] at hp
  obtain ⟨bits, _, hp⟩ := hp
  exact passedSourceBlock_noFresh bits p hp

def cycleInputPairs (k r d : Nat) (done : List (List Bool))
    (bits : List Bool) (rest : List (List Bool)) : List (Bool × Bool) :=
  List.replicate k (true, true) ++
    (true, false) :: List.replicate r (true, false) ++
    List.replicate d (true, true) ++ [(false, true)] ++
    done.flatMap passedSourceBlock ++ freshSourceBlock bits ++
    rest.flatMap freshSourceBlock

def cycleCountMarkedPairs (k r d : Nat) (done : List (List Bool))
    (bits : List Bool) (rest : List (List Bool)) : List (Bool × Bool) :=
  List.replicate (k + 1) (true, true) ++
    List.replicate r (true, false) ++
    List.replicate d (true, true) ++ [(false, true)] ++
    done.flatMap passedSourceBlock ++ freshSourceBlock bits ++
    rest.flatMap freshSourceBlock

def cycleOutputPairs (k r d : Nat) (done : List (List Bool))
    (bits : List Bool) (rest : List (List Bool)) : List (Bool × Bool) :=
  List.replicate (k + 1) (true, true) ++
    List.replicate r (true, false) ++
    List.replicate d (true, true) ++ [(false, true)] ++
    done.flatMap passedSourceBlock ++ passedSourceBlock bits ++
    rest.flatMap freshSourceBlock

@[simp] theorem cycleInputPairs_length_pos (k r d : Nat)
    (done : List (List Bool)) (bits : List Bool) (rest : List (List Bool)) :
    k < (cycleInputPairs k r d done bits rest).length := by
  simp [cycleInputPairs]

theorem set_fresh_header (A tail : List (Bool × Bool)) :
    (A ++ (true, false) :: tail).set A.length
        ((((A ++ (true, false) :: tail).getD A.length (false, false)).1), true) =
      A ++ (true, true) :: tail := by
  have hg := getD_append_left_length' A ((true, false) :: tail) rfl
    0 (false, false)
  simp only [Nat.add_zero] at hg
  have hg' : (A ++ (true, false) :: tail).getD A.length (false, false) =
      (true, false) := hg
  rw [hg']
  have hs := set_append_left_length' A ((true, false) :: tail) rfl
    0 (true, true)
  simp only [Nat.add_zero] at hs
  exact hs

theorem cycle_count_write (k r d : Nat) (done : List (List Bool))
    (bits : List Bool) (rest : List (List Bool)) :
    writeAt (flattenPairs (cycleInputPairs k r d done bits rest))
        (2 * k + 1) true =
      flattenPairs (cycleCountMarkedPairs k r d done bits rest) := by
  rw [writeAt_flattenPairs_hi _ k (cycleInputPairs_length_pos _ _ _ _ _ _) true]
  congr 1
  let A := List.replicate k (true, true)
  let tail := List.replicate r (true, false) ++
    List.replicate d (true, true) ++ [(false, true)] ++
    done.flatMap passedSourceBlock ++ freshSourceBlock bits ++
    rest.flatMap freshSourceBlock
  have hin : cycleInputPairs k r d done bits rest =
      A ++ (true, false) :: tail := by
    simp [cycleInputPairs, A, tail, List.append_assoc]
  have hout : cycleCountMarkedPairs k r d done bits rest =
      A ++ (true, true) :: tail := by
    rw [cycleCountMarkedPairs, List.replicate_succ']
    simp [A, tail, List.append_assoc]
  have hk : k = A.length := by simp [A]
  rw [hin, hout, hk]
  exact set_fresh_header A tail

theorem cycle_archive_write (k r d : Nat) (done : List (List Bool))
    (bits : List Bool) (rest : List (List Bool)) :
    let ps := cycleCountMarkedPairs k r d done bits rest
    let q := k + 1 + r + d + 1 + (done.flatMap passedSourceBlock).length
    writeAt (flattenPairs ps) (2 * q + 1) true =
      flattenPairs (cycleOutputPairs k r d done bits rest) := by
  dsimp only
  let A := List.replicate (k + 1) (true, true) ++
    List.replicate r (true, false) ++ List.replicate d (true, true) ++
    [(false, true)] ++ done.flatMap passedSourceBlock
  let tail := dataPairs bits ++ [(false, true)] ++ rest.flatMap freshSourceBlock
  have hq : k + 1 + r + d + 1 + (done.flatMap passedSourceBlock).length =
      A.length := by simp [A]; omega
  have hform : cycleCountMarkedPairs k r d done bits rest =
      A ++ (true, false) :: tail := by
    simp [cycleCountMarkedPairs, A, tail, freshSourceBlock, List.append_assoc]
  have hout : cycleOutputPairs k r d done bits rest =
      A ++ (true, true) :: tail := by
    simp [cycleOutputPairs, A, tail, passedSourceBlock, List.append_assoc]
  rw [hq, writeAt_flattenPairs_hi _ A.length (by rw [hform]; simp) true]
  congr 1
  rw [hform, hout]
  exact set_fresh_header A tail

def sourceSelectCycleClock (k r d : Nat) (done : List (List Bool)) : Nat :=
  (2 * k + 2) +
    (2 * (k + 1 + r + d) + 2) +
    (2 * (done.flatMap passedSourceBlock).length + 2)

/-- One destructive metadata cycle: consume one countdown `10`, mark one
archive header passed, preserve every payload, and reset to the origin. -/
theorem sourceSelect_cycle (k r d : Nat) (done : List (List Bool))
    (bits : List Bool) (rest : List (List Bool)) :
    run sourceSelectMachine (sourceSelectCycleClock k r d done)
        ⟨cntLo, 0, flattenPairs (cycleInputPairs k r d done bits rest)⟩ =
      ⟨cntLo, 0, flattenPairs (cycleOutputPairs k r d done bits rest)⟩ := by
  let old := cycleInputPairs k r d done bits rest
  let mid := cycleCountMarkedPairs k r d done bits rest
  let new := cycleOutputPairs k r d done bits rest
  have hcnt : NoFreshMark (List.replicate k (true, true)) := by
    intro p hp
    rcases List.mem_replicate.mp hp with ⟨_, rfl⟩
    simp
  have hskipCnt := cnt_skip_pairStream []
    (List.replicate k (true, true))
    ((true, false) :: List.replicate r (true, false) ++
      List.replicate d (true, true) ++ [(false, true)] ++
      done.flatMap passedSourceBlock ++ freshSourceBlock bits ++
      rest.flatMap freshSourceBlock) hcnt (by
        intro p hp
        rcases List.mem_replicate.mp hp with ⟨_, rfl⟩
        rfl)
  have hloCnt : (flattenPairs old).getD (2 * k) false = true := by
    unfold old cycleInputPairs
    simpa [List.append_assoc] using
      pair_start_lo (List.replicate k (true, true)) true false
        (List.replicate r (true, false) ++ List.replicate d (true, true) ++
          [(false, true)] ++ done.flatMap passedSourceBlock ++
          freshSourceBlock bits ++ rest.flatMap freshSourceBlock)
  have hhiCnt : (flattenPairs old).getD (2 * k + 1) false = false := by
    unfold old cycleInputPairs
    simpa [List.append_assoc] using
      pair_start_hi (List.replicate k (true, true)) true false
        (List.replicate r (true, false) ++ List.replicate d (true, true) ++
          [(false, true)] ++ done.flatMap passedSourceBlock ++
          freshSourceBlock bits ++ rest.flatMap freshSourceBlock)
  have hmarkCnt := cnt_take_mark (flattenPairs old) (2 * k) hloCnt hhiCnt
  have hcountWrite : writeAt (flattenPairs old) (2 * k + 1) true =
      flattenPairs mid := by
    exact cycle_count_write k r d done bits rest
  have hdataLo : ∀ p ∈
      (List.replicate (k + 1) (true, true) ++
        List.replicate r (true, false) ++ List.replicate d (true, true)),
    p.1 = true := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · rcases List.mem_append.mp hp with hp | hp
      · rcases List.mem_replicate.mp hp with ⟨_, rfl⟩
        rfl
      · rcases List.mem_replicate.mp hp with ⟨_, rfl⟩
        rfl
    · rcases List.mem_replicate.mp hp with ⟨_, rfl⟩
      rfl
  have hboundary := boundary_skip_pairStream []
    (List.replicate (k + 1) (true, true) ++
      List.replicate r (true, false) ++ List.replicate d (true, true))
    ((false, true) :: done.flatMap passedSourceBlock ++
      freshSourceBlock bits ++ rest.flatMap freshSourceBlock) hdataLo
  have hloBound : (flattenPairs mid).getD
      (2 * (k + 1 + r + d)) false = false := by
    unfold mid cycleCountMarkedPairs
    have hh := pair_start_lo
      (List.replicate (k + 1) (true, true) ++
        List.replicate r (true, false) ++ List.replicate d (true, true))
      false true (done.flatMap passedSourceBlock ++ freshSourceBlock bits ++
        rest.flatMap freshSourceBlock)
    have he : 2 * (k + 1 + (r + d)) = 2 * (k + 1 + r + d) := by omega
    simpa [List.append_assoc, he] using hh
  have hfinish := boundary_finish (flattenPairs mid)
    (2 * (k + 1 + r + d)) hloBound
  have hadvance := advance_skip_pairStream
    (List.replicate (k + 1) (true, true) ++
      List.replicate r (true, false) ++ List.replicate d (true, true) ++
      [(false, true)]) (done.flatMap passedSourceBlock)
    (freshSourceBlock bits ++ rest.flatMap freshSourceBlock)
    (passedArchive_noFresh done)
  let q := k + 1 + r + d + 1 + (done.flatMap passedSourceBlock).length
  let archivePre := List.replicate (k + 1) (true, true) ++
    List.replicate r (true, false) ++ List.replicate d (true, true) ++
    [(false, true)] ++ done.flatMap passedSourceBlock
  have harchivePre : archivePre.length = q := by
    simp [archivePre, q]
    omega
  have hloArchive : (flattenPairs mid).getD (2 * q) false = true := by
    unfold mid cycleCountMarkedPairs
    have hh := pair_start_lo archivePre
      true false (dataPairs bits ++ [(false, true)] ++
        rest.flatMap freshSourceBlock)
    rw [harchivePre] at hh
    simpa [archivePre, List.append_assoc, freshSourceBlock] using hh
  have hhiArchive : (flattenPairs mid).getD (2 * q + 1) false = false := by
    unfold mid cycleCountMarkedPairs
    have hh := pair_start_hi archivePre
      true false (dataPairs bits ++ [(false, true)] ++
        rest.flatMap freshSourceBlock)
    rw [harchivePre] at hh
    simpa [archivePre, List.append_assoc, freshSourceBlock] using hh
  have hmarkArchive := advance_take_mark (flattenPairs mid) (2 * q)
    hloArchive hhiArchive
  have harchiveWrite : writeAt (flattenPairs mid) (2 * q + 1) true =
      flattenPairs new := by
    exact cycle_archive_write k r d done bits rest
  have hskipCnt' :
      run sourceSelectMachine (2 * k)
        ⟨cntLo, 0, flattenPairs old⟩ =
      ⟨cntLo, 2 * k, flattenPairs old⟩ := by
    simpa [old, cycleInputPairs, List.append_assoc] using hskipCnt
  have hboundary' :
      run sourceSelectMachine (2 * (k + 1 + r + d))
        ⟨boundaryLo, 0, flattenPairs mid⟩ =
      ⟨boundaryLo, 2 * (k + 1 + r + d), flattenPairs mid⟩ := by
    have he : k + 1 + (r + d) = k + 1 + r + d := by omega
    simpa [mid, cycleCountMarkedPairs, List.append_assoc, he] using hboundary
  have hadvance' :
      run sourceSelectMachine (2 * (done.flatMap passedSourceBlock).length)
        ⟨advanceLo, 2 * (k + 1 + r + d) + 2, flattenPairs mid⟩ =
      ⟨advanceLo, 2 * q, flattenPairs mid⟩ := by
    have hs : 2 * (k + 1 + (r + (d + 1))) =
        2 * (k + 1 + r + d) + 2 := by omega
    have he : 2 * (k + 1 + (r + (d + 1)) +
        (done.flatMap passedSourceBlock).length) =
        2 * (k + 1 + r + d + 1 +
          (done.flatMap passedSourceBlock).length) := by omega
    have he2 : 2 * (k + 1 + (r + (d + 1)) +
        (done.map fun a => (passedSourceBlock a).length).sum) =
        2 * (k + 1 + r + d + 1 +
          (done.map fun a => (passedSourceBlock a).length).sum) := by omega
    simpa [mid, cycleCountMarkedPairs, q, List.append_assoc, hs, he, he2] using hadvance
  have hfirst :
      run sourceSelectMachine (2 * k + 2)
        ⟨cntLo, 0, flattenPairs old⟩ =
      ⟨boundaryLo, 0, flattenPairs mid⟩ := by
    rw [run_add, hskipCnt', hmarkCnt, hcountWrite]
  have hsecond :
      run sourceSelectMachine (2 * (k + 1 + r + d) + 2)
        ⟨boundaryLo, 0, flattenPairs mid⟩ =
      ⟨advanceLo, 2 * (k + 1 + r + d) + 2, flattenPairs mid⟩ := by
    rw [run_add, hboundary', hfinish]
  have hthird :
      run sourceSelectMachine
        (2 * (done.flatMap passedSourceBlock).length + 2)
        ⟨advanceLo, 2 * (k + 1 + r + d) + 2, flattenPairs mid⟩ =
      ⟨cntLo, 0, flattenPairs new⟩ := by
    rw [run_add, hadvance', hmarkArchive, harchiveWrite]
  unfold sourceSelectCycleClock
  rw [show (2 * k + 2) + (2 * (k + 1 + r + d) + 2) +
      (2 * (done.flatMap passedSourceBlock).length + 2) =
      2 * k + 2 + (2 * (k + 1 + r + d) + 2 +
        (2 * (done.flatMap passedSourceBlock).length + 2)) by omega,
    run_add]
  rw [hfirst, run_add, hsecond, hthird]

/-! ## Arbitrarily many source-selection cycles -/

def progressPairs (d : Nat) (done todo future : List (List Bool)) :
    List (Bool × Bool) :=
  List.replicate done.length (true, true) ++
    List.replicate todo.length (true, false) ++
    List.replicate d (true, true) ++ [(false, true)] ++
    done.flatMap passedSourceBlock ++
    (todo ++ future).flatMap freshSourceBlock

def sourceSelectRoundsClock (d : Nat) (done : List (List Bool)) :
    List (List Bool) → Nat
  | [] => 0
  | bits :: rest =>
      sourceSelectCycleClock done.length rest.length d done +
        sourceSelectRoundsClock d (done ++ [bits]) rest

theorem cycleInputPairs_progress (d : Nat) (done : List (List Bool))
    (bits : List Bool) (rest future : List (List Bool)) :
    cycleInputPairs done.length rest.length d done bits (rest ++ future) =
      progressPairs d done (bits :: rest) future := by
  simp [cycleInputPairs, progressPairs, List.replicate_succ,
    List.flatMap_append, List.append_assoc]

theorem cycleOutputPairs_progress (d : Nat) (done : List (List Bool))
    (bits : List Bool) (rest future : List (List Bool)) :
    cycleOutputPairs done.length rest.length d done bits (rest ++ future) =
      progressPairs d (done ++ [bits]) rest future := by
  simp [cycleOutputPairs, progressPairs, List.replicate_succ',
    passedSourceBlock, List.flatMap_append, List.append_assoc]

theorem sourceSelect_rounds (d : Nat) (done todo future : List (List Bool)) :
    run sourceSelectMachine (sourceSelectRoundsClock d done todo)
        ⟨cntLo, 0, flattenPairs (progressPairs d done todo future)⟩ =
      ⟨cntLo, 0,
        flattenPairs (progressPairs d (done ++ todo) [] future)⟩ := by
  induction todo generalizing done with
  | nil => simp [sourceSelectRoundsClock]
  | cons bits rest ih =>
      rw [sourceSelectRoundsClock, run_add,
        ← cycleInputPairs_progress d done bits rest future,
        sourceSelect_cycle done.length rest.length d done bits (rest ++ future),
        cycleOutputPairs_progress d done bits rest future,
        ih (done ++ [bits])]
      simp [List.append_assoc]

def sourceSelectFinalClock (d : Nat) (done : List (List Bool)) : Nat :=
  (2 * (done.length + d) + 2) +
    (2 * (done.flatMap passedSourceBlock).length + 2)

/-- Once all marked countdown pairs have been consumed, the fixed machine
crosses the normalized countdown and passed archive prefix and halts exactly
at the selected payload's first doubled data cell. -/
theorem sourceSelect_final (d : Nat) (done : List (List Bool))
    (bits : List Bool) (rest : List (List Bool)) :
    run sourceSelectMachine (sourceSelectFinalClock d done)
        ⟨cntLo, 0,
          flattenPairs (progressPairs d done [] (bits :: rest))⟩ =
      ⟨SourceSelectState.done, 2 * (done.length + d + 1 +
          (done.flatMap passedSourceBlock).length + 1),
        flattenPairs (progressPairs d done [] (bits :: rest))⟩ := by
  let T := flattenPairs (progressPairs d done [] (bits :: rest))
  let cnt := List.replicate done.length (true, true) ++
    List.replicate d (true, true)
  have hcntNo : NoFreshMark cnt := by
    intro p hp
    unfold cnt at hp
    rcases List.mem_append.mp hp with hp | hp
    · rcases List.mem_replicate.mp hp with ⟨_, rfl⟩; simp
    · rcases List.mem_replicate.mp hp with ⟨_, rfl⟩; simp
  have hcntLo : ∀ p ∈ cnt, p.1 = true := by
    intro p hp
    unfold cnt at hp
    rcases List.mem_append.mp hp with hp | hp
    · rcases List.mem_replicate.mp hp with ⟨_, rfl⟩; rfl
    · rcases List.mem_replicate.mp hp with ⟨_, rfl⟩; rfl
  have hscan := cnt_skip_pairStream [] cnt
    ((false, true) :: done.flatMap passedSourceBlock ++
      freshSourceBlock bits ++ rest.flatMap freshSourceBlock) hcntNo hcntLo
  have hloBoundary : T.getD (2 * (done.length + d)) false = false := by
    unfold T progressPairs
    simpa [List.append_assoc] using pair_start_lo
      (List.replicate done.length (true, true) ++
        List.replicate d (true, true)) false true
      (done.flatMap passedSourceBlock ++ freshSourceBlock bits ++
        rest.flatMap freshSourceBlock)
  have hfinish := cnt_finish T (2 * (done.length + d)) hloBoundary
  have hpassed := select_skip_pairStream
    (List.replicate (done.length + d) (true, true) ++ [(false, true)])
    (done.flatMap passedSourceBlock)
    (freshSourceBlock bits ++ rest.flatMap freshSourceBlock)
    (passedArchive_noFresh done)
  let q := done.length + d + 1 + (done.flatMap passedSourceBlock).length
  have hloArchive : T.getD (2 * q) false = true := by
    unfold T progressPairs q
    have he : done.length + d +
        ((done.flatMap passedSourceBlock).length + 1) = q := by
      unfold q
      omega
    have he2 : done.length + d +
        ((done.map fun a => (passedSourceBlock a).length).sum + 1) =
        done.length + d + 1 +
          (done.map fun a => (passedSourceBlock a).length).sum := by omega
    simpa [List.append_assoc, freshSourceBlock, he, he2] using
      pair_start_lo
        (List.replicate done.length (true, true) ++
          List.replicate d (true, true) ++ [(false, true)] ++
          done.flatMap passedSourceBlock) true false
        (dataPairs bits ++ [(false, true)] ++ rest.flatMap freshSourceBlock)
  have hhiArchive : T.getD (2 * q + 1) false = false := by
    unfold T progressPairs q
    have he : done.length + d +
        ((done.flatMap passedSourceBlock).length + 1) = q := by
      unfold q
      omega
    have he2 : done.length + d +
        ((done.map fun a => (passedSourceBlock a).length).sum + 1) =
        done.length + d + 1 +
          (done.map fun a => (passedSourceBlock a).length).sum := by omega
    simpa [List.append_assoc, freshSourceBlock, he, he2] using
      pair_start_hi
        (List.replicate done.length (true, true) ++
          List.replicate d (true, true) ++ [(false, true)] ++
          done.flatMap passedSourceBlock) true false
        (dataPairs bits ++ [(false, true)] ++ rest.flatMap freshSourceBlock)
  have htake := select_take_mark T (2 * q) hloArchive hhiArchive
  have hscan' :
      run sourceSelectMachine (2 * (done.length + d))
        ⟨cntLo, 0, T⟩ =
      ⟨cntLo, 2 * (done.length + d), T⟩ := by
    simpa [T, cnt, progressPairs, List.append_assoc] using hscan
  have hpassed' :
      run sourceSelectMachine (2 * (done.flatMap passedSourceBlock).length)
        ⟨selectLo, 2 * (done.length + d) + 2, T⟩ =
      ⟨selectLo, 2 * q, T⟩ := by
    have hs : 2 * (done.length + d + 1) = 2 * (done.length + d) + 2 := by
      omega
    have he : 2 * (done.length + d + 1 +
        (done.flatMap passedSourceBlock).length) = 2 * q := by
      unfold q
      omega
    simpa [T, progressPairs, q, List.append_assoc, hs, he] using hpassed
  have hfirst :
      run sourceSelectMachine (2 * (done.length + d) + 2)
        ⟨cntLo, 0, T⟩ =
      ⟨selectLo, 2 * (done.length + d) + 2, T⟩ := by
    rw [run_add, hscan', hfinish]
  have hsecond :
      run sourceSelectMachine
        (2 * (done.flatMap passedSourceBlock).length + 2)
        ⟨selectLo, 2 * (done.length + d) + 2, T⟩ =
      ⟨SourceSelectState.done, 2 * q + 2, T⟩ := by
    rw [run_add, hpassed', htake]
  unfold sourceSelectFinalClock
  rw [run_add, hfirst, hsecond]
  unfold q T
  congr 2

def sourceSelectClock (d : Nat) (preBlocks : List (List Bool)) : Nat :=
  sourceSelectRoundsClock d [] preBlocks + sourceSelectFinalClock d preBlocks

/-- Complete fixed source selection.  The transition table receives no
schedule parameter: the prefix length is represented only by live `10`
countdown pairs, and all payload blocks remain byte-for-byte unchanged. -/
theorem sourceSelect_run (d : Nat) (preBlocks : List (List Bool))
    (bits : List Bool) (rest : List (List Bool)) :
    run sourceSelectMachine (sourceSelectClock d preBlocks)
        (init sourceSelectMachine
          (flattenPairs (progressPairs d [] preBlocks (bits :: rest)))) =
      ⟨SourceSelectState.done,
        2 * (preBlocks.length + d + 1 +
          (preBlocks.flatMap passedSourceBlock).length + 1),
        flattenPairs (progressPairs d preBlocks [] (bits :: rest))⟩ := by
  rw [sourceSelectClock, run_add]
  change run sourceSelectMachine (sourceSelectFinalClock d preBlocks)
      (run sourceSelectMachine (sourceSelectRoundsClock d [] preBlocks)
        ⟨cntLo, 0, flattenPairs (progressPairs d [] preBlocks (bits :: rest))⟩) = _
  rw [sourceSelect_rounds d [] preBlocks (bits :: rest)]
  simpa using sourceSelect_final d preBlocks bits rest

theorem flattenPairs_dataPairs (bits : List Bool) :
    flattenPairs (dataPairs bits ++ [(false, true)]) = encodeD bits := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
      change b :: b :: flattenPairs (dataPairs bits ++ [(false, true)]) =
        b :: b :: encodeD bits
      rw [ih]

/-- At the halting head, the selected source block is exactly the doubled
canonical payload, followed by the untouched later archive. -/
theorem sourceSelect_selected_suffix (d : Nat) (preBlocks : List (List Bool))
    (bits : List Bool) (rest : List (List Bool)) :
    let cf := run sourceSelectMachine (sourceSelectClock d preBlocks)
      (init sourceSelectMachine
        (flattenPairs (progressPairs d [] preBlocks (bits :: rest))))
    cf.tp.drop cf.hd = encodeD bits ++ flattenPairs (rest.flatMap freshSourceBlock) := by
  rw [sourceSelect_run]
  dsimp only
  let pre : List (Bool × Bool) :=
    List.replicate preBlocks.length (true, true) ++
      List.replicate d (true, true) ++ [(false, true)] ++
      preBlocks.flatMap passedSourceBlock ++ [(true, false)]
  have hpre : pre.length = preBlocks.length + d + 1 +
      (preBlocks.flatMap passedSourceBlock).length + 1 := by
    simp [pre]
    omega
  have htape : progressPairs d preBlocks [] (bits :: rest) =
      pre ++ (dataPairs bits ++ [(false, true)] ++
        rest.flatMap freshSourceBlock) := by
    simp [progressPairs, pre, freshSourceBlock, List.append_assoc]
  have hlen : (flattenPairs pre).length =
      2 * (preBlocks.length + d + 1 +
        (preBlocks.flatMap passedSourceBlock).length + 1) := by
    rw [flattenPairs_length, hpre]
  rw [htape, flattenPairs_append, ← hlen, List.drop_left]
  rw [flattenPairs_append (dataPairs bits ++ [(false, true)])
      (rest.flatMap freshSourceBlock),
    flattenPairs_dataPairs]

def sourceSelectorInput (B t : Nat) (schedule : List (List Bool)) : List Bool :=
  flattenPairs
    (List.replicate t (true, false) ++
      List.replicate (B - t) (true, true) ++ [(false, true)] ++
      sourceArchive schedule)

/-- Canonical archive specialization: a single fixed machine locates the
exact scheduled lookup payload using only tape metadata. -/
theorem sourceSelect_scheduled (x w : List Bool) {t : Nat}
    (ht : t < (decodedLiterals x).length) :
    let B := (decodedLiterals x).length
    let schedule := literalTapeSchedule x w
    let preBlocks := schedule.take t
    let bits := literalLookupTape w (scheduledLiteral x t)
    let rest := schedule.drop (t + 1)
    let cf := run sourceSelectMachine (sourceSelectClock (B - t) preBlocks)
      (init sourceSelectMachine (sourceSelectorInput B t schedule))
    cf.st = SourceSelectState.done ∧
      cf.tp.drop cf.hd = encodeD bits ++
        flattenPairs (rest.flatMap freshSourceBlock) := by
  dsimp only
  let schedule := literalTapeSchedule x w
  let bits := literalLookupTape w (scheduledLiteral x t)
  let preBlocks := schedule.take t
  let rest := schedule.drop (t + 1)
  have hget : schedule.getD t [] = bits := by
    dsimp only [schedule, bits]
    exact literalTapeSchedule_getD x w ht
  have hslen : schedule.length = (decodedLiterals x).length := by
    simp [schedule, literalTapeSchedule]
  have hts : t < schedule.length := by simpa [hslen] using ht
  have hbit : schedule[t] = bits := by
    rw [← hget, List.getD_eq_getElem schedule [] hts]
  have hsplit : schedule = preBlocks ++ bits :: rest := by
    dsimp only [preBlocks, rest]
    conv_lhs => rw [← List.take_append_drop t schedule]
    rw [List.drop_eq_getElem_cons hts, hbit]
  have hprefix : preBlocks.length = t := by
    dsimp only [preBlocks]
    rw [List.length_take, Nat.min_eq_left hts.le]
  have hinput : sourceSelectorInput (decodedLiterals x).length t schedule =
      flattenPairs (progressPairs ((decodedLiterals x).length - t)
        [] preBlocks (bits :: rest)) := by
    rw [sourceSelectorInput, progressPairs, sourceArchive, hsplit]
    simp [hprefix, List.append_assoc]
  rw [hinput]
  constructor
  · rw [sourceSelect_run]
  · exact sourceSelect_selected_suffix
      ((decodedLiterals x).length - t) preBlocks bits rest

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect.sourceSelect_cycle
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect.sourceSelect_rounds
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect.sourceSelect_run
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect.sourceSelect_selected_suffix
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect.sourceSelect_scheduled
