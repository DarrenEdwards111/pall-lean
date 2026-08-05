import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeSourceCompact
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupLayoutBridge

/-!
# Charged local lookup: fixed runtime source-to-lookup bridge

The fixed source compactor halts just beyond the selected raw canonical
payload.  This file supplies a fixed rewind transducer.  It skips the local
four-cell compaction trailer, skips the payload's final `10`, scans backwards
through pairs which are never `10`, and halts on the payload's initial `10`.
The resulting head is exactly the canonical lookup origin.

The rewind is composed with the fixed selector/compactor and then with
`masterM`.  The final transition table is independent of the input, witness,
schedule, capacity, and live round index, and exposes `masterM`'s actual
accept bit.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceLookup

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinMaster
open PallLean.Paper93.DeepMath.PathB.CookLevinRoundInvariant
open PallLean.Paper93.DeepMath.PathB.CookLevinWholeRun
open PallLean.Paper93.DeepMath.PathB.CookLevinInP
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLiteralWeld
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixAdapter
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixRun
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryTerminal
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryWholeRun
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupScheduleBound
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRepeatController
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeStage
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceCompact

/-! ## Fixed canonical rewind -/

inductive SourceRewindState
  | back0 | back1 | back2 | back3
  | scanHi (seenEnd : Bool)
  | scanLo (seenEnd hi : Bool)
  | done
  deriving Fintype, DecidableEq

open SourceRewindState

/-- Rewind from the compactor's fixed trailer to the canonical left sentinel. -/
def sourceRewindMachine : Machine where
  State := SourceRewindState
  fin := inferInstance
  dec := inferInstance
  start := back0
  halt
    | done => true
    | _ => false
  δ s b := match s with
    | back0 => (back1, none, 0)
    | back1 => (back2, none, 0)
    | back2 => (back3, none, 0)
    | back3 => (scanHi false, none, 0)
    | scanHi seen => (scanLo seen b, none, 0)
    | scanLo seen hi =>
        if b && !hi then
          if seen then (done, none, 2)
          else (scanHi true, none, 0)
        else (scanHi seen, none, 0)
    | done => (done, none, 2)
  accept := fun _ => false

private theorem getD_boundary (P R : List Bool) (b : Bool) :
    (P ++ b :: R).getD P.length false = b := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
    Nat.sub_self]
  rfl

def rewindRaw (mid : List (Bool × Bool)) : List Bool :=
  [true, false] ++ flattenPairs mid ++ [true, false]

def rewindTape (pre : List Bool) (mid : List (Bool × Bool))
    (tail : List Bool) : List Bool :=
  pre ++ rewindRaw mid ++ tail

def NoRendPair (ps : List (Bool × Bool)) : Prop :=
  ∀ p ∈ ps, ¬(p.1 && !p.2)

private theorem sourceRewind_step_back0 (p : Nat) (T : List Bool) :
    step sourceRewindMachine ⟨back0, p, T⟩ =
      ⟨back1, p - 1, T⟩ := by
  simp [step, sourceRewindMachine, moveHead]

private theorem sourceRewind_step_back1 (p : Nat) (T : List Bool) :
    step sourceRewindMachine ⟨back1, p, T⟩ =
      ⟨back2, p - 1, T⟩ := by
  simp [step, sourceRewindMachine, moveHead]

private theorem sourceRewind_step_back2 (p : Nat) (T : List Bool) :
    step sourceRewindMachine ⟨back2, p, T⟩ =
      ⟨back3, p - 1, T⟩ := by
  simp [step, sourceRewindMachine, moveHead]

private theorem sourceRewind_step_back3 (p : Nat) (T : List Bool) :
    step sourceRewindMachine ⟨back3, p, T⟩ =
      ⟨scanHi false, p - 1, T⟩ := by
  simp [step, sourceRewindMachine, moveHead]

theorem sourceRewind_boot (pre : List Bool) (mid : List (Bool × Bool))
    (tail : List Bool) :
    run sourceRewindMachine 4
        ⟨back0, pre.length + (rewindRaw mid).length + 3,
          rewindTape pre mid ([true, false, false, true] ++ tail)⟩ =
      ⟨scanHi false, pre.length + (rewindRaw mid).length - 1,
        rewindTape pre mid ([true, false, false, true] ++ tail)⟩ := by
  let p := pre.length + (rewindRaw mid).length + 3
  let T := rewindTape pre mid ([true, false, false, true] ++ tail)
  have h1 : run sourceRewindMachine 1 ⟨back0, p, T⟩ =
      ⟨back1, p - 1, T⟩ := by
    rw [run_succ, run_zero, sourceRewind_step_back0]
  have h2 : run sourceRewindMachine 1 ⟨back1, p - 1, T⟩ =
      ⟨back2, p - 2, T⟩ := by
    rw [run_succ, run_zero, sourceRewind_step_back1]
    congr 1 <;> omega
  have h3 : run sourceRewindMachine 1 ⟨back2, p - 2, T⟩ =
      ⟨back3, p - 3, T⟩ := by
    rw [run_succ, run_zero, sourceRewind_step_back2]
    congr 1 <;> omega
  have h4 : run sourceRewindMachine 1 ⟨back3, p - 3, T⟩ =
      ⟨scanHi false, p - 4, T⟩ := by
    rw [run_succ, run_zero, sourceRewind_step_back3]
    congr 1 <;> omega
  rw [show 4 = 1 + (1 + (1 + 1)) by omega, run_add, h1,
    run_add, h2, run_add, h3, h4]
  simp [p, T, rewindRaw, flattenPairs_length]

theorem sourceRewind_pair (P : List Bool) (lo hi : Bool)
    (R : List Bool) (seen : Bool) (hn : ¬(lo && !hi)) :
    run sourceRewindMachine 2
        ⟨scanHi seen, (P ++ [lo, hi]).length - 1,
          P ++ [lo, hi] ++ R⟩ =
      ⟨scanHi seen, P.length - 1, P ++ [lo, hi] ++ R⟩ := by
  let T := P ++ [lo, hi] ++ R
  have hhi : T.getD (P.length + 1) false = hi := by
    rw [show T = (P ++ [lo]) ++ hi :: R by simp [T, List.append_assoc]]
    simpa using getD_boundary (P ++ [lo]) R hi
  have hlo : T.getD P.length false = lo := by
    rw [show T = P ++ lo :: (hi :: R) by simp [T, List.append_assoc]]
    exact getD_boundary P (hi :: R) lo
  rw [show (P ++ [lo, hi]).length - 1 = P.length + 1 by simp,
    show 2 = 1 + 1 by omega, run_add]
  have h1 : run sourceRewindMachine 1
      ⟨scanHi seen, P.length + 1, T⟩ =
      ⟨scanLo seen hi, P.length, T⟩ := by
    rw [run_succ, run_zero]
    rw [List.getD_eq_getElem?_getD] at hhi
    simp [step, sourceRewindMachine, moveHead, hhi]
  rw [h1, run_succ, run_zero]
  rw [List.getD_eq_getElem?_getD] at hlo
  have hn' : (lo && !hi) = false := by simpa using hn
  simpa [T, step, sourceRewindMachine, moveHead, hlo, hn']

theorem sourceRewind_take_end (P R : List Bool) :
    run sourceRewindMachine 2
        ⟨scanHi false, (P ++ [true, false]).length - 1,
          P ++ [true, false] ++ R⟩ =
      ⟨scanHi true, P.length - 1, P ++ [true, false] ++ R⟩ := by
  let T := P ++ [true, false] ++ R
  have hhi : T.getD (P.length + 1) false = false := by
    rw [show T = (P ++ [true]) ++ false :: R by simp [T, List.append_assoc]]
    simpa using getD_boundary (P ++ [true]) R false
  have hlo : T.getD P.length false = true := by
    rw [show T = P ++ true :: (false :: R) by simp [T, List.append_assoc]]
    exact getD_boundary P (false :: R) true
  rw [show (P ++ [true, false]).length - 1 = P.length + 1 by simp,
    show 2 = 1 + 1 by omega, run_add]
  have h1 : run sourceRewindMachine 1
      ⟨scanHi false, P.length + 1, T⟩ =
      ⟨scanLo false false, P.length, T⟩ := by
    rw [run_succ, run_zero]
    rw [List.getD_eq_getElem?_getD] at hhi
    simp [step, sourceRewindMachine, moveHead, hhi]
  rw [h1, run_succ, run_zero]
  rw [List.getD_eq_getElem?_getD] at hlo
  simpa [T, step, sourceRewindMachine, moveHead, hlo]

theorem sourceRewind_finish (pre R : List Bool) :
    run sourceRewindMachine 2
        ⟨scanHi true, (pre ++ [true, false]).length - 1,
          pre ++ [true, false] ++ R⟩ =
      ⟨done, pre.length, pre ++ [true, false] ++ R⟩ := by
  let T := pre ++ [true, false] ++ R
  have hhi : T.getD (pre.length + 1) false = false := by
    rw [show T = (pre ++ [true]) ++ false :: R by simp [T, List.append_assoc]]
    simpa using getD_boundary (pre ++ [true]) R false
  have hlo : T.getD pre.length false = true := by
    rw [show T = pre ++ true :: (false :: R) by simp [T, List.append_assoc]]
    exact getD_boundary pre (false :: R) true
  rw [show (pre ++ [true, false]).length - 1 = pre.length + 1 by simp,
    show 2 = 1 + 1 by omega, run_add]
  have h1 : run sourceRewindMachine 1
      ⟨scanHi true, pre.length + 1, T⟩ =
      ⟨scanLo true false, pre.length, T⟩ := by
    rw [run_succ, run_zero]
    rw [List.getD_eq_getElem?_getD] at hhi
    simp [step, sourceRewindMachine, moveHead, hhi]
  rw [h1, run_succ, run_zero]
  rw [List.getD_eq_getElem?_getD] at hlo
  simpa [T, step, sourceRewindMachine, moveHead, hlo]

def sourceRewindPairsClock (ps : List (Bool × Bool)) : Nat :=
  2 * ps.length

theorem sourceRewind_pairs : ∀ (pre : List Bool)
    (revps : List (Bool × Bool)) (tail : List Bool),
    NoRendPair revps →
    run sourceRewindMachine (sourceRewindPairsClock revps)
        ⟨scanHi true,
          (pre ++ [true, false] ++ flattenPairs revps.reverse).length - 1,
          pre ++ [true, false] ++ flattenPairs revps.reverse ++ tail⟩ =
      ⟨scanHi true, (pre ++ [true, false]).length - 1,
        pre ++ [true, false] ++ flattenPairs revps.reverse ++ tail⟩
  | pre, [], tail, _ => by simp [sourceRewindPairsClock]
  | pre, (lo, hi) :: revps, tail, hvalid => by
      have hp : ¬(lo && !hi) := hvalid (lo, hi) (by simp)
      have hps : NoRendPair revps := by
        intro p hp'
        exact hvalid p (by simp [hp'])
      rw [sourceRewindPairsClock, List.length_cons,
        show 2 * (revps.length + 1) = 2 + 2 * revps.length by omega,
        run_add]
      have hshape : flattenPairs ((lo, hi) :: revps).reverse =
          flattenPairs revps.reverse ++ [lo, hi] := by
        simp [flattenPairs_append, flattenPairs]
      rw [hshape]
      let P := pre ++ [true, false] ++ flattenPairs revps.reverse
      have hpRun := sourceRewind_pair P lo hi tail true hp
      have hpRun' : run sourceRewindMachine 2
          ⟨scanHi true,
            (pre ++ [true, false] ++
              (flattenPairs revps.reverse ++ [lo, hi])).length - 1,
            pre ++ [true, false] ++
              (flattenPairs revps.reverse ++ [lo, hi]) ++ tail⟩ =
          ⟨scanHi true, P.length - 1, P ++ [lo, hi] ++ tail⟩ := by
        simpa [P, List.append_assoc] using hpRun
      rw [hpRun']
      have ih := sourceRewind_pairs pre revps (lo :: hi :: tail) hps
      simp only [sourceRewindPairsClock] at ih
      have ih' : run sourceRewindMachine (2 * revps.length)
          ⟨scanHi true, P.length - 1, P ++ [lo, hi] ++ tail⟩ =
          ⟨scanHi true, (pre ++ [true, false]).length - 1,
            pre ++ [true, false] ++
              (flattenPairs revps.reverse ++ [lo, hi]) ++ tail⟩ := by
        simpa [sourceRewindPairsClock, P, List.append_assoc] using ih
      exact ih'

def sourceRewindClock (mid : List (Bool × Bool)) : Nat :=
  8 + 2 * mid.length

/-- Complete rewind over `10 ++ mid ++ 10`, where `mid` contains no `10`. -/
theorem sourceRewind_run (pre : List Bool) (mid : List (Bool × Bool))
    (tail : List Bool) (hmid : NoRendPair mid) :
    run sourceRewindMachine (sourceRewindClock mid)
        ⟨back0, pre.length + (rewindRaw mid).length + 3,
          rewindTape pre mid ([true, false, false, true] ++ tail)⟩ =
      ⟨done, pre.length,
        rewindTape pre mid ([true, false, false, true] ++ tail)⟩ := by
  have hb := sourceRewind_boot pre mid tail
  let P := pre ++ [true, false] ++ flattenPairs mid
  let R := [true, false, false, true] ++ tail
  have he := sourceRewind_take_end P R
  have hs := sourceRewind_pairs pre mid.reverse
    ([true, false] ++ R) (by
      intro p hp
      exact hmid p (by simpa using hp))
  have hf := sourceRewind_finish pre
    (flattenPairs mid ++ [true, false] ++ R)
  rw [sourceRewindClock,
    show 8 + 2 * mid.length = 4 + (2 + (2 * mid.length + 2)) by omega,
    run_add, hb, run_add]
  have he' : run sourceRewindMachine 2
      ⟨scanHi false, pre.length + (rewindRaw mid).length - 1,
        rewindTape pre mid R⟩ =
      ⟨scanHi true, P.length - 1, rewindTape pre mid R⟩ := by
    simpa [P, R, rewindRaw, rewindTape, List.append_assoc] using he
  rw [he', run_add]
  have hs' : run sourceRewindMachine (2 * mid.length)
      ⟨scanHi true, P.length - 1, rewindTape pre mid R⟩ =
      ⟨scanHi true, (pre ++ [true, false]).length - 1,
        rewindTape pre mid R⟩ := by
    simpa [sourceRewindPairsClock, P, R, rewindRaw, rewindTape,
      List.append_assoc] using hs
  rw [hs']
  simpa [R, rewindRaw, rewindTape, List.append_assoc] using hf

/-! ## Canonical payload grammar -/

def literalMiddlePairs (w : List Bool) (l : Lit) : List (Bool × Bool) :=
  List.replicate l.1 (true, true) ++ [(false, true)] ++
    dataPairs (signedLookupAssignment w l.1 l.2)

private theorem flattenPairs_dataPairs_eq_double (xs : List Bool) :
    flattenPairs (dataPairs xs) = double xs := by
  unfold dataPairs
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [flattenPairs, double, ih]

private theorem flattenPairs_replicate_true (n : Nat) :
    flattenPairs (List.replicate n (true, true)) =
      List.replicate (2 * n) true := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change true :: true :: flattenPairs (List.replicate n (true, true)) =
        List.replicate (2 * (n + 1)) true
      rw [ih]
      rw [show 2 * (n + 1) = 2 + 2 * n by omega]
      rw [List.replicate_add]
      rfl

theorem literalLookupTape_rewind_shape (w : List Bool) (l : Lit) :
    literalLookupTape w l = rewindRaw (literalMiddlePairs w l) := by
  simp [literalLookupTape, encode, rewindRaw, literalMiddlePairs,
    flattenPairs_append, flattenPairs, flattenPairs_dataPairs_eq_double,
    flattenPairs_replicate_true, List.append_assoc]

theorem literalMiddlePairs_noRend (w : List Bool) (l : Lit) :
    NoRendPair (literalMiddlePairs w l) := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · rcases List.mem_append.mp hp with hp | hp
    · have hp0 : l.1 ≠ 0 ∧ p = (true, true) := by
        simpa only [List.mem_replicate] using hp
      have hp' : p = (true, true) := hp0.2
      subst p
      decide
    · have hp' : p = (false, true) := by simpa using hp
      subst p
      decide
  · simp only [dataPairs, List.mem_map] at hp
    rcases hp with ⟨b, _, rfl⟩
    cases b <;> decide

def canonicalRewindClock (w : List Bool) (l : Lit) : Nat :=
  sourceRewindClock (literalMiddlePairs w l)

theorem sourceRewind_literal (pre w : List Bool) (l : Lit)
    (tail : List Bool) :
    run sourceRewindMachine (canonicalRewindClock w l)
        ⟨back0, pre.length + (literalLookupTape w l).length + 3,
          pre ++ literalLookupTape w l ++
            [true, false, false, true] ++ tail⟩ =
      ⟨done, pre.length,
        pre ++ literalLookupTape w l ++
          [true, false, false, true] ++ tail⟩ := by
  rw [literalLookupTape_rewind_shape]
  simpa [canonicalRewindClock, rewindTape, List.append_assoc] using
    sourceRewind_run pre (literalMiddlePairs w l) tail
      (literalMiddlePairs_noRend w l)

/-! ## Translation-invariant canonical lookup -/

def shiftCfg (M : Machine) (pre : List Bool) (c : Cfg M) : Cfg M :=
  ⟨c.st, pre.length + c.hd, pre ++ c.tp⟩

theorem step_shiftCfg (M : Machine) (pre : List Bool) (c : Cfg M)
    (hreset : M.halt c.st = false →
      (M.δ c.st (c.tp.getD c.hd false)).2.2 ≠ 3)
    (hleft : M.halt c.st = false →
      (M.δ c.st (c.tp.getD c.hd false)).2.2 = 0 → 0 < c.hd) :
    step M (shiftCfg M pre c) = shiftCfg M pre (step M c) := by
  cases hh : M.halt c.st with
  | false =>
      have hread : (pre ++ c.tp).getD (pre.length + c.hd) false =
          c.tp.getD c.hd false := by
        rw [PallLean.Paper93.DeepMath.PathB.CookLevinInP.getD_append_ge
          (by omega)]
        simp
      have hmove := moveHead_add_of_no_reset pre.length c.hd
        (M.δ c.st (c.tp.getD c.hd false)).2.2
        (hreset hh) (hleft hh)
      simp only [step, shiftCfg, hh, Bool.false_eq_true, ↓reduceIte, hread]
      rw [hmove]
      cases hw : (M.δ c.st (c.tp.getD c.hd false)).2.1 with
      | none => simp
      | some bv =>
          simp only
          rw [writeAt_append_shift]
  | true => simp [step, shiftCfg, hh]

theorem run_shiftCfg (M : Machine) (pre : List Bool) (c : Cfg M)
    (n : Nat) (hsafe : PrefixSafeRun M c n) :
    run M n (shiftCfg M pre c) = shiftCfg M pre (run M n c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [run_succ, ih (prefixSafeRun_mono hsafe (by omega))]
      have hs := hsafe n (by omega)
      simpa only [run_succ] using
        step_shiftCfg M pre (run M n c) hs.noReset hs.leftInside

private theorem prefixSafeRun_of_leftSafe {M : Machine} {c : Cfg M}
    {n : Nat} (hleft : LeftSafeRun M c n)
    (hreset : ∀ s b, (M.δ s b).2.2 ≠ 3) :
    PrefixSafeRun M c n := by
  intro i hi
  exact ⟨fun _ => hreset _ _, hleft i hi⟩

theorem masterM_run_shifted (pre w : List Bool) (l : Lit)
    (tail : List Bool) :
    run masterM (literalLookupClock w l)
        (shiftCfg masterM pre
          (init masterM (literalLookupTape w l ++ tail))) =
      shiftCfg masterM pre
        (run masterM (literalLookupClock w l)
          (init masterM (literalLookupTape w l ++ tail))) := by
  let A := signedLookupAssignment w l.1 l.2
  have hv : l.1 ≤ A.length := by
    dsimp only [A]
    rw [signedLookupAssignment_length]
    omega
  have hinv : RoundInv (literalLookupTape w l ++ tail) l.1 A.length := by
    dsimp only [A]
    exact literalLookupTape_append_roundInv w l tail
  have hleft : LeftSafeRun masterM
      (init masterM (literalLookupTape w l ++ tail))
      (2 * (l.1 + 1) + 2 + 1 + (clockSum l.1 A.length + 7)) := by
    simpa only [master_forced_init] using
      fullRun_leftSafe (literalLookupTape w l ++ tail)
        l.1 A.length hv hinv
  have hsafe : PrefixSafeRun masterM
      (init masterM (literalLookupTape w l ++ tail))
      (2 * (l.1 + 1) + 2 + 1 + (clockSum l.1 A.length + 7)) :=
    prefixSafeRun_of_leftSafe hleft masterM_reset_free
  have hr := run_shiftCfg masterM pre
    (init masterM (literalLookupTape w l ++ tail))
    (2 * (l.1 + 1) + 2 + 1 + (clockSum l.1 A.length + 7)) hsafe
  simpa only [literalLookupClock, A] using hr

/-! ## Fixed selector, rewind, and lookup composition -/

def sourceSelectCompactRewindMachine : Machine :=
  headSeqMachine sourceSelectCompactMachine sourceRewindMachine

def sourceRuntimeLookupCore : Machine :=
  headSeqMachine sourceSelectCompactRewindMachine masterM

/-- Read the nested final `masterM` state of the fixed sequential core. -/
def sourceRuntimeLookupAccept (s : sourceRuntimeLookupCore.State) : Bool :=
  match s with
  | .inl _ => false
  | .inr sm => masterM.accept sm

def sourceRuntimeLookupClock (d : Nat) (preBlocks : List (List Bool))
    (w : List Bool) (l : Lit) : Nat :=
  sourceSelectCompactClock d preBlocks (literalLookupTape w l) + 1 +
    canonicalRewindClock w l + 1 + literalLookupClock w l

-- The exact generic composition theorem is stated on the selected archive
-- shape and is specialized below to the live schedule.

theorem sourceRuntimeLookup_scheduled (x w : List Bool) {t : Nat}
    (ht : t < (decodedLiterals x).length) :
    let B := (decodedLiterals x).length
    let schedule := literalTapeSchedule x w
    let preBlocks := schedule.take t
    let l := scheduledLiteral x t
    let bits := literalLookupTape w l
    let rest := schedule.drop (t + 1)
    let pre := selectedPrefix (B - t) preBlocks
    let cf := run sourceRuntimeLookupCore
      (sourceRuntimeLookupClock (B - t) preBlocks w l)
      (init sourceRuntimeLookupCore (sourceSelectorInput B t schedule))
    sourceRuntimeLookupCore.halt cf.st = true ∧
      sourceRuntimeLookupAccept cf.st =
        evalLit (fun k => w.getD k false) l ∧
      cf.tp.take pre.length = pre := by
  dsimp only
  let B := (decodedLiterals x).length
  let schedule := literalTapeSchedule x w
  let preBlocks := schedule.take t
  let l := scheduledLiteral x t
  let bits := literalLookupTape w l
  let rest := schedule.drop (t + 1)
  let pre := selectedPrefix (B - t) preBlocks
  have hcompact := sourceSelectCompact_run (B - t) preBlocks bits rest
  have hshape : sourceSelectorInput B t schedule =
      flattenPairs (progressPairs (B - t) [] preBlocks (bits :: rest)) := by
    have hget : schedule.getD t [] = bits := by
      dsimp only [schedule, bits, l]
      exact literalTapeSchedule_getD x w ht
    have hslen : schedule.length = B := by
      simp [schedule, B, literalTapeSchedule]
    have hts : t < schedule.length := by simpa [hslen] using ht
    have hbit : schedule[t] = bits := by
      rw [← hget, List.getD_eq_getElem schedule [] hts]
    have hsplit : schedule = preBlocks ++ bits :: rest := by
      dsimp only [preBlocks, rest]
      conv_lhs => rw [← List.take_append_drop t schedule]
      rw [List.drop_eq_getElem_cons hts, hbit]
    have hprelen : preBlocks.length = t := by
      dsimp only [preBlocks]
      rw [List.length_take, Nat.min_eq_left hts.le]
    rw [sourceSelectorInput, progressPairs, sourceArchive, hsplit]
    simp [hprelen, List.append_assoc]
  let trailer := [true, false, false, true] ++
    List.replicate bits.length true ++ selectedTail rest
  have hcompact' : run sourceSelectCompactMachine
      (sourceSelectCompactClock (B - t) preBlocks bits)
      (init sourceSelectCompactMachine (sourceSelectorInput B t schedule)) =
      ⟨Sum.inr SourceCompactState.done,
        pre.length + bits.length + 3,
        pre ++ bits ++ trailer⟩ := by
    rw [hshape]
    simpa [pre, trailer, List.append_assoc] using hcompact
  have hrew := sourceRewind_literal pre w l
    (List.replicate bits.length true ++ selectedTail rest)
  have hrew' : run sourceRewindMachine (canonicalRewindClock w l)
      ⟨sourceRewindMachine.start, pre.length + bits.length + 3,
        pre ++ bits ++ trailer⟩ =
      ⟨SourceRewindState.done, pre.length, pre ++ bits ++ trailer⟩ := by
    simpa [bits, l, trailer, List.append_assoc] using hrew
  have hfirst := headSeq_run sourceSelectCompactMachine sourceRewindMachine
    (sourceSelectorInput B t schedule)
    (pre ++ bits ++ trailer) (pre ++ bits ++ trailer)
    (sourceSelectCompactClock (B - t) preBlocks bits)
    (canonicalRewindClock w l)
    (pre.length + bits.length + 3) pre.length
    (Sum.inr SourceCompactState.done) SourceRewindState.done
    hcompact' rfl hrew' rfl
  let mcf := run masterM (literalLookupClock w l)
    (init masterM (bits ++ trailer))
  have hmaster : run masterM (literalLookupClock w l)
      ⟨masterM.start, pre.length, pre ++ bits ++ trailer⟩ =
      shiftCfg masterM pre mcf := by
    simpa [bits, mcf, List.append_assoc] using
      masterM_run_shifted pre w l trailer
  let A := signedLookupAssignment w l.1 l.2
  have hv : l.1 ≤ A.length := by
    dsimp only [A]
    rw [signedLookupAssignment_length]
    omega
  have hinv : RoundInv (bits ++ trailer) l.1 A.length := by
    dsimp only [bits, A]
    exact literalLookupTape_append_roundInv w l trailer
  have happ := readAv_promise (bits ++ trailer) l.1 A.length hv hinv
  have hmhalt : masterM.halt mcf.st = true := by
    simpa [mcf, literalLookupClock, A, bits] using happ.1
  have hidx : 2 * l.1 + 4 + 2 * l.1 < bits.length := by
    simp [bits, literalLookupTape, CookLevinInP.encode,
      signedLookupAssignment_length,
      PallLean.Paper93.DeepMath.PathB.CookLevinInP.double_length]
    omega
  have hpureInv : RoundInv bits l.1 A.length := by
    dsimp only [bits, A]
    simpa [literalLookupTape, A] using
      encode_roundInv (signedLookupAssignment w l.1 l.2) l.1
  have hpure := readAv_promise bits l.1 A.length hv hpureInv
  have hvalue : bits.getD (2 * l.1 + 4 + 2 * l.1) false =
      evalLit (fun k => w.getD k false) l := by
    have hm := (masterM_reads_literal w l).2
    rw [← hpure.2]
    simpa [decideOut, literalLookupClock, A, bits] using hm
  have hmacc : masterM.accept mcf.st =
      evalLit (fun k => w.getD k false) l := by
    have ha := happ.2
    rw [List.getD_append bits trailer false
      (2 * l.1 + 4 + 2 * l.1) hidx, hvalue] at ha
    simpa [decideOut, mcf, literalLookupClock, A, bits] using ha
  have hsecond := headSeq_run sourceSelectCompactRewindMachine masterM
    (sourceSelectorInput B t schedule)
    (pre ++ bits ++ trailer) (pre ++ mcf.tp)
    (sourceSelectCompactClock (B - t) preBlocks bits + 1 +
      canonicalRewindClock w l)
    (literalLookupClock w l)
    pre.length (pre.length + mcf.hd)
    (Sum.inr SourceRewindState.done) mcf.st
    hfirst rfl (by simpa [shiftCfg] using hmaster) hmhalt
  have hrun : run sourceRuntimeLookupCore
      (sourceRuntimeLookupClock (B - t) preBlocks w l)
      (init sourceRuntimeLookupCore (sourceSelectorInput B t schedule)) =
      ⟨Sum.inr mcf.st, pre.length + mcf.hd, pre ++ mcf.tp⟩ := by
    simpa [sourceRuntimeLookupClock, sourceRuntimeLookupCore, bits,
      Nat.add_assoc] using hsecond
  rw [hrun]
  refine ⟨?_, hmacc, ?_⟩
  · simpa [sourceRuntimeLookupCore,
      headSeqMachine] using hmhalt
  · change (pre ++ mcf.tp).take pre.length = pre
    simp

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceLookup

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceLookup.sourceRewind_literal
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceLookup.masterM_run_shifted
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceLookup.sourceRuntimeLookup_scheduled
