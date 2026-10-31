import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeArchiveLocator

/-!
# Fixed output-to-source boundary locator

After a nonterminal truth cashout, the physical tape starts with a doubled
truth stream, its unique `01` terminator, at least one unused `00` capacity
pair, and then the runtime source region whose first cell is `1`.  This file
uses that grammar to locate the source origin with one fixed finite controller.
No capacity, output length, input, or live round occurs in its state space.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeOutputSourceLocator

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSeq
open PallLean.Paper93.DeepMath.PathB.CookLevinMaster
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLiteralWeld
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupDynamicRoute
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupOutputCapacity
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRepeatController
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupScheduleBound
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixRun
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeStage
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceCompact
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceLookup
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRelativeOutput
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeTailPreservation

inductive OutputSourceLocatorState
  | outLo
  | outHi (lo : Bool)
  | padLo
  | padHi
  | done
  deriving DecidableEq, Fintype

open OutputSourceLocatorState

/-- Fixed parser for `encodeD out ++ 00^k ++ source`, with `k > 0` and a
leading `1` at the source origin. -/
def outputSourceLocatorMachine : Machine where
  State := OutputSourceLocatorState
  fin := inferInstance
  dec := inferInstance
  start := .outLo
  halt := fun s => decide (s = .done)
  δ := fun s b =>
    match s with
    | .outLo => (.outHi b, none, 1)
    | .outHi lo =>
        if lo = b then (.outLo, none, 1)
        else if !lo && b then (.padLo, none, 1)
        else (.done, none, 2)
    | .padLo =>
        if b then (.done, none, 2)
        else (.padHi, none, 1)
    | .padHi =>
        if b then (.done, none, 2)
        else (.padLo, none, 1)
    | .done => (.done, none, 2)
  accept := fun _ => false

theorem outputSource_run_dataPair (T : List Bool) (p : Nat)
    (h : T.getD p false = T.getD (p + 1) false) :
    run outputSourceLocatorMachine 2 ⟨outLo, p, T⟩ =
      ⟨outLo, p + 2, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [run_succ, step, outputSourceLocatorMachine, moveHead, h]

theorem outputSource_run_outputPairs (T : List Bool) (q k : Nat)
    (h : ∀ i, i < k →
      T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run outputSourceLocatorMachine (2 * k) ⟨outLo, q, T⟩ =
      ⟨outLo, q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hk := h k (by omega)
      rw [show 2 * (k + 1) = 2 * k + 2 by omega, run_add,
        ih (fun i hi => h i (by omega)),
        outputSource_run_dataPair T (q + 2 * k) (by
          simpa [Nat.add_assoc] using hk)]
      congr 1

theorem outputSource_run_terminator (T : List Bool) (p : Nat)
    (h0 : T.getD p false = false)
    (h1 : T.getD (p + 1) false = true) :
    run outputSourceLocatorMachine 2 ⟨outLo, p, T⟩ =
      ⟨padLo, p + 2, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h0 h1
  simp [run_succ, step, outputSourceLocatorMachine, moveHead, h0, h1]

theorem outputSource_run_zeroPair (T : List Bool) (p : Nat)
    (h0 : T.getD p false = false)
    (h1 : T.getD (p + 1) false = false) :
    run outputSourceLocatorMachine 2 ⟨padLo, p, T⟩ =
      ⟨padLo, p + 2, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h0 h1
  simp [run_succ, step, outputSourceLocatorMachine, moveHead, h0, h1]

theorem outputSource_run_zeroPairs (T : List Bool) (q k : Nat)
    (h : ∀ i, i < k →
      T.getD (q + 2 * i) false = false ∧
      T.getD (q + 2 * i + 1) false = false) :
    run outputSourceLocatorMachine (2 * k) ⟨padLo, q, T⟩ =
      ⟨padLo, q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hk := h k (by omega)
      rw [show 2 * (k + 1) = 2 * k + 2 by omega, run_add,
        ih (fun i hi => h i (by omega)),
        outputSource_run_zeroPair T (q + 2 * k) hk.1 (by
          simpa [Nat.add_assoc] using hk.2)]
      congr 1

theorem outputSource_run_sourceHead (T : List Bool) (p : Nat)
    (h : T.getD p false = true) :
    run outputSourceLocatorMachine 1 ⟨padLo, p, T⟩ =
      ⟨done, p, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [run_succ, step, outputSourceLocatorMachine, moveHead, h]

/-- Complete fixed traversal from output origin to source origin. -/
theorem outputSourceLocator_run (out source : List Bool) (k : Nat)
    (hk : 0 < k) (hsource : source.getD 0 false = true) :
    let pad := List.replicate (2 * k) false
    let T := encodeD out ++ pad ++ source
    run outputSourceLocatorMachine (2 * out.length + 2 + 2 * k + 1)
        (init outputSourceLocatorMachine T) =
      ⟨done, (encodeD out).length + 2 * k, T⟩ := by
  dsimp only
  let pad := List.replicate (2 * k) false
  let T := encodeD out ++ pad ++ source
  have hd : run outputSourceLocatorMachine (2 * out.length)
      (init outputSourceLocatorMachine T) =
      ⟨outLo, 2 * out.length, T⟩ := by
    simpa using outputSource_run_outputPairs T 0 out.length (fun i hi => by
    dsimp [T]
    rw [show encodeD out ++ pad ++ source =
      encodeD out ++ (pad ++ source) by simp [List.append_assoc]]
    rw [List.getD_append (h := by rw [encodeD_length]; omega),
      List.getD_append (h := by rw [encodeD_length]; omega)]
    simpa using encodeD_data_eq out i hi)
  have ht := outputSource_run_terminator T (2 * out.length)
    (by
      dsimp [T]
      rw [show encodeD out ++ pad ++ source =
        encodeD out ++ (pad ++ source) by simp [List.append_assoc]]
      rw [List.getD_append (h := by rw [encodeD_length]; omega)]
      exact encodeD_mark_lo out)
    (by
      dsimp [T]
      rw [show encodeD out ++ pad ++ source =
        encodeD out ++ (pad ++ source) by simp [List.append_assoc]]
      rw [List.getD_append (h := by rw [encodeD_length]; omega)]
      exact encodeD_mark_hi out)
  have hp : run outputSourceLocatorMachine (2 * k)
      ⟨padLo, 2 * out.length + 2, T⟩ =
      ⟨padLo, 2 * out.length + 2 + 2 * k, T⟩ := by
    apply outputSource_run_zeroPairs
    intro i hi
    constructor
    · dsimp [T, pad]
      rw [show encodeD out ++ List.replicate (2 * k) false ++ source =
        encodeD out ++ (List.replicate (2 * k) false ++ source) by
          simp [List.append_assoc]]
      rw [List.getD_append_right (h := by rw [encodeD_length]; omega)]
      rw [show 2 * out.length + 2 + 2 * i - (encodeD out).length =
          2 * i by rw [encodeD_length]; omega]
      rw [List.getD_append (h := by simp; omega)]
      simp
    · dsimp [T, pad]
      rw [show encodeD out ++ List.replicate (2 * k) false ++ source =
        encodeD out ++ (List.replicate (2 * k) false ++ source) by
          simp [List.append_assoc]]
      rw [List.getD_append_right (h := by rw [encodeD_length]; omega)]
      rw [show 2 * out.length + 2 + 2 * i + 1 - (encodeD out).length =
          2 * i + 1 by rw [encodeD_length]; omega]
      rw [List.getD_append (h := by simp; omega)]
      simp
  have hs : T.getD (2 * out.length + 2 + 2 * k) false = true := by
    dsimp [T, pad]
    rw [show encodeD out ++ List.replicate (2 * k) false ++ source =
      encodeD out ++ (List.replicate (2 * k) false ++ source) by
        simp [List.append_assoc]]
    rw [List.getD_append_right (h := by rw [encodeD_length]; omega)]
    rw [show 2 * out.length + 2 + 2 * k - (encodeD out).length =
        2 * k by rw [encodeD_length]; omega]
    rw [List.getD_append_right (h := by simp)]
    simpa using hsource
  change run outputSourceLocatorMachine (2 * out.length + 2 + 2 * k + 1)
      (init outputSourceLocatorMachine T) =
    ⟨done, (encodeD out).length + 2 * k, T⟩
  rw [show 2 * out.length + 2 + 2 * k + 1 =
      2 * out.length + (2 + (2 * k + 1)) by omega,
    run_add, hd, run_add, ht, run_add, hp,
    outputSource_run_sourceHead T (2 * out.length + 2 + 2 * k) hs]
  simp [encodeD_length]

def outputSourceLocatorClock (B : Nat) (out : List Bool) : Nat :=
  2 * out.length + 2 + 2 * (B - out.length) + 1

theorem flattenPairs_replicate_tt_head (n : Nat) (hn : 0 < n) :
    (flattenPairs (List.replicate n (true, true))).getD 0 false = true := by
  cases n with
  | zero => omega
  | succ n => rfl

theorem selectedPrefix_head_true (d : Nat) (preBlocks : List (List Bool))
    (hd : 0 < d) :
    (selectedPrefix d preBlocks).getD 0 false = true := by
  have hp : 0 < (selectedPrefixPairs d preBlocks).length := by
    simp [selectedPrefixPairs]
  rw [selectedPrefix, flattenPairs_getD_lo
    (selectedPrefixPairs d preBlocks) 0 hp]
  simp [selectedPrefixPairs, hd]

/-- The fixed locator starts at the physical origin of the genuine routed
tape and halts exactly at the runtime-source origin, without knowing `B`. -/
theorem scheduledRuntimeRelativeOutput_sourceOriginLocate
    (x w : List Bool) {t : Nat}
    (ht : t < (decodedLiterals x).length)
    (htnext : t + 1 < (decodedLiterals x).length) :
    let B := (decodedLiterals x).length
    let schedule := literalTapeSchedule x w
    let preBlocks := schedule.take t
    let l := scheduledLiteral x t
    let out := (scheduledTruths x w).take t
    let out' := (scheduledTruths x w).take (t + 1)
    let T := sourceSelectorInput B t schedule
    let n := sourceRuntimeLookupClock (B - t) preBlocks w l
    let M := runtimeRelativeOutputSourceMachine B
    let clock := runtimeRelativeOutputRouteClock B out T n
    let rcf := run (acceptRouteMachine M) clock
      (init (acceptRouteMachine M) (outputCap B out ++ T))
    run outputSourceLocatorMachine (outputSourceLocatorClock B out')
        (init outputSourceLocatorMachine rcf.tp) =
      ⟨done, 2 * B + 2, rcf.tp⟩ := by
  dsimp only
  let B := (decodedLiterals x).length
  let schedule := literalTapeSchedule x w
  let preBlocks := schedule.take t
  let l := scheduledLiteral x t
  let out := (scheduledTruths x w).take t
  let out' := (scheduledTruths x w).take (t + 1)
  let T := sourceSelectorInput B t schedule
  let n := sourceRuntimeLookupClock (B - t) preBlocks w l
  let cf := run sourceRuntimeLookupCore n (init sourceRuntimeLookupCore T)
  let M := runtimeRelativeOutputSourceMachine B
  let clock := runtimeRelativeOutputRouteClock B out T n
  let rcf := run (acceptRouteMachine M) clock
    (init (acceptRouteMachine M) (outputCap B out ++ T))
  have hout : out'.length = t + 1 := by
    dsimp [out']
    rw [List.length_take, scheduledTruths_length,
      Nat.min_eq_left (by simpa [B] using htnext.le)]
  have hk : 0 < B - out'.length := by
    rw [hout]
    simpa [B] using Nat.sub_pos_of_lt htnext
  have hroute := scheduledRuntimeRelativeOutputSourceRoute x w ht
  have htp : rcf.tp = outputCap B out' ++ cf.tp := by
    have hs := scheduledTruths_take_succ x w ht
    simpa [B, schedule, preBlocks, l, out, out', T, n, cf, M, clock, rcf,
      hs] using hroute.2
  let bits := literalLookupTape w l
  let rest := schedule.drop (t + 1)
  let pre := selectedPrefix (B - t) preBlocks
  let trailer := [true, false, false, true] ++
    List.replicate bits.length true ++ selectedTail rest
  let mcf := run masterM (literalLookupClock w l)
    (init masterM (bits ++ trailer))
  have hcf : cf.tp = pre ++ mcf.tp := by
    have hslen : schedule.length = B := by
      simp [schedule, B, literalTapeSchedule]
    have hts : t < schedule.length := by simpa [hslen] using ht
    have hget : schedule.getD t [] = bits := by
      dsimp [schedule, bits, l]
      exact literalTapeSchedule_getD x w ht
    have hbit : schedule[t] = bits := by
      rw [← hget, List.getD_eq_getElem schedule [] hts]
    have hsplit : schedule = preBlocks ++ bits :: rest := by
      dsimp [preBlocks, rest]
      conv_lhs => rw [← List.take_append_drop t schedule]
      rw [List.drop_eq_getElem_cons hts, hbit]
    have hprelen : preBlocks.length = t := by
      dsimp [preBlocks]
      rw [List.length_take, Nat.min_eq_left hts.le]
    have hshape : T =
        flattenPairs (progressPairs (B - t) [] preBlocks (bits :: rest)) := by
      dsimp [T]
      rw [sourceSelectorInput, progressPairs, sourceArchive, hsplit]
      simp [hprelen, List.append_assoc]
    have hr := sourceRuntimeLookup_run_shape (B - t) preBlocks w l rest
    dsimp [cf, n]
    rw [hshape]
    simpa [bits, pre, trailer, mcf] using congrArg Cfg.tp hr
  have hpre : 0 < pre.length := by
    have hp : pre.getD 0 false = true := by
      simpa [pre] using selectedPrefix_head_true (B - t) preBlocks (by omega)
    by_contra hz
    have : pre = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [this] at hp
    simp at hp
  have hsource : cf.tp.getD 0 false = true := by
    rw [hcf, List.getD_append (h := hpre)]
    exact selectedPrefix_head_true (B - t) preBlocks (by omega)
  have hr := outputSourceLocator_run out' cf.tp (B - out'.length) hk hsource
  rw [htp]
  change run outputSourceLocatorMachine (outputSourceLocatorClock B out')
      (init outputSourceLocatorMachine
        (outputCap B out' ++ cf.tp)) =
    ⟨done, 2 * B + 2, outputCap B out' ++ cf.tp⟩
  rw [outputCap]
  convert hr using 1 <;>
    simp [encodeD_length, hout] <;> omega

/-- Cashout and source-origin discovery are one operational sequential
machine; the handoff resets to physical origin and the fixed right phase
recovers the source boundary from tape grammar alone. -/
theorem scheduledRuntimeRelativeOutput_sourceOriginCombined
    (x w : List Bool) {t : Nat}
    (ht : t < (decodedLiterals x).length)
    (htnext : t + 1 < (decodedLiterals x).length) :
    let B := (decodedLiterals x).length
    let schedule := literalTapeSchedule x w
    let preBlocks := schedule.take t
    let l := scheduledLiteral x t
    let out := (scheduledTruths x w).take t
    let out' := (scheduledTruths x w).take (t + 1)
    let T := sourceSelectorInput B t schedule
    let n := sourceRuntimeLookupClock (B - t) preBlocks w l
    let M1 := acceptRouteMachine (runtimeRelativeOutputSourceMachine B)
    let clock1 := runtimeRelativeOutputRouteClock B out T n
    let rcf := run M1 clock1 (init M1 (outputCap B out ++ T))
    let clock2 := outputSourceLocatorClock B out'
    let M := seqMachine M1 outputSourceLocatorMachine
    run M (clock1 + 1 + clock2) (init M (outputCap B out ++ T)) =
      ⟨Sum.inr done, 2 * B + 2, rcf.tp⟩ := by
  dsimp only
  let B := (decodedLiterals x).length
  let schedule := literalTapeSchedule x w
  let preBlocks := schedule.take t
  let l := scheduledLiteral x t
  let out := (scheduledTruths x w).take t
  let out' := (scheduledTruths x w).take (t + 1)
  let T := sourceSelectorInput B t schedule
  let n := sourceRuntimeLookupClock (B - t) preBlocks w l
  let M1 := acceptRouteMachine (runtimeRelativeOutputSourceMachine B)
  let clock1 := runtimeRelativeOutputRouteClock B out T n
  let rcf := run M1 clock1 (init M1 (outputCap B out ++ T))
  let clock2 := outputSourceLocatorClock B out'
  have h1 : run M1 clock1 (init M1 (outputCap B out ++ T)) = rcf := rfl
  have hh1 : M1.halt rcf.st = true := by
    have hr := scheduledRuntimeRelativeOutputSourceRoute x w ht
    simpa [B, schedule, preBlocks, l, out, T, n, M1, clock1, rcf] using hr.1
  have h2 : run outputSourceLocatorMachine clock2
      (init outputSourceLocatorMachine rcf.tp) =
      ⟨done, 2 * B + 2, rcf.tp⟩ := by
    simpa [B, schedule, preBlocks, l, out, out', T, n, M1, clock1, rcf,
      clock2] using scheduledRuntimeRelativeOutput_sourceOriginLocate
        x w ht htnext
  exact seq_run M1 outputSourceLocatorMachine
    (outputCap B out ++ T) rcf.tp rcf.tp clock1 clock2 rcf.st rcf.hd
    done (2 * B + 2) h1 hh1 h2 rfl

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeOutputSourceLocator

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeOutputSourceLocator.outputSourceLocator_run
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeOutputSourceLocator.scheduledRuntimeRelativeOutput_sourceOriginLocate
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeOutputSourceLocator.scheduledRuntimeRelativeOutput_sourceOriginCombined
