import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupLayoutBridge
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitSeq

/-!
# Charged local lookup: stage the next literal payload

After a routed lookup, the output capacity and marked schedule counter are
already in their next-round form, but the lookup suffix is the work tape left
by `masterM`.  This file supplies the missing finite-control rewrite pass.

`stageMachine P bits` crosses exactly `P` protected cells and writes the
finite block `bits` in place.  It never inspects the protected prefix, so the
live doubled output and countdown are preserved byte-for-byte.  The scheduled
specialization overwrites the old lookup work suffix with the canonical tape
for literal `t+1`; any old cells after the new `REND` marker are harmless,
because `RoundInv` deliberately leaves the region past `REND` unconstrained.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupNextStage

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinMaster
open PallLean.Paper93.DeepMath.PathB.CookLevinRoundInvariant
open PallLean.Paper93.DeepMath.PathB.CookLevinInP
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSplice (cntT)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSeq
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLiteralWeld
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupScheduleBound
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRepeatController
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupOutputCapacity
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLayoutBridge
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupReturnBit
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupDynamicRoute
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixRun

/-! ## A length-directed protected-prefix block writer -/

/-- Tape obtained after writing the first `k` bits of `bits` at offset `P`. -/
def stagedTape (P : Nat) (bits : List Bool) : Nat → List Bool → List Bool
  | 0, T => T
  | k + 1, T => writeAt (stagedTape P bits k T) (P + k) (bits.getD k false)

/-- Cross `P` cells, write `bits`, and halt.  The state value is the absolute
number of cells already crossed/written. -/
def stageMachine (P : Nat) (bits : List Bool) : Machine where
  State := Fin (P + bits.length + 1)
  fin := inferInstance
  dec := inferInstance
  start := ⟨0, by omega⟩
  halt := fun s => decide (s.val = P + bits.length)
  δ := fun s _ =>
    if hs : s.val < P + bits.length then
      let s' : Fin (P + bits.length + 1) := ⟨s.val + 1, by omega⟩
      if s.val < P then (s', none, 1)
      else (s', some (bits.getD (s.val - P) false), 1)
    else (s, none, 2)
  accept := fun _ => false

def stageFinalState (P : Nat) (bits : List Bool) : (stageMachine P bits).State :=
  ⟨P + bits.length, by omega⟩

@[simp] theorem stageFinalState_val (P : Nat) (bits : List Bool) :
    (stageFinalState P bits).val = P + bits.length := rfl

theorem stageMachine_run_scan (P : Nat) (bits T : List Bool) (i : Nat)
    (hi : i ≤ P) :
    run (stageMachine P bits) i (init (stageMachine P bits) T) =
      ⟨⟨i, by omega⟩, i, T⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      have hiP : i < P := by omega
      have hit : i < P + bits.length := by omega
      have hne : i ≠ P + bits.length := by omega
      rw [run_succ, ih (by omega)]
      simp [step, stageMachine, moveHead, hiP, hit, hne]

theorem stageMachine_run_write (P : Nat) (bits T : List Bool) (k : Nat)
    (hk : k ≤ bits.length) :
    run (stageMachine P bits) k
        ⟨⟨P, by omega⟩, P, T⟩ =
      ⟨⟨P + k, by omega⟩, P + k, stagedTape P bits k T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hklt : k < bits.length := by omega
      have hkne : k ≠ bits.length := by omega
      rw [run_succ, ih (by omega)]
      simp [step, stageMachine, stagedTape, moveHead, hklt, hkne,
        Nat.add_assoc]

/-- Exact whole staging run. -/
theorem stageMachine_run (P : Nat) (bits T : List Bool) :
    run (stageMachine P bits) (P + bits.length)
        (init (stageMachine P bits) T) =
      ⟨stageFinalState P bits, P + bits.length,
        stagedTape P bits bits.length T⟩ := by
  rw [run_add, stageMachine_run_scan P bits T P (by omega),
    stageMachine_run_write P bits T bits.length (by omega)]
  rfl

theorem stageMachine_halted (P : Nat) (bits T : List Bool) :
    (stageMachine P bits).halt
      (run (stageMachine P bits) (P + bits.length)
        (init (stageMachine P bits) T)).st = true := by
  rw [stageMachine_run]
  simp [stageMachine]

theorem stageMachine_halt_final (P : Nat) (bits : List Bool) :
    (stageMachine P bits).halt (stageFinalState P bits) = true := by
  simp [stageMachine, stageFinalState]

/-! ## Structural correctness of the rewrite -/

theorem stagedTape_getD_before (P : Nat) (bits : List Bool) (k : Nat)
    (T : List Bool) {p : Nat} (hp : p < P) :
    (stagedTape P bits k T).getD p false = T.getD p false := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [stagedTape]
      rw [PallLean.Paper93.DeepMath.PathB.CookLevinShiftLoop.writeAt_getD_ne
        (by omega)]
      exact ih

theorem stagedTape_getD_written (P : Nat) (bits : List Bool) (T : List Bool) :
    ∀ {k i : Nat}, i < k → k ≤ bits.length →
      (stagedTape P bits k T).getD (P + i) false = bits.getD i false := by
  intro k
  induction k with
  | zero => intro i hi; omega
  | succ k ih =>
      intro i hi hk
      simp only [stagedTape]
      by_cases hEq : i = k
      · subst i
        exact PallLean.Paper93.DeepMath.PathB.CookLevinShiftLoop.writeAt_getD_self _ _ _
      · rw [PallLean.Paper93.DeepMath.PathB.CookLevinShiftLoop.writeAt_getD_ne
          (by omega)]
        exact ih (by omega) (by omega)

/-- The freshly written canonical literal prefix satisfies `RoundInv`; cells
after its `REND` marker may retain arbitrary work-tape garbage. -/
theorem stagedTape_literal_roundInv (pre old : List Bool) (w : List Bool)
    (l : Lit) :
    RoundInv
      ((stagedTape pre.length (literalLookupTape w l)
        (literalLookupTape w l).length (pre ++ old)).drop pre.length)
      l.1 (signedLookupAssignment w l.1 l.2).length := by
  let A := signedLookupAssignment w l.1 l.2
  let fresh := literalLookupTape w l
  change RoundInv
    ((stagedTape pre.length fresh fresh.length (pre ++ old)).drop pre.length)
    l.1 A.length
  have hfresh : RoundInv fresh l.1 A.length := by
    simpa [fresh, literalLookupTape, A] using encode_roundInv A l.1
  have hlen : fresh.length = 4 * l.1 + 8 := by
    simp [fresh, literalLookupTape, encode, signedLookupAssignment_length,
      PallLean.Paper93.DeepMath.PathB.CookLevinInP.double_length]
    ring
  have hAlen : A.length = l.1 + 1 := by
    dsimp only [A]
    exact signedLookupAssignment_length _ _ _
  have hread : ∀ p, p < fresh.length →
      ((stagedTape pre.length fresh fresh.length (pre ++ old)).drop pre.length).getD p false =
        fresh.getD p false := by
    intro p hp
    rw [List.getD_eq_getElem?_getD, List.getElem?_drop,
      List.getD_eq_getElem?_getD]
    exact stagedTape_getD_written pre.length fresh (pre ++ old) hp (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi1 hi2
    rw [hread (2 * i) ?_, hread (2 * i + 1) ?_]
    exact hfresh.ctr i hi1 hi2
    all_goals rw [hlen]; omega
  · rw [hread (2 * l.1 + 2) ?_]
    exact hfresh.seplo
    rw [hlen]; omega
  · rw [hread (2 * l.1 + 3) ?_]
    exact hfresh.sephi
    rw [hlen]; omega
  · intro j hj
    rw [hread (2 * l.1 + 4 + 2 * j) ?_,
      hread (2 * l.1 + 5 + 2 * j) ?_]
    exact hfresh.dat j hj
    all_goals rw [hlen]; omega
  · rw [hread (2 * l.1 + 4 + 2 * A.length) ?_]
    exact hfresh.rendlo
    rw [hlen, hAlen]; omega
  · rw [hread (2 * l.1 + 5 + 2 * A.length) ?_]
    exact hfresh.rendhi
    rw [hlen, hAlen]; omega
  · rw [hread 1 ?_]
    exact hfresh.lsent
    rw [hlen]; omega

/-! ## Scheduled next-round staging -/

/-- Fixed prefix after round `t`: evolved output capacity followed by the
already marked countdown. -/
def nextStagePrefix (x w : List Bool) (t : Nat) : List Bool :=
  outputCap (decodedLiterals x).length ((scheduledTruths x w).take (t + 1)) ++
    cntT (decodedLiterals x).length (t + 1)

/-- The finite-control stage selected for the next scheduled literal. -/
def scheduledNextStageMachine (x w : List Bool) (t : Nat) : Machine :=
  stageMachine (nextStagePrefix x w t).length
    (literalLookupTape w (scheduledLiteral x (t + 1)))

theorem scheduledNextStage_run (x w old : List Bool) {t : Nat}
    (_ht : t + 1 < (decodedLiterals x).length) :
    let pre := nextStagePrefix x w t
    let next := literalLookupTape w (scheduledLiteral x (t + 1))
    run (scheduledNextStageMachine x w t) (pre.length + next.length)
        (init (scheduledNextStageMachine x w t) (pre ++ old)) =
      ⟨stageFinalState pre.length next, pre.length + next.length,
        stagedTape pre.length next next.length (pre ++ old)⟩ ∧
      RoundInv
        ((stagedTape pre.length next next.length (pre ++ old)).drop pre.length)
        (scheduledLiteral x (t + 1)).1
        (signedLookupAssignment w (scheduledLiteral x (t + 1)).1
          (scheduledLiteral x (t + 1)).2).length := by
  dsimp only
  constructor
  · exact stageMachine_run _ _ _
  · exact stagedTape_literal_roundInv _ _ _ _

/-! ## Lookup, route, and next-stage composition -/

/-- One scheduled nonterminal round: compute the current literal, append its
truth bit, then rewrite the work suffix for literal `t+1`. -/
def scheduledRouteStageMachine (x w : List Bool) (t : Nat) : Machine :=
  let B := (decodedLiterals x).length
  let out := (scheduledTruths x w).take t
  let lookup := layoutLookupMachine B (t + 1) out
  seqMachine (acceptRouteMachine lookup) (scheduledNextStageMachine x w t)

/-- Exact clock of lookup, routing handoff, and next-payload staging. -/
def scheduledRouteStageClock (x w : List Bool) (t : Nat) : Nat :=
  let B := (decodedLiterals x).length
  let out := (scheduledTruths x w).take t
  let l := scheduledLiteral x t
  let pre := nextStagePrefix x w t
  let next := literalLookupTape w (scheduledLiteral x (t + 1))
  layoutLookupRouteClock B (t + 1) out w l + 1 +
    (pre.length + next.length)

/-- Exact physical composition.  The dynamically computed current truth bit
is routed first; the sequenced finite-control writer then stages the next
canonical lookup prefix on the same tape. -/
theorem scheduledRouteStage_run (x w : List Bool) {t : Nat}
    (ht : t + 1 < (decodedLiterals x).length) :
    let B := (decodedLiterals x).length
    let out := (scheduledTruths x w).take t
    let l := scheduledLiteral x t
    let cf := run masterM (literalLookupClock w l)
      (init masterM (literalLookupTape w l))
    let pre := nextStagePrefix x w t
    let next := literalLookupTape w (scheduledLiteral x (t + 1))
    run (scheduledRouteStageMachine x w t)
        (scheduledRouteStageClock x w t)
        (init (scheduledRouteStageMachine x w t)
          (lookupLayoutPrefix B (t + 1) out ++ literalLookupTape w l)) =
      ⟨Sum.inr (stageFinalState pre.length next),
        pre.length + next.length,
        stagedTape pre.length next next.length (pre ++ cf.tp)⟩ := by
  dsimp only
  let B := (decodedLiterals x).length
  let out := (scheduledTruths x w).take t
  let l := scheduledLiteral x t
  let lookup := layoutLookupMachine B (t + 1) out
  let cf := run masterM (literalLookupClock w l)
    (init masterM (literalLookupTape w l))
  let pre := nextStagePrefix x w t
  let next := literalLookupTape w (scheduledLiteral x (t + 1))
  have ht0 : t < B := by dsimp only [B]; omega
  have houtlen : out.length = t := by
    dsimp only [out]
    rw [List.length_take, scheduledTruths_length,
      Nat.min_eq_left (by omega)]
  have hout : out.length < B := by omega
  have hstage := stageMachine_run pre.length next (pre ++ cf.tp)
  by_cases hb : evalLit (fun k => w.getD k false) l = true
  · have hroute := layoutLookupRoute_true B (t + 1) out w l hout hb
    have hpre : pre = outputCap B (out ++ [true]) ++ cntT B (t + 1) := by
      dsimp only [pre, nextStagePrefix, B, out, l]
      rw [scheduledTruths_take_succ x w ht0, hb]
    have hroute' : run (acceptRouteMachine lookup)
        (layoutLookupRouteClock B (t + 1) out w l)
        (init (acceptRouteMachine lookup)
          (lookupLayoutPrefix B (t + 1) out ++ literalLookupTape w l)) =
        embedTrueRouter lookup
          ⟨(6, ⟨0, by omega⟩, false), 2 * out.length + 3,
            pre ++ cf.tp⟩ := by
      rw [hpre]
      simpa [B, out, l, lookup, cf, List.append_assoc] using hroute
    exact seq_run (acceptRouteMachine lookup) (stageMachine pre.length next)
      _ _ _ _ _ _ _ _ _ hroute' rfl hstage (stageMachine_halt_final _ _)
  · have hb0 : evalLit (fun k => w.getD k false) l = false := by
      simpa using hb
    have hroute := layoutLookupRoute_false B (t + 1) out w l hout hb0
    have hpre : pre = outputCap B (out ++ [false]) ++ cntT B (t + 1) := by
      dsimp only [pre, nextStagePrefix, B, out, l]
      rw [scheduledTruths_take_succ x w ht0, hb0]
    have hroute' : run (acceptRouteMachine lookup)
        (layoutLookupRouteClock B (t + 1) out w l)
        (init (acceptRouteMachine lookup)
          (lookupLayoutPrefix B (t + 1) out ++ literalLookupTape w l)) =
        embedFalseRouter lookup
          ⟨(6, ⟨0, by omega⟩, false), 2 * out.length + 3,
            pre ++ cf.tp⟩ := by
      rw [hpre]
      simpa [B, out, l, lookup, cf, List.append_assoc] using hroute
    exact seq_run (acceptRouteMachine lookup) (stageMachine pre.length next)
      _ _ _ _ _ _ _ _ _ hroute' rfl hstage (stageMachine_halt_final _ _)

/-- The composed round leaves a valid canonical next-lookup prefix behind the
evolved output/countdown layout. -/
theorem scheduledRouteStage_next_roundInv (x w : List Bool) {t : Nat}
    (ht : t + 1 < (decodedLiterals x).length) :
    let B := (decodedLiterals x).length
    let out := (scheduledTruths x w).take t
    let l := scheduledLiteral x t
    let pre := nextStagePrefix x w t
    RoundInv
      ((run (scheduledRouteStageMachine x w t)
        (scheduledRouteStageClock x w t)
        (init (scheduledRouteStageMachine x w t)
          (lookupLayoutPrefix B (t + 1) out ++ literalLookupTape w l))).tp.drop
            pre.length)
      (scheduledLiteral x (t + 1)).1
      (signedLookupAssignment w (scheduledLiteral x (t + 1)).1
        (scheduledLiteral x (t + 1)).2).length := by
  dsimp only
  rw [scheduledRouteStage_run x w ht]
  exact stagedTape_literal_roundInv _ _ _ _

/-- Staging is linear in the protected layout plus the next literal tape and
therefore quadratic in the instance length. -/
theorem scheduledNextStageClock_le (x w : List Bool) {t : Nat}
    (ht : t + 1 < (decodedLiterals x).length) :
    (nextStagePrefix x w t).length +
        (literalLookupTape w (scheduledLiteral x (t + 1))).length
      ≤ 12 * (x.length + 1) ^ 2 := by
  let B := (decodedLiterals x).length
  let out := (scheduledTruths x w).take (t + 1)
  let l := scheduledLiteral x (t + 1)
  have hB0 := decodedLiterals_length_le x
  have hB : B ≤ (x.length + 1) ^ 2 := by
    dsimp only [B]
    nlinarith [Nat.zero_le x.length]
  have houtlen : out.length = t + 1 := by
    dsimp only [out]
    rw [List.length_take, scheduledTruths_length,
      Nat.min_eq_left (by omega)]
  have hcap := outputCap_length B out (by omega)
  have hcnt := PallLean.Paper93.DeepMath.PathB.CookLevinEmitSplice.cntT_length
    B (t + 1) (by omega)
  have hlmem := scheduledLiteral_mem x ht
  have hlvar := decodedLiterals_var_le x hlmem
  have hlit : (literalLookupTape w l).length = 4 * l.1 + 8 := by
    simp [literalLookupTape, encode, signedLookupAssignment_length,
      PallLean.Paper93.DeepMath.PathB.CookLevinInP.double_length]
    ring
  dsimp only [nextStagePrefix, B, out, l] at hcap hcnt houtlen hlit ⊢
  rw [List.length_append, hcap, hcnt, hlit]
  nlinarith [Nat.one_le_pow 2 (x.length + 1) (by omega)]

/-- Lookup, dynamic routing, the sequential handoff, and next-literal staging
all fit in one quadratic round envelope. -/
theorem scheduledRouteStageClock_le (x w : List Bool) {t : Nat}
    (ht : t + 1 < (decodedLiterals x).length) :
    scheduledRouteStageClock x w t ≤ 231 * (x.length + 1) ^ 2 := by
  have ht0 : t < (decodedLiterals x).length := by omega
  have hr := scheduledLayoutLookupRouteClock_le x w ht0
  have hs := scheduledNextStageClock_le x w ht
  dsimp only [scheduledRouteStageClock]
  nlinarith [Nat.one_le_pow 2 (x.length + 1) (by omega)]

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupNextStage

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupNextStage.stageMachine_run
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupNextStage.stagedTape_literal_roundInv
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupNextStage.scheduledNextStage_run
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupNextStage.scheduledRouteStage_run
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupNextStage.scheduledRouteStage_next_roundInv
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupNextStage.scheduledNextStageClock_le
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupNextStage.scheduledRouteStageClock_le
