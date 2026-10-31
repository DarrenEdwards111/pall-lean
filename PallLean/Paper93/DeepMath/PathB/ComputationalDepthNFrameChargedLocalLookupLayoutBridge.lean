import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupDynamicRoute
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupSuffixCanonical

/-!
# Charged local lookup: fixed-capacity layout bridge

The output router must start at tape position zero, while a literal lookup
must begin after both the fixed output capacity and the controller countdown.
`fixedPrefixAdapter P M` supplies that physical bridge: it skips exactly `P`
cells (ignoring any internal doubled-stream terminators), then simulates `M`
on the suffix while preserving the entire prefix.

Unlike the self-delimiting suffix adapter, this scanner is length-directed.
It can therefore cross the live output's `01` marker and all reserved blank
pairs.  The canonical specialization skips `outputCap B out ++ cntT B j`,
runs `masterM` on the literal payload, resets to the origin, and dynamically
routes the computed accepting bit back into the reserved output.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLayoutBridge

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinMaster
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSplice (cntT cntT_length)
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLiteralWeld
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixAdapter
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixRun
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryWholeRun
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupScheduleBound
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRepeatController
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixCanonical
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupOutputCapacity
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupOutputRouter
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupDynamicRoute

/-! ## Exact fixed-length prefix adapter -/

/-- Skip exactly `P` tape cells and then execute `M` on the suffix. -/
def fixedPrefixAdapter (P : Nat) (M : Machine) : Machine where
  State := Fin (P + 1) ⊕ M.State
  fin := inferInstance
  dec := inferInstance
  start := Sum.inl ⟨0, by omega⟩
  halt := fun s => match s with
    | .inl _ => false
    | .inr sm => M.halt sm
  δ := fun s b => match s with
    | .inl i =>
        if hi : i.val < P then
          (Sum.inl ⟨i.val + 1, by omega⟩, none, 1)
        else
          (Sum.inr M.start, none, 2)
    | .inr sm =>
        let tr := M.δ sm b
        (Sum.inr tr.1, tr.2.1, tr.2.2)
  accept := fun s => match s with
    | .inl _ => false
    | .inr sm => M.accept sm

def embedFixedBody (P : Nat) (M : Machine) (pre : List Bool) (c : Cfg M) :
    Cfg (fixedPrefixAdapter P M) :=
  ⟨Sum.inr c.st, pre.length + c.hd, pre ++ c.tp⟩

theorem fixedPrefix_step_scan (P : Nat) (M : Machine) (T : List Bool)
    (i : Nat) (hi : i < P) :
    step (fixedPrefixAdapter P M)
        ⟨Sum.inl ⟨i, by omega⟩, i, T⟩ =
      ⟨Sum.inl ⟨i + 1, by omega⟩, i + 1, T⟩ := by
  simp [step, fixedPrefixAdapter, hi, moveHead]

theorem fixedPrefix_step_switch (P : Nat) (M : Machine) (T : List Bool) :
    step (fixedPrefixAdapter P M)
        ⟨Sum.inl ⟨P, by omega⟩, P, T⟩ =
      ⟨Sum.inr M.start, P, T⟩ := by
  simp [step, fixedPrefixAdapter, moveHead]

theorem fixedPrefix_run_scan (P : Nat) (M : Machine) (T : List Bool)
    (i : Nat) (hi : i ≤ P) :
    run (fixedPrefixAdapter P M) i (init (fixedPrefixAdapter P M) T) =
      ⟨Sum.inl ⟨i, by omega⟩, i, T⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [run_succ, ih (by omega)]
      exact fixedPrefix_step_scan P M T i (by omega)

/-- After `P+1` steps, the adapter is at the body start on the suffix. -/
theorem fixedPrefix_enter (P : Nat) (M : Machine) (pre tail : List Bool)
    (hpre : pre.length = P) :
    run (fixedPrefixAdapter P M) (P + 1)
        (init (fixedPrefixAdapter P M) (pre ++ tail)) =
      embedFixedBody P M pre (init M tail) := by
  rw [run_succ, fixedPrefix_run_scan P M (pre ++ tail) P (by omega),
    fixedPrefix_step_switch]
  simp [embedFixedBody, init, hpre]

theorem fixedPrefix_step_body (P : Nat) (M : Machine)
    (pre : List Bool) (c : Cfg M)
    (hreset : M.halt c.st = false →
      (M.δ c.st (c.tp.getD c.hd false)).2.2 ≠ 3)
    (hleft : M.halt c.st = false →
      (M.δ c.st (c.tp.getD c.hd false)).2.2 = 0 → 0 < c.hd) :
    step (fixedPrefixAdapter P M) (embedFixedBody P M pre c) =
      embedFixedBody P M pre (step M c) := by
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
      simp only [step, fixedPrefixAdapter, embedFixedBody, hh,
        Bool.false_eq_true, ↓reduceIte, hread]
      rw [hmove]
      cases hw : (M.δ c.st (c.tp.getD c.hd false)).2.1 with
      | none => simp
      | some w =>
          simp only
          rw [writeAt_append_shift]
  | true =>
      simp [step, fixedPrefixAdapter, embedFixedBody, hh]

theorem fixedPrefix_run_body (P : Nat) (M : Machine)
    (pre : List Bool) (c : Cfg M) (n : Nat)
    (hsafe : PrefixSafeRun M c n) :
    run (fixedPrefixAdapter P M) n (embedFixedBody P M pre c) =
      embedFixedBody P M pre (run M n c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [run_succ, ih (prefixSafeRun_mono hsafe (by omega))]
      have hs := hsafe n (by omega)
      simpa only [run_succ] using
        fixedPrefix_step_body P M pre (run M n c)
          hs.noReset hs.leftInside

/-- Scan the fixed prefix and transport an entire safe body run. -/
theorem fixedPrefix_run (P : Nat) (M : Machine) (pre tail : List Bool)
    (n : Nat) (hpre : pre.length = P)
    (hsafe : PrefixSafeRun M (init M tail) n) :
    run (fixedPrefixAdapter P M) (P + 1 + n)
        (init (fixedPrefixAdapter P M) (pre ++ tail)) =
      embedFixedBody P M pre (run M n (init M tail)) := by
  rw [run_add, fixedPrefix_enter P M pre tail hpre]
  exact fixedPrefix_run_body P M pre (init M tail) n hsafe

/-! ## Canonical lookup behind output capacity and countdown -/

/-- The complete canonical lookup runs after an arbitrary fixed prefix and
preserves that prefix byte-for-byte. -/
theorem fixedPrefix_masterM_run (pre w : List Bool) (l : Lit) :
    run (fixedPrefixAdapter pre.length masterM)
        (pre.length + 1 + literalLookupClock w l)
        (init (fixedPrefixAdapter pre.length masterM)
          (pre ++ literalLookupTape w l)) =
      embedFixedBody pre.length masterM pre
        (run masterM (literalLookupClock w l)
          (init masterM (literalLookupTape w l))) := by
  exact fixedPrefix_run pre.length masterM pre (literalLookupTape w l)
    (literalLookupClock w l) rfl
    ((masterLiteralPrefixSafe_iff_leftSafe w l).2
      (masterLiteralLeftSafe w l))

/-- Physical prefix used by one verifier lookup round: fixed output capacity
first, then the controller countdown, then the canonical literal payload. -/
def lookupLayoutPrefix (B j : Nat) (out : List Bool) : List Bool :=
  outputCap B out ++ cntT B j

/-- Body machine for a round on the unified physical tape layout. -/
def layoutLookupMachine (B j : Nat) (out : List Bool) : Machine :=
  fixedPrefixAdapter (lookupLayoutPrefix B j out).length masterM

/-- Exact body clock before the dynamic router handoff. -/
def layoutLookupClock (B j : Nat) (out w : List Bool) (l : Lit) : Nat :=
  (lookupLayoutPrefix B j out).length + 1 + literalLookupClock w l

theorem layoutLookup_run (B j : Nat) (out w : List Bool) (l : Lit) :
    run (layoutLookupMachine B j out) (layoutLookupClock B j out w l)
        (init (layoutLookupMachine B j out)
          (lookupLayoutPrefix B j out ++ literalLookupTape w l)) =
      embedFixedBody (lookupLayoutPrefix B j out).length masterM
        (lookupLayoutPrefix B j out)
        (run masterM (literalLookupClock w l)
          (init masterM (literalLookupTape w l))) := by
  exact fixedPrefix_masterM_run (lookupLayoutPrefix B j out) w l

/-- Exact combined clock for lookup, dynamic branch selection, and routing. -/
def layoutLookupRouteClock (B j : Nat) (out w : List Bool) (l : Lit) : Nat :=
  layoutLookupClock B j out w l + 1 + outputRouteClock out

/-- When the computed literal is false, the unified machine crosses the fixed
layout, performs the lookup, resets to the origin, and consumes one reserved
output pair.  The countdown and evolved lookup tape are untouched by routing. -/
theorem layoutLookupRoute_false (B j : Nat) (out w : List Bool) (l : Lit)
    (hout : out.length < B)
    (hb : evalLit (fun k => w.getD k false) l = false) :
    let M := layoutLookupMachine B j out
    let cf := run masterM (literalLookupClock w l)
      (init masterM (literalLookupTape w l))
    run (acceptRouteMachine M) (layoutLookupRouteClock B j out w l)
        (init (acceptRouteMachine M)
          (lookupLayoutPrefix B j out ++ literalLookupTape w l)) =
      embedFalseRouter M
        ⟨(6, ⟨0, by omega⟩, false), 2 * out.length + 3,
          outputCap B (out ++ [false]) ++ (cntT B j ++ cf.tp)⟩ := by
  dsimp only
  let pre := lookupLayoutPrefix B j out
  let cf := run masterM (literalLookupClock w l)
    (init masterM (literalLookupTape w l))
  have hbody0 := layoutLookup_run B j out w l
  have hbody : run (layoutLookupMachine B j out)
      (layoutLookupClock B j out w l)
      (init (layoutLookupMachine B j out)
        (lookupLayoutPrefix B j out ++ literalLookupTape w l)) =
      ⟨Sum.inr cf.st, pre.length + cf.hd,
        outputCap B out ++ (cntT B j ++ cf.tp)⟩ := by
    rw [hbody0]
    simp [embedFixedBody, pre, cf, lookupLayoutPrefix, List.append_assoc]
  have hm := masterM_reads_literal w l
  have hhalt : masterM.halt cf.st = true := by
    exact hm.1
  have haccept : masterM.accept cf.st = false := by
    have heval : masterM.accept cf.st =
        evalLit (fun k => w.getD k false) l := by
      dsimp only [cf]
      change decideOut masterM (literalLookupTape w l)
        (literalLookupClock w l) = _
      simpa only [literalLookupClock] using hm.2
    rw [heval, hb]
  exact acceptRoute_output_false (layoutLookupMachine B j out)
    (lookupLayoutPrefix B j out ++ literalLookupTape w l)
    (layoutLookupClock B j out w l) B out (cntT B j ++ cf.tp)
    (Sum.inr cf.st) (pre.length + cf.hd) hbody hhalt haccept hout

/-- The accepting branch is identical operationally and appends `true`. -/
theorem layoutLookupRoute_true (B j : Nat) (out w : List Bool) (l : Lit)
    (hout : out.length < B)
    (hb : evalLit (fun k => w.getD k false) l = true) :
    let M := layoutLookupMachine B j out
    let cf := run masterM (literalLookupClock w l)
      (init masterM (literalLookupTape w l))
    run (acceptRouteMachine M) (layoutLookupRouteClock B j out w l)
        (init (acceptRouteMachine M)
          (lookupLayoutPrefix B j out ++ literalLookupTape w l)) =
      embedTrueRouter M
        ⟨(6, ⟨0, by omega⟩, false), 2 * out.length + 3,
          outputCap B (out ++ [true]) ++ (cntT B j ++ cf.tp)⟩ := by
  dsimp only
  let pre := lookupLayoutPrefix B j out
  let cf := run masterM (literalLookupClock w l)
    (init masterM (literalLookupTape w l))
  have hbody0 := layoutLookup_run B j out w l
  have hbody : run (layoutLookupMachine B j out)
      (layoutLookupClock B j out w l)
      (init (layoutLookupMachine B j out)
        (lookupLayoutPrefix B j out ++ literalLookupTape w l)) =
      ⟨Sum.inr cf.st, pre.length + cf.hd,
        outputCap B out ++ (cntT B j ++ cf.tp)⟩ := by
    rw [hbody0]
    simp [embedFixedBody, pre, cf, lookupLayoutPrefix, List.append_assoc]
  have hm := masterM_reads_literal w l
  have hhalt : masterM.halt cf.st = true := by
    exact hm.1
  have haccept : masterM.accept cf.st = true := by
    have heval : masterM.accept cf.st =
        evalLit (fun k => w.getD k false) l := by
      dsimp only [cf]
      change decideOut masterM (literalLookupTape w l)
        (literalLookupClock w l) = _
      simpa only [literalLookupClock] using hm.2
    rw [heval, hb]
  exact acceptRoute_output_true (layoutLookupMachine B j out)
    (lookupLayoutPrefix B j out ++ literalLookupTape w l)
    (layoutLookupClock B j out w l) B out (cntT B j ++ cf.tp)
    (Sum.inr cf.st) (pre.length + cf.hd) hbody hhalt haccept hout

/-- Branch-independent cashout: the machine halts and the output contains the
actual computed literal bit, while the countdown and evolved lookup suffix
remain byte-for-byte intact. -/
theorem layoutLookupRoute (B j : Nat) (out w : List Bool) (l : Lit)
    (hout : out.length < B) :
    let M := layoutLookupMachine B j out
    let cf := run masterM (literalLookupClock w l)
      (init masterM (literalLookupTape w l))
    let bv := evalLit (fun k => w.getD k false) l
    HaltsBy (acceptRouteMachine M)
        (lookupLayoutPrefix B j out ++ literalLookupTape w l)
        (layoutLookupRouteClock B j out w l) ∧
      (run (acceptRouteMachine M) (layoutLookupRouteClock B j out w l)
        (init (acceptRouteMachine M)
          (lookupLayoutPrefix B j out ++ literalLookupTape w l))).tp =
        outputCap B (out ++ [bv]) ++ (cntT B j ++ cf.tp) := by
  dsimp only
  by_cases hb : evalLit (fun k => w.getD k false) l = true
  · have h := layoutLookupRoute_true B j out w l hout hb
    constructor
    · change (acceptRouteMachine (layoutLookupMachine B j out)).halt
        (run (acceptRouteMachine (layoutLookupMachine B j out))
          (layoutLookupRouteClock B j out w l)
          (init (acceptRouteMachine (layoutLookupMachine B j out))
            (lookupLayoutPrefix B j out ++ literalLookupTape w l))).st = true
      rw [h]
      rfl
    · rw [h, hb]
      simp only [embedTrueRouter]
  · have hb0 : evalLit (fun k => w.getD k false) l = false := by
      simpa using hb
    have h := layoutLookupRoute_false B j out w l hout hb0
    constructor
    · change (acceptRouteMachine (layoutLookupMachine B j out)).halt
        (run (acceptRouteMachine (layoutLookupMachine B j out))
          (layoutLookupRouteClock B j out w l)
          (init (acceptRouteMachine (layoutLookupMachine B j out))
            (lookupLayoutPrefix B j out ++ literalLookupTape w l))).st = true
      rw [h]
      rfl
    · rw [h, hb0]
      simp only [embedFalseRouter]

/-! ## Scheduled round specialization -/

/-- At schedule index `t`, the unified machine appends exactly the next
semantic truth value to the fixed-capacity output and preserves the live
countdown plus the lookup's final work tape. -/
theorem scheduledLayoutLookupRoute (x w : List Bool) {t : Nat}
    (ht : t < (decodedLiterals x).length) :
    let B := (decodedLiterals x).length
    let out := (scheduledTruths x w).take t
    let l := scheduledLiteral x t
    let M := layoutLookupMachine B (t + 1) out
    let cf := run masterM (literalLookupClock w l)
      (init masterM (literalLookupTape w l))
    HaltsBy (acceptRouteMachine M)
        (lookupLayoutPrefix B (t + 1) out ++ literalLookupTape w l)
        (layoutLookupRouteClock B (t + 1) out w l) ∧
      (run (acceptRouteMachine M)
        (layoutLookupRouteClock B (t + 1) out w l)
        (init (acceptRouteMachine M)
          (lookupLayoutPrefix B (t + 1) out ++ literalLookupTape w l))).tp =
        outputCap B ((scheduledTruths x w).take (t + 1)) ++
          (cntT B (t + 1) ++ cf.tp) := by
  dsimp only
  have hlen : ((scheduledTruths x w).take t).length = t := by
    rw [List.length_take, scheduledTruths_length,
      Nat.min_eq_left (by omega)]
  have h := layoutLookupRoute (decodedLiterals x).length (t + 1)
    ((scheduledTruths x w).take t) w (scheduledLiteral x t)
    (by rw [hlen]; exact ht)
  simpa only [scheduledTruths_take_succ x w ht] using h

/-- The scan-inclusive unified round remains quadratic in the paired-input
length.  This bound includes both fixed regions, the canonical lookup,
dynamic branch selection, and output routing. -/
theorem scheduledLayoutLookupRouteClock_le (x w : List Bool) {t : Nat}
    (ht : t < (decodedLiterals x).length) :
    layoutLookupRouteClock (decodedLiterals x).length (t + 1)
      ((scheduledTruths x w).take t) w (scheduledLiteral x t) ≤
        218 * (x.length + 1) ^ 2 := by
  let B := (decodedLiterals x).length
  let out := (scheduledTruths x w).take t
  have hB : B ≤ (x.length + 1) ^ 2 := by
    dsimp only [B]
    have h0 := decodedLiterals_length_le x
    nlinarith [Nat.zero_le x.length]
  have houtlen : out.length = t := by
    dsimp only [out]
    rw [List.length_take, scheduledTruths_length,
      Nat.min_eq_left (by omega)]
  have houtle : out.length ≤ B := by omega
  have hcap := outputCap_length B out houtle
  have hcnt := cntT_length B (t + 1) (by omega)
  have hlit := lookupRoundClock_le x w ht
  dsimp only [B, out] at hB houtlen hcap hcnt ⊢
  rw [layoutLookupRouteClock, layoutLookupClock, lookupLayoutPrefix,
    List.length_append, hcap, hcnt, outputRouteClock, houtlen,
    literalLookupClock_eq_cost]
  simp only [lookupRoundClock] at hlit
  nlinarith [Nat.one_le_pow 2 (x.length + 1) (by omega)]

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLayoutBridge

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLayoutBridge.fixedPrefix_run
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLayoutBridge.fixedPrefix_masterM_run
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLayoutBridge.layoutLookupRoute_false
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLayoutBridge.layoutLookupRoute_true
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLayoutBridge.layoutLookupRoute
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLayoutBridge.scheduledLayoutLookupRoute
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLayoutBridge.scheduledLayoutLookupRouteClock_le
