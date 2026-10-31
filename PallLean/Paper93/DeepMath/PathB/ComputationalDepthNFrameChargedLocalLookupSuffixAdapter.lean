import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRepeatController
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitRange

/-!
# Charged local lookup: prefix-safe suffix adapter

The runtime repeat controller owns a leading doubled countdown.  A lookup
body must therefore run on the suffix without reading or overwriting that
prefix.  This file supplies the missing local adapter mechanism.

`suffixAdapter M` first scans the self-delimiting doubled prefix to its `01`
boundary, steps onto the suffix, and then simulates `M`.  Its body-step theorem
shows that a local read, in-bounds write, and non-reset head move translate
exactly by the prefix length.  The concrete lookup machine `masterM` is proved
reset-free, so it meets the essential move-side condition.

This is the prefix-preservation core of the remaining verifier body.  Staging
the selected canonical lookup tape and copying the returned bit into the
output region remain separate finite-control passes.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixAdapter

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinMaster
open PallLean.Paper93.DeepMath.PathB.CookLevinInP (getD_append_ge)
open PallLean.Paper93.DeepMath.PathB.CookLevinScanRightSep
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSplice
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRange (writeAt_append_right)

/-! ## The finite prefix scanner and body wrapper -/

/-- Scan a doubled self-delimiting prefix, then execute `M` on its suffix. -/
def suffixAdapter (M : Machine) : Machine where
  State := scanRightSep.State ⊕ M.State
  fin := inferInstance
  dec := inferInstance
  start := Sum.inl scanRightSep.start
  halt := fun s => match s with
    | .inl _ => false
    | .inr sm => M.halt sm
  δ := fun s b => match s with
    | .inl ss =>
        if scanRightSep.halt ss then (Sum.inr M.start, none, 1)
        else
          let tr := scanRightSep.δ ss b
          (Sum.inl tr.1, tr.2.1, tr.2.2)
    | .inr sm =>
        let tr := M.δ sm b
        (Sum.inr tr.1, tr.2.1, tr.2.2)
  accept := fun s => match s with
    | .inl _ => false
    | .inr sm => M.accept sm

def embedScan (M : Machine) (c : Cfg scanRightSep) : Cfg (suffixAdapter M) :=
  ⟨Sum.inl c.st, c.hd, c.tp⟩

def embedSuffix (M : Machine) (pre : List Bool) (c : Cfg M) :
    Cfg (suffixAdapter M) :=
  ⟨Sum.inr c.st, pre.length + c.hd, pre ++ c.tp⟩

theorem suffixAdapter_step_scan (M : Machine) (c : Cfg scanRightSep)
    (hh : scanRightSep.halt c.st = false) :
    step (suffixAdapter M) (embedScan M c) =
      embedScan M (step scanRightSep c) := by
  simp only [step, suffixAdapter, embedScan, hh, Bool.false_eq_true, ↓reduceIte]

theorem suffixAdapter_step_switch (M : Machine) (c : Cfg scanRightSep)
    (hh : scanRightSep.halt c.st = true) :
    step (suffixAdapter M) (embedScan M c) =
      ⟨Sum.inr M.start, c.hd + 1, c.tp⟩ := by
  simp only [step, suffixAdapter, embedScan, hh, Bool.false_eq_true,
    ↓reduceIte, moveHead]
  rfl

/-! ## Exact scan to the runtime countdown boundary -/

theorem suffixAdapter_run_two (M : Machine) {s : Bool} {p : Nat}
    {tape : List Bool}
    (h : (!(tape.getD p false) && tape.getD (p + 1) false) = false) :
    run (suffixAdapter M) 2 ⟨Sum.inl (0, s), p, tape⟩ =
      ⟨Sum.inl (0, tape.getD p false), p + 2, tape⟩ := by
  rw [show (⟨Sum.inl (0, s), p, tape⟩ : Cfg (suffixAdapter M)) =
      embedScan M ⟨(0, s), p, tape⟩ from rfl,
    run_succ, run_succ, run_zero,
    suffixAdapter_step_scan M _ (by rfl), step_readlo,
    suffixAdapter_step_scan M _ (by rfl), step_readhi_cont h]
  rfl

theorem suffixAdapter_run_pairs (M : Machine) (tape : List Bool)
    (P : Nat) (s : Bool) (m : Nat)
    (hns : ∀ i < m,
      (!(tape.getD (P + 2 * i) false) &&
        tape.getD (P + 2 * i + 1) false) = false) :
    run (suffixAdapter M) (2 * m) ⟨Sum.inl (0, s), P, tape⟩ =
      ⟨Sum.inl (0, storedR tape P s m), P + 2 * m, tape⟩ := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [show 2 * (m + 1) = 2 * m + 2 from by ring, run_add,
        ih (fun i hi => hns i (by omega)),
        suffixAdapter_run_two M (hns m (by omega))]
      simp only [storedR, Nat.add_assoc]

theorem suffixAdapter_scan_enter (M : Machine) (tape : List Bool)
    (P : Nat) (s : Bool) (m : Nat)
    (hns : ∀ i < m,
      (!(tape.getD (P + 2 * i) false) &&
        tape.getD (P + 2 * i + 1) false) = false)
    (hsep : (!(tape.getD (P + 2 * m) false) &&
      tape.getD (P + 2 * m + 1) false) = true) :
    run (suffixAdapter M) (2 * m + 3)
        ⟨Sum.inl (0, s), P, tape⟩ =
      ⟨Sum.inr M.start, P + 2 * m + 2, tape⟩ := by
  let c0 : Cfg scanRightSep :=
    ⟨(0, storedR tape P s m), P + 2 * m, tape⟩
  let c1 : Cfg scanRightSep :=
    ⟨(1, tape.getD (P + 2 * m) false), P + 2 * m + 1, tape⟩
  let c2 : Cfg scanRightSep :=
    ⟨(2, tape.getD (P + 2 * m) false), P + 2 * m + 1, tape⟩
  have e1 : step (suffixAdapter M) (embedScan M c0) = embedScan M c1 := by
    rw [suffixAdapter_step_scan M c0 (by rfl)]
    exact congrArg (embedScan M) step_readlo
  have e2 : step (suffixAdapter M) (embedScan M c1) = embedScan M c2 := by
    rw [suffixAdapter_step_scan M c1 (by rfl)]
    exact congrArg (embedScan M) (step_readhi_halt hsep)
  have e3 : step (suffixAdapter M) (embedScan M c2) =
      ⟨Sum.inr M.start, P + 2 * m + 2, tape⟩ := by
    rw [suffixAdapter_step_switch M c2 (by rfl)]
  rw [show 2 * m + 3 = 2 * m + 3 from rfl, run_add,
    suffixAdapter_run_pairs M tape P s m hns]
  change run (suffixAdapter M) 3 (embedScan M c0) = _
  rw [show 3 = 2 + 1 from rfl, run_succ,
    show 2 = 1 + 1 from rfl, run_succ, run_succ, run_zero,
    e1, e2, e3]

theorem suffixAdapter_enter_cntT (M : Machine) (B j : Nat)
    (hj : j ≤ B) (tail : List Bool) :
    run (suffixAdapter M) (2 * B + 3)
        (init (suffixAdapter M) (cntT B j ++ tail)) =
      ⟨Sum.inr M.start, (cntT B j).length, cntT B j ++ tail⟩ := by
  have hns : ∀ i < B,
      (!((cntT B j ++ tail).getD (2 * i) false) &&
        (cntT B j ++ tail).getD (2 * i + 1) false) = false := by
    intro i hi
    by_cases hij : i < j
    · rw [cntE_mark_lo B j tail i hij, cntE_mark_hi B j tail i hij]
      decide
    · rw [cntE_data B j tail (2 * i) hj (by omega) (by omega)]
      simp
  have hsep : (!((cntT B j ++ tail).getD (2 * B) false) &&
      (cntT B j ++ tail).getD (2 * B + 1) false) = true := by
    rw [cntE_cm_lo B j tail hj, cntE_cm_hi B j tail hj]
    decide
  have h := suffixAdapter_scan_enter M (cntT B j ++ tail) 0 false B
    (by simpa using hns) (by simpa using hsep)
  simp only [init, Nat.zero_add] at h ⊢
  rw [cntT_length B j hj]
  exact h

/-! ## Prefix-preserving body simulation -/

theorem moveHead_add_of_no_reset (q h : Nat) (m : Move)
    (hreset : m ≠ 3) (hleft : m = 0 → 0 < h) :
    moveHead (q + h) m = q + moveHead h m := by
  fin_cases m <;> simp_all [moveHead] <;> omega

/-- `writeAt` commutes with shifting an arbitrary tape behind one cell. -/
theorem writeAt_cons_succ (a : Bool) (t : List Bool) (p : Nat) (w : Bool) :
    writeAt (a :: t) (p + 1) w = a :: writeAt t p w := by
  unfold writeAt
  simp only [List.length_cons]
  rw [show p + 1 + 1 - (t.length + 1) = p + 1 - t.length by omega]
  simp

/-- `writeAt` commutes with shifting behind any protected prefix, including
when the write extends the body tape with padding. -/
theorem writeAt_append_shift (pre t : List Bool) (p : Nat) (w : Bool) :
    writeAt (pre ++ t) (pre.length + p) w = pre ++ writeAt t p w := by
  induction pre with
  | nil => simp
  | cons a pre ih =>
      simp only [List.cons_append, List.length_cons]
      rw [show pre.length + 1 + p = (pre.length + p) + 1 by omega,
        writeAt_cons_succ, ih]

private theorem suffixAdapter_step_body_running (M : Machine) (pre : List Bool)
    (c : Cfg M)
    (hhalt : M.halt c.st = false)
    (hreset : (M.δ c.st (c.tp.getD c.hd false)).2.2 ≠ 3)
    (hleft : (M.δ c.st (c.tp.getD c.hd false)).2.2 = 0 → 0 < c.hd) :
    step (suffixAdapter M) (embedSuffix M pre c) =
      embedSuffix M pre (step M c) := by
  have hread : (pre ++ c.tp).getD (pre.length + c.hd) false =
      c.tp.getD c.hd false := by
    rw [getD_append_ge (by omega)]
    simp
  have hmove := moveHead_add_of_no_reset pre.length c.hd
    (M.δ c.st (c.tp.getD c.hd false)).2.2 hreset hleft
  simp only [step, suffixAdapter, embedSuffix, hhalt, Bool.false_eq_true,
    ↓reduceIte, hread]
  rw [hmove]
  cases hw : (M.δ c.st (c.tp.getD c.hd false)).2.1 with
  | none => simp
  | some w =>
      simp only
      rw [writeAt_append_shift]

/-- One body step commutes with suffix embedding.  Halted configurations need
no side conditions because both machines freeze.  On a live step, only a
reset-free move and protection against crossing left through relative head
zero are required; arbitrary writes commute with suffix shifting. -/
theorem suffixAdapter_step_body (M : Machine) (pre : List Bool)
    (c : Cfg M)
    (hreset : M.halt c.st = false →
      (M.δ c.st (c.tp.getD c.hd false)).2.2 ≠ 3)
    (hleft : M.halt c.st = false →
      (M.δ c.st (c.tp.getD c.hd false)).2.2 = 0 → 0 < c.hd) :
    step (suffixAdapter M) (embedSuffix M pre c) =
      embedSuffix M pre (step M c) := by
  cases hh : M.halt c.st with
  | false =>
      exact suffixAdapter_step_body_running M pre c hh (hreset hh) (hleft hh)
  | true =>
      simp [step, suffixAdapter, embedSuffix, hh]

/-! ## The concrete lookup body satisfies the reset discipline -/

@[simp] private theorem rendStep_reset_free (sp : Fin 9) (c0 c1 b : Bool) :
    (rendStep sp c0 c1 b).2.2 ≠ 3 := by
  simp [rendStep]
  split_ifs <;> simp

@[simp] private theorem scanLeftStep_reset_free (sp : Fin 9) (c0 b : Bool) :
    (scanLeftStep sp c0 b).2.2 ≠ 3 := by
  simp [scanLeftStep]
  split_ifs <;> simp

@[simp] private theorem scanRightStep_reset_free (sp : Fin 9) (c0 b : Bool) :
    (scanRightStep sp c0 b).2.2 ≠ 3 := by
  simp [scanRightStep]
  split_ifs <;> simp

@[simp] private theorem loopStep_reset_free (sp : Fin 9) (c0 b : Bool) :
    (loopStep sp c0 b).2.2 ≠ 3 := by
  simp [loopStep]
  split_ifs <;> simp

@[simp] private theorem readResStep_reset_free (sp : Fin 9) (c0 b : Bool) :
    (readResStep sp c0 b).2.2 ≠ 3 := by
  simp [readResStep]
  split_ifs <;> simp

theorem masterM_reset_free (s : masterM.State) (b : Bool) :
    (masterM.δ s b).2.2 ≠ 3 := by
  rcases s with ⟨g, sp, c0, c1⟩
  simp only [masterM]
  by_cases h0 : g = 0
  · simp only [h0, if_true]
    by_cases hs : sp = 2
    · simp [hs, seam]
    · simpa [hs, inGroup] using scanRightStep_reset_free sp c0 b
  · simp only [h0, if_false]
    by_cases h1 : g = 1
    · simp only [h1, if_true]
      by_cases hs : sp = 2
      · cases c0 <;> simp [hs, seam]
      · simpa [hs, inGroup] using loopStep_reset_free sp c0 b
    · simp only [h1, if_false]
      by_cases h2 : g = 2
      · simp only [h2, if_true]
        by_cases hs : sp = 0 <;> simp [hs, seam]
      · simp only [h2, if_false]
        by_cases h3 : g = 3
        · simp only [h3, if_true]
          by_cases hs : sp = 8
          · simp [hs, seam]
          · simpa [hs, inGroup] using rendStep_reset_free sp c0 c1 b
        · simp only [h3, if_false]
          by_cases h4 : g = 4
          · simp only [h4, if_true]
            by_cases hs : sp = 2
            · simp [hs, seam]
            · simpa [hs, inGroup] using scanLeftStep_reset_free sp c0 b
          · simp only [h4, if_false]
            by_cases h5 : g = 5
            · simp [h5, seam]
            · simp only [h5, if_false]
              by_cases h6 : g = 6
              · simp only [h6, if_true]
                by_cases hs : sp = 8
                · simp [hs, seam]
                · simpa [hs, inGroup] using rendStep_reset_free sp c0 c1 b
              · simp only [h6, if_false]
                by_cases h7 : g = 7
                · simp only [h7, if_true]
                  by_cases hs : sp = 2
                  · simp [hs, seam]
                  · simpa [hs, inGroup] using scanLeftStep_reset_free sp c0 b
                · simp only [h7, if_false]
                  by_cases h8 : g = 8
                  · simp only [h8, if_true]
                    by_cases hs : sp = 3
                    · simp [hs]
                    · simpa [hs, inGroup] using readResStep_reset_free sp c0 b
                  · simp [h8]

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixAdapter

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixAdapter.suffixAdapter_enter_cntT
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixAdapter.moveHead_add_of_no_reset
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixAdapter.writeAt_append_shift
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixAdapter.suffixAdapter_step_body
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixAdapter.masterM_reset_free
