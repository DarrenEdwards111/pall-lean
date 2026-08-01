import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMCSPPowerGapAwareCopyRounds

/-!
# MCSP verifier: restore after all gap-aware bridge-copy rounds

After every table pair has been copied, this file runs the real controller
through the fully marked find pass, enters restore control, returns to the
true outer home without enabling gap skipping, heals every source pair, and
crosses the restored table marker.  The exact handoff is the low cell of the
retained internal `00`, immediately before the physical power bridge.
-/

namespace PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopyRestore

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCompare
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCopy
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyLift
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalHomeMachine
open PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCopyLayout
open PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCopyRound
open PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopyMachine
open PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopySeek
open PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopyRound
open PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopyRounds
open LocalHomeState
open GapCopyState

/-- Restore descriptor with the physical two-cell internal gap retained. -/
def gappedBridgeResS (n a i : ℕ) (suffix : List Bool) : List Bool :=
  List.replicate (2 * i) true ++
    (markedD (a - i) ++
      ([false, true] ++ ([false, false] ++
        (powBridge n ++
          (List.replicate (2 * a) true ++ ([false, false] ++ suffix))))))

theorem gappedBridgeResS_zero (n a : ℕ) (suffix : List Bool) :
    gappedBridgeResS n a 0 suffix =
      gappedBridgeCpyS n a a a suffix := by
  simp [gappedBridgeResS, gappedBridgeCpyS, cpyT, List.append_assoc]

theorem gappedBridgeResS_length (n a i : ℕ) (suffix : List Bool)
    (hi : i ≤ a) :
    (gappedBridgeResS n a i suffix).length =
      4 * a + 4 * (2 ^ n) + 10 + suffix.length := by
  simp [gappedBridgeResS, markedD_length, powBridge_length]
  omega

theorem gappedBridgeResS_pair_lo (n a i : ℕ) (suffix : List Bool)
    (hi : i < a) :
    (gappedBridgeResS n a i suffix).getD (2 * i) false = true := by
  rw [gappedBridgeResS,
    getD_append_length' _ _ List.length_replicate false,
    show a - i = (a - i - 1) + 1 by omega]
  rfl

theorem gappedBridgeResS_pair_hi (n a i : ℕ) (suffix : List Bool)
    (hi : i < a) :
    (gappedBridgeResS n a i suffix).getD (2 * i + 1) false = false := by
  rw [gappedBridgeResS,
    getD_append_left_length' _ _ List.length_replicate,
    show a - i = (a - i - 1) + 1 by omega]
  rfl

theorem gappedBridgeResS_marker_lo (n a : ℕ) (suffix : List Bool) :
    (gappedBridgeResS n a a suffix).getD (2 * a) false = false := by
  rw [gappedBridgeResS, Nat.sub_self,
    getD_append_length' _ _ List.length_replicate false]
  rfl

theorem gappedBridgeResS_marker_hi (n a : ℕ) (suffix : List Bool) :
    (gappedBridgeResS n a a suffix).getD (2 * a + 1) false = true := by
  rw [gappedBridgeResS, Nat.sub_self,
    getD_append_left_length' _ _ List.length_replicate]
  rfl

theorem gappedBridgeResS_gap_lo (n a : ℕ) (suffix : List Bool) :
    (gappedBridgeResS n a a suffix).getD (2 * a + 2) false = false := by
  rw [gappedBridgeResS, Nat.sub_self,
    show 2 * a + 2 = (List.replicate (2 * a) true).length + 2 by simp,
    getD_append_left_length' _ _ rfl]
  rfl

theorem gappedBridgeResS_gap_hi (n a : ℕ) (suffix : List Bool) :
    (gappedBridgeResS n a a suffix).getD (2 * a + 3) false = false := by
  rw [gappedBridgeResS, Nat.sub_self,
    show 2 * a + 3 = (List.replicate (2 * a) true).length + 3 by simp,
    getD_append_left_length' _ _ rfl]
  rfl

theorem gappedBridgeResS_heal (n a i : ℕ) (suffix : List Bool)
    (hi : i < a) :
    writeAt (gappedBridgeResS n a i suffix) (2 * i + 1) true =
      gappedBridgeResS n a (i + 1) suffix := by
  rw [writeAt_of_lt true (by
      rw [gappedBridgeResS_length n a i suffix (by omega)]
      omega),
    gappedBridgeResS,
    set_append_left_length' _ _ List.length_replicate,
    show a - i = (a - i - 1) + 1 by omega]
  simp only [markedD, List.cons_append, List.nil_append,
    List.set_cons_succ, List.set_cons_zero]
  rw [cons_cons_append, ← List.append_assoc,
    show ([true, true] : List Bool) = List.replicate 2 true from rfl,
    ← List.replicate_add,
    show 2 * i + 2 = 2 * (i + 1) by ring,
    show a - i - 1 = a - (i + 1) by omega]
  rfl

/-- Two unchanged restore transitions heal one marked source pair inside the
gap-aware controller.  Restore control never enables the gap flag. -/
theorem run_two_gapHeal {crossed s : Bool} {p : ℕ} {T : List Bool}
    (hlo : T.getD p false = true)
    (hhi : T.getD (p + 1) false = false) :
    run gapCopyMachine 2 ⟨.copy (6, s) crossed, p, T⟩ =
      ⟨.copy (6, true) crossed, p + 2,
        writeAt T (p + 1) true⟩ := by
  rw [List.getD_eq_getElem?_getD] at hlo hhi
  rw [run_succ, run_succ, run_zero]
  simp [step, gapCopyMachine, copyMachine, moveHead, hlo, hhi]

theorem run_gapped_restore (pre suffix : List Bool)
    (n a i : ℕ) (hi : i ≤ a) (s : Bool) :
    let q := localOffset pre
    run gapCopyMachine (2 * i)
      ⟨.copy (6, s) false, q,
        localTape pre (gappedBridgeResS n a 0 suffix)⟩ =
      ⟨.copy (6, if i = 0 then s else true) false, q + 2 * i,
        localTape pre (gappedBridgeResS n a i suffix)⟩ := by
  intro q
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [show 2 * (i + 1) = 2 * i + 2 by omega,
        run_add, ih (by omega)]
      have h := run_two_gapHeal
        (s := if i = 0 then s else true) (crossed := false)
        (p := q + 2 * i)
        (T := localTape pre (gappedBridgeResS n a i suffix))
        (by rw [show q + 2 * i = localOffset pre + 2 * i by rfl,
            localTape_getD]
            exact gappedBridgeResS_pair_lo n a i suffix (by omega))
        (by rw [show q + 2 * i + 1 =
              localOffset pre + (2 * i + 1) by omega, localTape_getD]
            exact gappedBridgeResS_pair_hi n a i suffix (by omega))
      have hp : 2 * i + 1 < (gappedBridgeResS n a i suffix).length := by
        rw [gappedBridgeResS_length n a i suffix (by omega)]
        omega
      rw [show q + 2 * i + 1 =
          localOffset pre + (2 * i + 1) by omega,
        localTape_writeAt pre _ (2 * i + 1) true hp,
        gappedBridgeResS_heal n a i suffix (by omega)] at h
      simpa [Nat.succ_ne_zero] using h

theorem run_gapped_restore_all (pre suffix : List Bool)
    (n a : ℕ) (s : Bool) :
    let q := localOffset pre
    run gapCopyMachine (2 * a)
      ⟨.copy (6, s) false, q,
        localTape pre (gappedBridgeResS n a 0 suffix)⟩ =
      ⟨.copy (6, if a = 0 then s else true) false, q + 2 * a,
        localTape pre (gappedBridgeResS n a a suffix)⟩ := by
  intro q
  exact run_gapped_restore pre suffix n a a (le_refl a) s

/-- From the fully marked source marker, enter restore home control and return
to the true outer home in copy state `6`.  Since restore starts left of the
internal gap, its skip flag is deliberately false. -/
theorem run_gapped_toRestore (pre suffix : List Bool)
    (n a : ℕ) (s : Bool) :
    let q := localOffset pre
    run gapCopyMachine (2 * a + 8)
      ⟨.copy (0, s) false, q + 2 * a,
        localTape pre (gappedBridgeCpyS n a a a suffix)⟩ =
      ⟨.copy (6, false) false, q,
        localTape pre (gappedBridgeCpyS n a a a suffix)⟩ := by
  intro q
  let T := localTape pre (gappedBridgeCpyS n a a a suffix)
  have henter : run gapCopyMachine 2
      ⟨.copy (0, s) false, q + 2 * a, T⟩ =
      ⟨.home (6, false) false scanHi, q + 2 * a + 1, T⟩ := by
    have hlo : T.getD (q + 2 * a) false = false := by
      dsimp [T]
      rw [show q + 2 * a = localOffset pre + 2 * a by rfl,
        localTape_getD]
      rw [gappedBridgeCpyS, List.getD_append (h := by
        rw [cpyT_length a a 0 (le_refl a)]
        omega)]
      exact cpyT_getD_marker_lo a a 0 (le_refl a)
    have hhi : T.getD (q + 2 * a + 1) false = true := by
      dsimp [T]
      rw [show q + 2 * a + 1 = localOffset pre + (2 * a + 1) by omega,
        localTape_getD]
      exact gapped_getD_marker_hi n a a a suffix (le_refl a)
    rw [List.getD_eq_getElem?_getD] at hlo hhi
    rw [run_succ, run_succ, run_zero]
    simp [step, gapCopyMachine, copyMachine, moveHead, hlo, hhi]
  have hscan := run_gapHomePairs (6, false) false T pre.length (a + 1)
    (fun i hi => by
      have hp := gapped_left_active_pair n a a i suffix (le_refl a) hi
      rcases hp with hp | hp
      · left
        dsimp [T]
        rw [show pre.length + 2 + 2 * i =
          localOffset pre + 2 * i by simp [localOffset], localTape_getD]
        exact hp
      · right
        dsimp [T]
        rw [show pre.length + 2 + 2 * i + 1 =
          localOffset pre + (2 * i + 1) by simp [localOffset]; omega,
          localTape_getD]
        exact hp)
  have hhead : q + 2 * a + 1 =
      pre.length + 1 + 2 * (a + 1) := by
    simp [q, localOffset]
    ring
  have hscan' : run gapCopyMachine (2 * (a + 1))
      ⟨.home (6, false) false scanHi, q + 2 * a + 1, T⟩ =
      ⟨.home (6, false) false scanHi, pre.length + 1, T⟩ := by
    rw [hhead]
    exact hscan
  have hhome := run_trueHome_four
    (resume := (6, false)) (q := pre.length) (T := T)
    (by simp [T, localTape, homePrefix])
    (by simp [T, localTape, homePrefix])
  have hhome' : run gapCopyMachine 4
      ⟨.home (6, false) false scanHi, pre.length + 1, T⟩ =
      ⟨.copy (6, false) false, q, T⟩ := by
    simpa [q, localOffset] using hhome
  rw [show 2 * a + 8 = 2 + (2 * (a + 1) + 4) by omega,
    run_add, henter, run_add, hscan', hhome']

theorem run_two_gapCross67 {s : Bool} {p : ℕ} {T : List Bool}
    (hlo : T.getD p false = false)
    (hhi : T.getD (p + 1) false = true) :
    run gapCopyMachine 2 ⟨.copy (6, s) false, p, T⟩ =
      ⟨.copy (8, false) false, p + 2, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at hlo hhi
  rw [run_succ, run_succ, run_zero]
  simp [step, gapCopyMachine, copyMachine, moveHead, hlo, hhi]

def gappedRestoreHandoffClock (a : ℕ) : ℕ :=
  2 * a + (2 * a + 8) + 2 * a + 2

theorem gappedRestoreHandoffClock_eq (a : ℕ) :
    gappedRestoreHandoffClock a = 6 * a + 10 := by
  unfold gappedRestoreHandoffClock
  omega

/-- Complete source restoration ends at the low cell of the retained internal
gap.  The next physical phase must cross these two known cells before starting
the already verified bridge-aware finish scan. -/
theorem run_gapped_restore_handoff (pre suffix : List Bool)
    (n a : ℕ) (s : Bool) :
    let q := localOffset pre
    run gapCopyMachine (gappedRestoreHandoffClock a)
      ⟨.copy (0, s) false, q,
        localTape pre (gappedBridgeCpyS n a a a suffix)⟩ =
      ⟨.copy (8, false) false, q + 2 * a + 2,
        localTape pre (gappedBridgeResS n a a suffix)⟩ := by
  intro q
  rw [gappedRestoreHandoffClock,
    show 2 * a + (2 * a + 8) + 2 * a + 2 =
      2 * a + ((2 * a + 8) + (2 * a + 2)) by omega,
    run_add, run_gapped_find pre suffix n a a (le_refl a) s,
    run_add, run_gapped_toRestore pre suffix n a
      (if a = 0 then s else true),
    ← gappedBridgeResS_zero,
    run_add, run_gapped_restore_all pre suffix n a false,
    run_two_gapCross67
      (by rw [show q + 2 * a = localOffset pre + 2 * a by rfl,
          localTape_getD]
          exact gappedBridgeResS_marker_lo n a suffix)
      (by rw [show q + 2 * a + 1 =
            localOffset pre + (2 * a + 1) by omega, localTape_getD]
          exact gappedBridgeResS_marker_hi n a suffix)]

def gappedCopyToHandoffClock (n a : ℕ) : ℕ :=
  gappedAllRoundsClock n a + gappedRestoreHandoffClock a

theorem gappedCopyToHandoffClock_eq (n a : ℕ) :
    gappedCopyToHandoffClock n a =
      6 * a * a + 4 * bridgePairs n * a + 22 * a + 10 := by
  rw [gappedCopyToHandoffClock, gappedAllRoundsClock_eq,
    gappedRestoreHandoffClock_eq]
  ring

/-- One physical run from untouched table-copy scratch through every gapped
round and complete source restoration, ending exactly on the retained gap. -/
theorem run_gapped_copy_to_handoff (pre suffix : List Bool)
    (n a : ℕ) (s : Bool) :
    let q := localOffset pre
    run gapCopyMachine (gappedCopyToHandoffClock n a)
      ⟨.copy (0, s) false, q,
        localTape pre (gappedBridgeCpyS n a 0 0 suffix)⟩ =
      ⟨.copy (8, false) false, q + 2 * a + 2,
        localTape pre (gappedBridgeResS n a a suffix)⟩ := by
  intro q
  rw [gappedCopyToHandoffClock, run_add,
    run_gapped_allRounds pre suffix n a s,
    run_gapped_restore_handoff pre suffix n a
      (if a = 0 then s else false)]

end PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopyRestore

#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopyRestore.run_gapped_restore_all
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopyRestore.run_gapped_toRestore
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopyRestore.run_gapped_restore_handoff
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopyRestore.run_gapped_copy_to_handoff
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopyRestore.gappedCopyToHandoffClock_eq
