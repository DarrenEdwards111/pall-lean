import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMCSPPowerGapAwareCopySeek
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitRange

/-!
# MCSP verifier: source mark and target grow on the gapped bridge tape

The gap-aware seek reaches the correct blank target.  This file proves the two
mutating pieces around it: marking the next table-source pair and growing the
copied table after the complete power bridge.  The four real grow transitions
enter gap-aware home control with `skipGap = true`, ready for the leftward
reset theorem.
-/

namespace PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopyGrow

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCompare
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCopy
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRange
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyLift
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalHomeMachine
open PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCopyLayout
open PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCopyRound
open PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopyMachine
open PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopySeek
open LocalHomeState
open GapCopyState

/-- Mark the next table-source pair without changing the internal gap, power
bridge, copied target, scratch, or payload. -/
theorem gappedBridgeCpyS_mark (n a j : ℕ) (suffix : List Bool)
    (hj : j < a) :
    writeAt (gappedBridgeCpyS n a j j suffix) (2 * j + 1) false =
      gappedBridgeCpyS n a (j + 1) j suffix := by
  rw [writeAt_of_lt false (by
      rw [gappedBridgeCpyS_length n a j j suffix (by omega) (by omega)]
      omega),
    gappedBridgeCpyS, cpyT,
    List.append_assoc,
    set_append_left_length' _ _ (markedD_length j),
    show 2 * (a - j) = 2 * (a - j - 1) + 1 + 1 by omega,
    List.replicate_succ, List.replicate_succ]
  simp only [List.cons_append, List.nil_append,
    List.set_cons_succ, List.set_cons_zero]
  rw [cons_cons_append, ← List.append_assoc, markedD_snoc,
    show a - j - 1 = a - (j + 1) by omega]
  rw [gappedBridgeCpyS, cpyT,
    show 2 * (a - (j + 1)) + 1 + 1 + 2 = 2 * (a - j) + 2 by omega]
  simp only [List.cons_append, List.nil_append, List.append_assoc]

/-- The two target writes append one copied `11` pair after the gap and both
power counters. -/
theorem gappedBridgeCpyS_grow (n a j : ℕ) (suffix : List Bool)
    (hj : j < a) :
    let p := 2 * a + 4 + (powBridge n).length + 2 * j
    writeAt (writeAt (gappedBridgeCpyS n a (j + 1) j suffix) p true)
      (p + 1) true = gappedBridgeCpyS n a (j + 1) (j + 1) suffix := by
  intro p
  let A := cpyT a (j + 1) 0 ++
    ([false, false] ++ (powBridge n ++ List.replicate (2 * j) true))
  let tail := List.replicate (2 * (a - (j + 1)) + 2) false ++ suffix
  have hlen : A.length = p := by
    simp [A, p, cpyT_length a (j + 1) 0 (by omega), powBridge_length]
    omega
  have hshape : gappedBridgeCpyS n a (j + 1) j suffix =
      A ++ false :: false :: tail := by
    simp only [gappedBridgeCpyS, A, tail]
    rw [show 2 * (a - j) + 2 =
      2 + (2 * (a - (j + 1)) + 2) by omega,
      List.replicate_add]
    simp [List.append_assoc]
  rw [hshape, ← hlen]
  rw [PallLean.Paper93.DeepMath.PathB.DIndexMachine.writeAt_boundary]
  rw [show A ++ true :: false :: tail =
      (A ++ [true]) ++ false :: tail by simp,
    show A.length + 1 = (A ++ [true]).length by simp,
    PallLean.Paper93.DeepMath.PathB.DIndexMachine.writeAt_boundary]
  simp [gappedBridgeCpyS, A, tail, List.append_assoc,
    show 2 * (j + 1) = 2 * j + 2 by omega, List.replicate_add]

theorem run_two_gapMark {s crossed : Bool} {p : ℕ} {T : List Bool}
    (hlo : T.getD p false = true)
    (hhi : T.getD (p + 1) false = true) :
    run gapCopyMachine 2 ⟨.copy (0, s) crossed, p, T⟩ =
      ⟨.copy (2, true) crossed, p + 2,
        writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  rw [List.getD_eq_getElem?_getD] at hlo hhi
  simp [step, gapCopyMachine, copyMachine, moveHead, hlo, hhi]

theorem run_gapped_mark (pre suffix : List Bool)
    (n a j : ℕ) (hj : j < a) (s : Bool) :
    let q := localOffset pre
    run gapCopyMachine 2
      ⟨.copy (0, s) false, q + 2 * j,
        localTape pre (gappedBridgeCpyS n a j j suffix)⟩ =
      ⟨.copy (2, true) false, q + 2 * j + 2,
        localTape pre (gappedBridgeCpyS n a (j + 1) j suffix)⟩ := by
  intro q
  have hlo : (localTape pre (gappedBridgeCpyS n a j j suffix)).getD
      (q + 2 * j) false = true := by
    rw [show q + 2 * j = localOffset pre + 2 * j by rfl,
      localTape_getD]
    exact gapped_getD_Adata n a j j (2 * j) suffix
      (by omega) (by omega) (by omega)
  have hhi : (localTape pre (gappedBridgeCpyS n a j j suffix)).getD
      (q + 2 * j + 1) false = true := by
    rw [show q + 2 * j + 1 = localOffset pre + (2 * j + 1) by omega,
      localTape_getD]
    exact gapped_getD_Adata n a j j (2 * j + 1) suffix
      (by omega) (by omega) (by omega)
  rw [run_two_gapMark hlo hhi]
  have hp : 2 * j + 1 <
      (gappedBridgeCpyS n a j j suffix).length := by
    rw [gappedBridgeCpyS_length n a j j suffix (by omega) (by omega)]
    omega
  rw [show q + 2 * j + 1 = localOffset pre + (2 * j + 1) by omega,
    localTape_writeAt pre _ _ false hp,
    gappedBridgeCpyS_mark n a j suffix hj]

/-- Four genuine transitions recognize the later target `00`, write `11`, and
intercept the original absolute reset into gap-aware home control. -/
theorem run_four_gapGrow {p : ℕ} {T : List Bool}
    (hlo : T.getD p false = false)
    (hhi : T.getD (p + 1) false = false) :
    run gapCopyMachine 4 ⟨.copy (2, true) true, p, T⟩ =
      ⟨.home (0, false) true scanHi, p + 1,
        writeAt (writeAt T p true) (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  rw [List.getD_eq_getElem?_getD] at hlo hhi
  simp [step, gapCopyMachine, copyMachine, moveHead, hlo, hhi]

theorem run_gapped_grow_enterHome (pre suffix : List Bool)
    (n a j : ℕ) (hj : j < a) :
    let q := localOffset pre
    let p := 2 * a + 4 + 2 * bridgePairs n + 2 * j
    run gapCopyMachine 4
      ⟨.copy (2, true) true, q + p,
        localTape pre (gappedBridgeCpyS n a (j + 1) j suffix)⟩ =
      ⟨.home (0, false) true scanHi, q + p + 1,
        localTape pre (gappedBridgeCpyS n a (j + 1) (j + 1) suffix)⟩ := by
  intro q p
  have hlo : (localTape pre
      (gappedBridgeCpyS n a (j + 1) j suffix)).getD (q + p) false = false := by
    rw [show q + p = localOffset pre + p by rfl, localTape_getD]
    exact gapped_getD_blank_lo n a (j + 1) j suffix (by omega) (by omega)
  have hhi : (localTape pre
      (gappedBridgeCpyS n a (j + 1) j suffix)).getD
        (q + p + 1) false = false := by
    rw [show q + p + 1 = localOffset pre + (p + 1) by omega,
      localTape_getD]
    exact gapped_getD_blank_hi n a (j + 1) j suffix (by omega) (by omega)
  rw [run_four_gapGrow hlo hhi]
  have hp : p < (gappedBridgeCpyS n a (j + 1) j suffix).length := by
    rw [gappedBridgeCpyS_length n a (j + 1) j suffix (by omega) (by omega)]
    simp [p, bridgePairs]
    omega
  have hp1 : p + 1 <
      (writeAt (gappedBridgeCpyS n a (j + 1) j suffix) p true).length := by
    rw [writeAt_length,
      gappedBridgeCpyS_length n a (j + 1) j suffix (by omega) (by omega)]
    simp [p, bridgePairs]
    omega
  rw [show q + p = localOffset pre + p by rfl,
    localTape_writeAt pre _ p true hp,
    show q + p + 1 = localOffset pre + (p + 1) by omega,
    localTape_writeAt pre _ (p + 1) true hp1]
  have hg := gappedBridgeCpyS_grow n a j suffix hj
  dsimp only at hg
  rw [powBridge_length_eq_pairs] at hg
  rw [hg]

end PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopyGrow

#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopyGrow.gappedBridgeCpyS_mark
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopyGrow.gappedBridgeCpyS_grow
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopyGrow.run_gapped_mark
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopyGrow.run_gapped_grow_enterHome
