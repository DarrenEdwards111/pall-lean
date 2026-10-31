import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMCSPPowerGapAwareCopyLift
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMCSPComparatorBridgeCopyRound

/-!
# MCSP verifier: concrete seek across the staged power gap

This file instantiates the gap-aware controller on the evolving physical table
copy tape.  It proves the exact read layout, transports ordinary high-cell
seek segments, inserts the unique two-step `00` crossing, and reaches the real
table-copy target scratch after both power counters.
-/

namespace PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopySeek

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCompare
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCopy
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyLift
open PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCopyLayout
open PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCopyRound
open PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopyMachine
open PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopyLift
open GapCopyState

/-- Evolving table-copy tape with the physically unavoidable `00` power-copy
home pair retained between the table marker and the two power counters. -/
def gappedBridgeCpyS (n a jA jC : ℕ) (suffix : List Bool) : List Bool :=
  cpyT a jA 0 ++ ([false, false] ++
    (powBridge n ++ (List.replicate (2 * jC) true ++
      (List.replicate (2 * (a - jC) + 2) false ++ suffix))))

theorem gappedBridgeCpyS_zero (n a : ℕ) (suffix : List Bool) :
    gappedBridgeCpyS n a 0 0 suffix =
      unaryD a ++ [false, false] ++ powBridge n ++
        List.replicate (2 * a + 2) false ++ suffix := by
  simp [gappedBridgeCpyS, cpyT_zero, List.append_assoc]

theorem gappedBridgeCpyS_length (n a jA jC : ℕ) (suffix : List Bool)
    (hA : jA ≤ a) (hC : jC ≤ a) :
    (gappedBridgeCpyS n a jA jC suffix).length =
      4 * a + 4 * (2 ^ n) + 10 + suffix.length := by
  simp [gappedBridgeCpyS, cpyT_length a jA 0 hA, powBridge_length]
  omega

private theorem gapped_getD_source (n a jA jC p : ℕ)
    (suffix : List Bool) (hA : jA ≤ a) (hp : p < 2 * a + 2) :
    (gappedBridgeCpyS n a jA jC suffix).getD p false =
      (cpyT a jA 0).getD p false := by
  rw [gappedBridgeCpyS, List.getD_append (h := by
    rw [cpyT_length a jA 0 hA]
    omega)]

theorem gapped_getD_Adata (n a jA jC c : ℕ) (suffix : List Bool)
    (hA : jA ≤ a) (h1 : 2 * jA ≤ c) (h2 : c < 2 * a) :
    (gappedBridgeCpyS n a jA jC suffix).getD c false = true := by
  rw [gapped_getD_source n a jA jC c suffix hA (by omega)]
  exact cpyT_getD_Adata a jA 0 c hA h1 h2

theorem gapped_getD_marker_hi (n a jA jC : ℕ) (suffix : List Bool)
    (hA : jA ≤ a) :
    (gappedBridgeCpyS n a jA jC suffix).getD (2 * a + 1) false = true := by
  rw [gapped_getD_source n a jA jC (2 * a + 1) suffix hA (by omega)]
  exact cpyT_getD_marker_hi a jA 0 hA

theorem gapped_getD_gap_lo (n a jA jC : ℕ) (suffix : List Bool)
    (hA : jA ≤ a) :
    (gappedBridgeCpyS n a jA jC suffix).getD (2 * a + 2) false = false := by
  rw [gappedBridgeCpyS,
    getD_append_length' (cpyT a jA 0) _ (cpyT_length a jA 0 hA) false]
  rfl

theorem gapped_getD_gap_hi (n a jA jC : ℕ) (suffix : List Bool)
    (hA : jA ≤ a) :
    (gappedBridgeCpyS n a jA jC suffix).getD (2 * a + 3) false = false := by
  rw [gappedBridgeCpyS,
    show 2 * a + 3 = (cpyT a jA 0).length + 1 by
      rw [cpyT_length a jA 0 hA],
    getD_append_left_length' _ _ rfl]
  rfl

theorem gapped_getD_bridge_high (n a jA jC i : ℕ)
    (suffix : List Bool) (hA : jA ≤ a) (hi : i < bridgePairs n) :
    (gappedBridgeCpyS n a jA jC suffix).getD
      (2 * a + 4 + 2 * i + 1) false = true := by
  rw [gappedBridgeCpyS,
    show 2 * a + 4 + 2 * i + 1 =
      (cpyT a jA 0).length + (2 + (2 * i + 1)) by
      rw [cpyT_length a jA 0 hA]; omega,
    getD_append_left_length' _ _ rfl]
  rw [show 2 + (2 * i + 1) = [false, false].length + (2 * i + 1) by simp,
    getD_append_left_length' [false, false] _ rfl,
    List.getD_append (h := by rw [powBridge_length_eq_pairs]; omega)]
  exact powBridge_getD_high n i hi

theorem gapped_getD_C_high (n a jA jC i : ℕ)
    (suffix : List Bool) (hA : jA ≤ a) (hi : i < jC) :
    (gappedBridgeCpyS n a jA jC suffix).getD
      (2 * a + 4 + 2 * bridgePairs n + 2 * i + 1) false = true := by
  rw [gappedBridgeCpyS,
    show 2 * a + 4 + 2 * bridgePairs n + 2 * i + 1 =
      (cpyT a jA 0).length +
        (2 + ((powBridge n).length + (2 * i + 1))) by
      rw [cpyT_length a jA 0 hA, powBridge_length_eq_pairs]; omega,
    getD_append_left_length' _ _ rfl]
  rw [show 2 + ((powBridge n).length + (2 * i + 1)) =
      [false, false].length + ((powBridge n).length + (2 * i + 1)) by simp,
    getD_append_left_length' [false, false] _ rfl,
    getD_append_left_length' (powBridge n) _ rfl,
    List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (by omega)

theorem gapped_getD_blank_lo (n a jA jC : ℕ) (suffix : List Bool)
    (hA : jA ≤ a) (_hC : jC ≤ a) :
    (gappedBridgeCpyS n a jA jC suffix).getD
      (2 * a + 4 + 2 * bridgePairs n + 2 * jC) false = false := by
  rw [gappedBridgeCpyS,
    show 2 * a + 4 + 2 * bridgePairs n + 2 * jC =
      (cpyT a jA 0).length +
        (2 + ((powBridge n).length + 2 * jC)) by
      rw [cpyT_length a jA 0 hA, powBridge_length_eq_pairs]; omega,
    getD_append_left_length' _ _ rfl]
  rw [show 2 + ((powBridge n).length + 2 * jC) =
      [false, false].length + ((powBridge n).length + 2 * jC) by simp,
    getD_append_left_length' [false, false] _ rfl,
    getD_append_left_length' (powBridge n) _ rfl,
    getD_append_length' _ _ List.length_replicate false]
  simp

theorem gapped_getD_blank_hi (n a jA jC : ℕ) (suffix : List Bool)
    (hA : jA ≤ a) (hC : jC ≤ a) :
    (gappedBridgeCpyS n a jA jC suffix).getD
      (2 * a + 4 + 2 * bridgePairs n + 2 * jC + 1) false = false := by
  rw [gappedBridgeCpyS,
    show 2 * a + 4 + 2 * bridgePairs n + 2 * jC + 1 =
      (cpyT a jA 0).length +
        (2 + ((powBridge n).length + (2 * jC + 1))) by
      rw [cpyT_length a jA 0 hA, powBridge_length_eq_pairs]; omega,
    getD_append_left_length' _ _ rfl]
  rw [show 2 + ((powBridge n).length + (2 * jC + 1)) =
      [false, false].length + ((powBridge n).length + (2 * jC + 1)) by simp,
    getD_append_left_length' [false, false] _ rfl,
    getD_append_left_length' (powBridge n) _ rfl,
    List.getD_append_right (h := by rw [List.length_replicate]; omega),
    List.length_replicate]
  rw [List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (by omega)

/-- Skip one ordinary pair with true high cell, preserving the gap flag. -/
theorem run_two_gapSeekHigh {crossed s : Bool} {p : ℕ} {T : List Bool}
    (hhi : T.getD (p + 1) false = true) :
    run gapCopyMachine 2 ⟨.copy (2, s) crossed, p, T⟩ =
      ⟨.copy (2, true) crossed, p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  rw [List.getD_eq_getElem?_getD] at hhi
  simp [step, gapCopyMachine, copyMachine, moveHead, hhi]

theorem run_gapSeekHigh (T : List Bool) (q k : ℕ)
    (crossed s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i + 1) false = true) :
    run gapCopyMachine (2 * k) ⟨.copy (2, s) crossed, q, T⟩ =
      ⟨.copy (2, if k = 0 then s else true) crossed,
        q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, run_add,
        ih (fun i hi => h i (by omega)),
        run_two_gapSeekHigh (h k (by omega))]
      rfl

/-- Exact seek from the freshly marked table pair to the genuine target
scratch.  The clock is the old bridge seek plus exactly two gap-crossing
steps, and the controller arrives with `crossedGap = true`. -/
theorem run_gapped_bridge_seek (pre suffix : List Bool)
    (n a j : ℕ) (hj : j < a) :
    let T := localTape pre (gappedBridgeCpyS n a (j + 1) j suffix)
    let q := localOffset pre
    run gapCopyMachine (2 * (a + bridgePairs n) + 2)
      ⟨.copy (2, true) false, q + 2 * j + 2, T⟩ =
      ⟨.copy (2, true) true,
        q + 2 * a + 4 + 2 * bridgePairs n + 2 * j, T⟩ := by
  intro T q
  let kLeft := a - j
  let gap := q + 2 * a + 2
  have hleft : run gapCopyMachine (2 * kLeft)
      ⟨.copy (2, true) false, q + 2 * j + 2, T⟩ =
      ⟨.copy (2, true) false, gap, T⟩ := by
    have h := run_gapSeekHigh T (q + 2 * j + 2) kLeft false true
      (fun i hi => by
        rw [show q + 2 * j + 2 + 2 * i + 1 =
          localOffset pre + (2 * (j + 1 + i) + 1) by omega,
          localTape_getD]
        by_cases hs : j + 1 + i < a
        · exact gapped_getD_Adata n a (j + 1) j
            (2 * (j + 1 + i) + 1) suffix (by omega) (by omega) (by omega)
        · rw [show j + 1 + i = a by omega]
          exact gapped_getD_marker_hi n a (j + 1) j suffix (by omega))
    have hk : kLeft ≠ 0 := by simp [kLeft]; omega
    simp [hk] at h
    rw [show q + 2 * j + 2 + 2 * kLeft = gap by
      simp [kLeft, gap]; omega] at h
    exact h
  have hgap : run gapCopyMachine 2
      ⟨.copy (2, true) false, gap, T⟩ =
      ⟨.copy (2, true) true, gap + 2, T⟩ := by
    apply run_gapSeek_two
    · rw [show gap = localOffset pre + (2 * a + 2) by rfl,
        localTape_getD]
      exact gapped_getD_gap_lo n a (j + 1) j suffix (by omega)
    · rw [show gap + 1 = localOffset pre + (2 * a + 3) by omega,
        localTape_getD]
      exact gapped_getD_gap_hi n a (j + 1) j suffix (by omega)
  have hright : run gapCopyMachine (2 * (bridgePairs n + j))
      ⟨.copy (2, true) true, gap + 2, T⟩ =
      ⟨.copy (2, true) true,
        gap + 2 + 2 * (bridgePairs n + j), T⟩ := by
    have h := run_gapSeekHigh T (gap + 2) (bridgePairs n + j) true true
      (fun i hi => by
        rw [show gap + 2 + 2 * i + 1 =
          localOffset pre + (2 * a + 4 + 2 * i + 1) by
          simp [gap]; omega,
          localTape_getD]
        by_cases hb : i < bridgePairs n
        · exact gapped_getD_bridge_high n a (j + 1) j i suffix
            (by omega) hb
        · rw [show 2 * a + 4 + 2 * i + 1 =
            2 * a + 4 + 2 * bridgePairs n +
              2 * (i - bridgePairs n) + 1 by omega]
          exact gapped_getD_C_high n a (j + 1) j
            (i - bridgePairs n) suffix (by omega) (by omega))
    by_cases hk : bridgePairs n + j = 0
    · simp [hk] at h ⊢
    · simpa [hk] using h
  rw [show 2 * (a + bridgePairs n) + 2 =
      2 * kLeft + (2 + 2 * (bridgePairs n + j)) by
      simp [kLeft]; omega,
    run_add, hleft, run_add, hgap, hright]
  congr 1 <;> simp [gap, q, localOffset] <;> omega

end PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopySeek

#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopySeek.run_gapSeekHigh
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopySeek.run_gapped_bridge_seek
