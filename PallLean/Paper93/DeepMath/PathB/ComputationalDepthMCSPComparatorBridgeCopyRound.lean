import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMCSPComparatorBridgeCopyLayout

/-!
# MCSP verifier: one operational table-copy round across the power bridge

The bridge layout is now lifted into the real `localCopyMachine`.  This file
proves the complete read suite, the longer rightward seek, target growth after
both power counters, and the delimiter-aware reset for one table-copy round.
-/

namespace PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCopyRound

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCompare
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCopy
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalHomeMachine
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyRun
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyLift
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyScans
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyGrow
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyRound
open PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCopyLayout
open LocalHomeState
open LocalCopyState

/-- Number of doubled pairs occupied by the two power counters. -/
def bridgePairs (n : ℕ) : ℕ := 2 * ((2 ^ n) + 1)

theorem powBridge_length_eq_pairs (n : ℕ) :
    (powBridge n).length = 2 * bridgePairs n := by
  rw [powBridge_length]
  simp [bridgePairs]
  ring

theorem bridgeCpyS_eq (n a jA jC : ℕ) (suffix : List Bool) :
    bridgeCpyS n a jA jC suffix =
      cpyT a jA 0 ++ (powBridge n ++
        (List.replicate (2 * jC) true ++
          (List.replicate (2 * (a - jC) + 2) false ++ suffix))) := by
  simp [bridgeCpyS, cpyT, List.append_assoc]

private theorem bridgeCpyS_getD_source (n a jA jC p : ℕ)
    (suffix : List Bool) (hA : jA ≤ a) (hp : p < 2 * a + 2) :
    (bridgeCpyS n a jA jC suffix).getD p false =
      (cpyT a jA 0).getD p false := by
  rw [bridgeCpyS_eq, List.getD_append (h := by
    rw [cpyT_length a jA 0 hA]
    omega)]

theorem bridgeCpyS_getD_Amark_lo (n a jA jC i : ℕ)
    (suffix : List Bool) (hA : jA ≤ a) (hi : i < jA) :
    (bridgeCpyS n a jA jC suffix).getD (2 * i) false = true := by
  rw [bridgeCpyS_getD_source n a jA jC (2 * i) suffix hA (by omega)]
  exact cpyT_getD_Amark_lo a jA 0 i hi

theorem bridgeCpyS_getD_Amark_hi (n a jA jC i : ℕ)
    (suffix : List Bool) (hA : jA ≤ a) (hi : i < jA) :
    (bridgeCpyS n a jA jC suffix).getD (2 * i + 1) false = false := by
  rw [bridgeCpyS_getD_source n a jA jC (2 * i + 1) suffix hA (by omega)]
  exact cpyT_getD_Amark_hi a jA 0 i hi

theorem bridgeCpyS_getD_Adata (n a jA jC c : ℕ)
    (suffix : List Bool) (hA : jA ≤ a)
    (h1 : 2 * jA ≤ c) (h2 : c < 2 * a) :
    (bridgeCpyS n a jA jC suffix).getD c false = true := by
  rw [bridgeCpyS_getD_source n a jA jC c suffix hA (by omega)]
  exact cpyT_getD_Adata a jA 0 c hA h1 h2

theorem bridgeCpyS_getD_marker_lo (n a jA jC : ℕ)
    (suffix : List Bool) (hA : jA ≤ a) :
    (bridgeCpyS n a jA jC suffix).getD (2 * a) false = false := by
  rw [bridgeCpyS_getD_source n a jA jC (2 * a) suffix hA (by omega)]
  exact cpyT_getD_marker_lo a jA 0 hA

theorem bridgeCpyS_getD_marker_hi (n a jA jC : ℕ)
    (suffix : List Bool) (hA : jA ≤ a) :
    (bridgeCpyS n a jA jC suffix).getD (2 * a + 1) false = true := by
  rw [bridgeCpyS_getD_source n a jA jC (2 * a + 1) suffix hA (by omega)]
  exact cpyT_getD_marker_hi a jA 0 hA

theorem bridgeCpyS_getD_bridge_high (n a jA jC i : ℕ)
    (suffix : List Bool) (hA : jA ≤ a) (hi : i < bridgePairs n) :
    (bridgeCpyS n a jA jC suffix).getD
        (2 * a + 2 + 2 * i + 1) false = true := by
  rw [bridgeCpyS_eq,
    show 2 * a + 2 + 2 * i + 1 = (2 * a + 2) + (2 * i + 1) by omega,
    getD_append_left_length' _ _ (cpyT_length a jA 0 hA)]
  rw [List.getD_append (h := by
    rw [powBridge_length_eq_pairs]
    omega)]
  exact powBridge_getD_high n i hi

theorem bridgeCpyS_getD_C (n a jA jC c : ℕ)
    (suffix : List Bool) (hA : jA ≤ a)
    (h1 : 2 * a + 2 + 2 * bridgePairs n ≤ c)
    (h2 : c < 2 * a + 2 + 2 * bridgePairs n + 2 * jC) :
    (bridgeCpyS n a jA jC suffix).getD c false = true := by
  let d := c - (2 * a + 2 + 2 * bridgePairs n)
  have hc : c = (2 * a + 2) + (2 * bridgePairs n + d) := by omega
  rw [bridgeCpyS_eq, hc,
    getD_append_left_length' _ _ (cpyT_length a jA 0 hA)]
  rw [show 2 * bridgePairs n + d = (powBridge n).length + d by
      rw [powBridge_length_eq_pairs],
    getD_append_left_length' _ _ rfl]
  rw [List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (by omega)

theorem bridgeCpyS_getD_blank_lo (n a jA jC : ℕ)
    (suffix : List Bool) (hA : jA ≤ a) (_hC : jC ≤ a) :
    (bridgeCpyS n a jA jC suffix).getD
        (2 * a + 2 + 2 * bridgePairs n + 2 * jC) false = false := by
  rw [bridgeCpyS_eq,
    show 2 * a + 2 + 2 * bridgePairs n + 2 * jC =
      (2 * a + 2) + (2 * bridgePairs n + 2 * jC) by omega,
    getD_append_left_length' _ _ (cpyT_length a jA 0 hA)]
  rw [show 2 * bridgePairs n + 2 * jC =
      (powBridge n).length + 2 * jC by rw [powBridge_length_eq_pairs],
    getD_append_left_length' _ _ rfl]
  rw [getD_append_length' _ _ List.length_replicate false]
  simp

theorem bridgeCpyS_getD_blank_hi (n a jA jC : ℕ)
    (suffix : List Bool) (hA : jA ≤ a) (hC : jC ≤ a) :
    (bridgeCpyS n a jA jC suffix).getD
        (2 * a + 2 + 2 * bridgePairs n + 2 * jC + 1) false = false := by
  rw [bridgeCpyS_eq,
    show 2 * a + 2 + 2 * bridgePairs n + 2 * jC + 1 =
      (2 * a + 2) + (2 * bridgePairs n + (2 * jC + 1)) by omega,
    getD_append_left_length' _ _ (cpyT_length a jA 0 hA)]
  rw [show 2 * bridgePairs n + (2 * jC + 1) =
      (powBridge n).length + (2 * jC + 1) by rw [powBridge_length_eq_pairs],
    getD_append_left_length' _ _ rfl]
  rw [List.getD_append_right (h := by rw [List.length_replicate]; omega),
    List.length_replicate]
  rw [List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (by omega)

/-- Every active pair from the table source through the copied target is
nonblank, so local-home reset cannot stop inside the bridge. -/
theorem bridgeCpyS_active_pair (n a j i : ℕ) (suffix : List Bool)
    (hj : j ≤ a) (hi : i < a + 1 + bridgePairs n + j) :
    (bridgeCpyS n a j j suffix).getD (2 * i) false = true ∨
      (bridgeCpyS n a j j suffix).getD (2 * i + 1) false = true := by
  by_cases hs : i < a
  · by_cases hm : i < j
    · exact Or.inl (bridgeCpyS_getD_Amark_lo n a j j i suffix hj hm)
    · exact Or.inl (bridgeCpyS_getD_Adata n a j j (2 * i) suffix hj
        (by omega) (by omega))
  · by_cases hmark : i = a
    · subst i
      exact Or.inr (bridgeCpyS_getD_marker_hi n a j j suffix hj)
    · by_cases hb : i < a + 1 + bridgePairs n
      · right
        rw [show 2 * i + 1 =
          2 * a + 2 + 2 * (i - (a + 1)) + 1 by omega]
        exact bridgeCpyS_getD_bridge_high n a j j
          (i - (a + 1)) suffix hj (by omega)
      · left
        exact bridgeCpyS_getD_C n a j j (2 * i) suffix hj
          (by omega) (by omega)

theorem localTape_bridge_active_pair (pre suffix : List Bool)
    (n a j i : ℕ) (hj : j ≤ a)
    (hi : i < a + 1 + bridgePairs n + j) :
    (localTape pre (bridgeCpyS n a j j suffix)).getD
        (pre.length + 2 + 2 * i) false = true ∨
      (localTape pre (bridgeCpyS n a j j suffix)).getD
        (pre.length + 2 + 2 * i + 1) false = true := by
  rcases bridgeCpyS_active_pair n a j i suffix hj hi with hlo | hhi
  · left
    rw [show pre.length + 2 + 2 * i = localOffset pre + 2 * i by
      simp [localOffset], localTape_getD]
    exact hlo
  · right
    rw [show pre.length + 2 + 2 * i + 1 =
      localOffset pre + (2 * i + 1) by simp [localOffset]; omega,
      localTape_getD]
    exact hhi

/-- The longer seek crosses the remainder of the table source, its marker,
both power counters, and the already-grown table target. -/
theorem run_seek_bridge_local (pre suffix : List Bool)
    (n a j : ℕ) (hj : j < a) :
    run localCopyMachine (2 * (a + bridgePairs n))
      (liftCopyCfg pre
        ⟨(2, true), 2 * j + 2,
          bridgeCpyS n a (j + 1) j suffix⟩) =
      liftCopyCfg pre
        ⟨(2, true),
          2 * a + 2 + 2 * bridgePairs n + 2 * j,
          bridgeCpyS n a (j + 1) j suffix⟩ := by
  have h := run_seekE_local pre (bridgeCpyS n a (j + 1) j suffix)
    (2 * j + 2) (a + bridgePairs n) true (fun i hi => by
      let pair := j + 1 + i
      by_cases hs : pair < a
      · exact bridgeCpyS_getD_Adata n a (j + 1) j
          (2 * j + 2 + 2 * i + 1) suffix (by omega) (by omega) (by omega)
      · by_cases hm : pair = a
        · rw [show 2 * j + 2 + 2 * i + 1 = 2 * a + 1 by omega]
          exact bridgeCpyS_getD_marker_hi n a (j + 1) j suffix (by omega)
        · by_cases hb : pair < a + 1 + bridgePairs n
          · rw [show 2 * j + 2 + 2 * i + 1 =
              2 * a + 2 + 2 * (pair - (a + 1)) + 1 by omega]
            exact bridgeCpyS_getD_bridge_high n a (j + 1) j
              (pair - (a + 1)) suffix (by omega) (by omega)
          · exact bridgeCpyS_getD_C n a (j + 1) j
              (2 * j + 2 + 2 * i + 1) suffix (by omega)
              (by omega) (by omega))
  have hpos : 2 * j + 2 + 2 * (a + bridgePairs n) =
      2 * a + 2 + 2 * bridgePairs n + 2 * j := by ring
  rw [hpos] at h
  simp at h
  exact h

theorem run_mark_bridge_local (pre suffix : List Bool)
    (n a j : ℕ) (hj : j < a) (s : Bool) :
    run localCopyMachine 2
      (liftCopyCfg pre
        ⟨(0, s), 2 * j, bridgeCpyS n a j j suffix⟩) =
      liftCopyCfg pre
        ⟨(2, true), 2 * j + 2,
          bridgeCpyS n a (j + 1) j suffix⟩ := by
  have h := run_two_mark_local (pre := pre) (s := s)
    (p := 2 * j) (T := bridgeCpyS n a j j suffix)
    (bridgeCpyS_getD_Adata n a j j (2 * j) suffix
      (by omega) (by omega) (by omega))
    (bridgeCpyS_getD_Adata n a j j (2 * j + 1) suffix
      (by omega) (by omega) (by omega))
    (by rw [bridgeCpyS_length n a j j suffix (by omega) (by omega)]; omega)
  rw [bridgeCpyS_mark n a j suffix hj] at h
  exact h

theorem run_grow_bridge_enterHome (pre suffix : List Bool)
    (n a j : ℕ) (hj : j < a) :
    let p := 2 * a + 2 + 2 * bridgePairs n + 2 * j
    run localCopyMachine 4
      (liftCopyCfg pre
        ⟨(2, true), p, bridgeCpyS n a (j + 1) j suffix⟩) =
      ⟨.home (0, false) scanHi, localOffset pre + p + 1,
        localTape pre (bridgeCpyS n a (j + 1) (j + 1) suffix)⟩ := by
  intro p
  have h := run_four_grow_enterHome_local pre
    (p := p) (T := bridgeCpyS n a (j + 1) j suffix)
    (bridgeCpyS_getD_blank_lo n a (j + 1) j suffix (by omega) (by omega))
    (by simpa [p] using
      bridgeCpyS_getD_blank_hi n a (j + 1) j suffix (by omega) (by omega))
    (by
      rw [bridgeCpyS_length n a (j + 1) j suffix (by omega) (by omega)]
      dsimp [p]
      simp [bridgePairs]
      omega)
  have hg := bridgeCpyS_grow n a j suffix hj
  dsimp only at hg
  rw [powBridge_length_eq_pairs] at hg
  rw [hg] at h
  simpa [p, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem run_grow_bridge_reset (pre suffix : List Bool)
    (n a j : ℕ) (hj : j < a) :
    let p := 2 * a + 2 + 2 * bridgePairs n + 2 * j
    let k := a + 1 + bridgePairs n + (j + 1)
    run localCopyMachine (4 + (2 * k + 4))
      (liftCopyCfg pre
        ⟨(2, true), p, bridgeCpyS n a (j + 1) j suffix⟩) =
      liftCopyCfg pre
        ⟨(0, false), 0, bridgeCpyS n a (j + 1) (j + 1) suffix⟩ := by
  intro p k
  rw [run_add, run_grow_bridge_enterHome pre suffix n a j hj]
  have h := run_localCopy_home_resume (0, false)
    (localTape pre (bridgeCpyS n a (j + 1) (j + 1) suffix))
    pre.length k
    (localTape_home_lo pre _)
    (localTape_home_hi pre _)
    (fun i hi => localTape_bridge_active_pair pre suffix n a (j + 1) i
      (by omega) (by simpa [k, Nat.add_assoc] using hi))
  have hhead : localOffset pre + p + 1 =
      pre.length + 1 + 2 * k := by
    simp [localOffset, p, k]
    ring
  rw [hhead]
  simpa [liftCopyCfg, localOffset] using h

/-- Exact clock for one physical bridge-copy round. -/
def bridgeRoundClock (n a j : ℕ) : ℕ :=
  2 * j + 2 + 2 * (a + bridgePairs n) +
    (4 + (2 * (a + 1 + bridgePairs n + (j + 1)) + 4))

theorem bridgeRoundClock_eq (n a j : ℕ) :
    bridgeRoundClock n a j =
      4 * a + 4 * j + 4 * bridgePairs n + 14 := by
  unfold bridgeRoundClock
  ring

/-- One complete real-machine bridge-copy round. -/
theorem run_bridge_round (pre suffix : List Bool)
    (n a j : ℕ) (hj : j < a) (s : Bool) :
    run localCopyMachine (bridgeRoundClock n a j)
      (liftCopyCfg pre
        ⟨(0, s), 0, bridgeCpyS n a j j suffix⟩) =
      liftCopyCfg pre
        ⟨(0, false), 0, bridgeCpyS n a (j + 1) (j + 1) suffix⟩ := by
  have hfind :=
    run_findSkip_local pre (bridgeCpyS n a j j suffix) 0 j s
      (fun i hi => ⟨by simpa using
          bridgeCpyS_getD_Amark_lo n a j j i suffix (by omega) hi,
        by simpa using
          bridgeCpyS_getD_Amark_hi n a j j i suffix (by omega) hi⟩)
  simp only [Nat.zero_add] at hfind
  rw [bridgeRoundClock,
    show 2 * j + 2 + 2 * (a + bridgePairs n) +
        (4 + (2 * (a + 1 + bridgePairs n + (j + 1)) + 4)) =
      2 * j + (2 + (2 * (a + bridgePairs n) +
        (4 + (2 * (a + 1 + bridgePairs n + (j + 1)) + 4)))) by omega,
    run_add,
    hfind,
    run_add,
    run_mark_bridge_local pre suffix n a j hj (if j = 0 then s else true),
    run_add,
    run_seek_bridge_local pre suffix n a j hj,
    run_grow_bridge_reset pre suffix n a j hj]

end PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCopyRound

#print axioms PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCopyRound.run_seek_bridge_local
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCopyRound.run_grow_bridge_reset
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCopyRound.run_bridge_round
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCopyRound.bridgeRoundClock_eq
