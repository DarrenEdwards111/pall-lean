import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMCSPCounterLocalCopyGrow

/-!
# MCSP verifier: one complete delimited local-copy round

This file closes one full round of the physical local-copy controller:

    find → mark → seek → grow → local-home reset → resume.

The key layout fact is that every active doubled pair between the `00` home
delimiter and the newly grown target end is nonblank: source pairs are `10`
or `11`, the unary boundary is `01`, and target pairs are `11`.  Therefore the
proved local-home scanner crosses all of them and stops only at the delimiter.

The resulting theorem is a run of the real fixed `localCopyMachine`, preserves
the arbitrary live prefix, evolves `cpyS n j j suffix` to
`cpyS n (j+1) (j+1) suffix`, returns to local counter home, and has an exact
clock.
-/

namespace PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyRound

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCopy
open PallLean.Paper93.DeepMath.PathB.MCSPCounterCopyScratchMachine
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalHomeMachine
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyRun
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyLift
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyScans
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyGrow
open LocalHomeState
open LocalCopyState

theorem localTape_home_lo (pre T : List Bool) :
    (localTape pre T).getD pre.length false = false := by
  simp [localTape, homePrefix]

theorem localTape_home_hi (pre T : List Bool) :
    (localTape pre T).getD (pre.length + 1) false = false := by
  rw [localTape, homePrefix, List.append_assoc,
    PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCompare.getD_append_left_length'
      pre ([false, false] ++ T) rfl 1 false]
  rfl

/-- Every active pair of a fully grown round tape is distinct from `00`. -/
theorem cpyS_active_pair (n j i : ℕ) (suffix : List Bool)
    (hj : j ≤ n) (hi : i < n + j + 1) :
    (cpyS n j j suffix).getD (2 * i) false = true ∨
      (cpyS n j j suffix).getD (2 * i + 1) false = true := by
  rcases Nat.lt_trichotomy i n with hin | hin | hin
  · by_cases him : i < j
    · exact Or.inl (cpyS_getD_Amark_lo n j j i suffix hj hj him)
    · exact Or.inl (cpyS_getD_Adata n j j (2 * i) suffix hj hj
        (by omega) (by omega))
  · subst i
    exact Or.inr (cpyS_getD_marker_hi n j j suffix hj hj)
  · exact Or.inl (cpyS_getD_C n j j (2 * i) suffix hj hj
      (by omega) (by omega))

/-- Lift active-pair nonblankness past the arbitrary prefix and delimiter. -/
theorem localTape_cpyS_active_pair (pre suffix : List Bool)
    (n j i : ℕ) (hj : j ≤ n) (hi : i < n + j + 1) :
    (localTape pre (cpyS n j j suffix)).getD
        (pre.length + 2 + 2 * i) false = true ∨
      (localTape pre (cpyS n j j suffix)).getD
        (pre.length + 2 + 2 * i + 1) false = true := by
  have h := cpyS_active_pair n j i suffix hj hi
  rcases h with hlo | hhi
  · left
    rw [show pre.length + 2 + 2 * i =
        localOffset pre + 2 * i by simp [localOffset],
      localTape_getD]
    exact hlo
  · right
    rw [show pre.length + 2 + 2 * i + 1 =
        localOffset pre + (2 * i + 1) by simp [localOffset]; omega,
      localTape_getD]
    exact hhi

/-- After growth has entered local-home control, finish the scan and resume
copy state `0` at the local counter origin. -/
theorem run_growHome_resume (pre suffix : List Bool)
    (n j : ℕ) (hj : j < n) :
    run localCopyMachine (2 * (n + (j + 1) + 1) + 4)
      ⟨.home (0, false) scanHi,
        localOffset pre + (2 * n + 2 * j + 3),
        localTape pre (cpyS n (j + 1) (j + 1) suffix)⟩ =
      liftCopyCfg pre
        ⟨(0, false), 0, cpyS n (j + 1) (j + 1) suffix⟩ := by
  have h := run_localCopy_home_resume (0, false)
    (localTape pre (cpyS n (j + 1) (j + 1) suffix))
    pre.length (n + (j + 1) + 1)
    (localTape_home_lo pre _)
    (localTape_home_hi pre _)
    (fun i hi => by
      simpa [Nat.add_assoc] using
        localTape_cpyS_active_pair pre suffix n (j + 1) i
          (by omega) hi)
  have hhead : localOffset pre + (2 * n + 2 * j + 3) =
      pre.length + 1 + 2 * (n + (j + 1) + 1) := by
    simp [localOffset]
    ring
  rw [hhead]
  simpa [liftCopyCfg, localOffset] using h

/-- Grow plus its variable-distance local reset. -/
def localGrowResetClock (n j : ℕ) : ℕ :=
  4 + (2 * (n + (j + 1) + 1) + 4)

theorem run_grow_cpyS_reset (pre suffix : List Bool)
    (n j : ℕ) (hj : j < n) :
    run localCopyMachine (localGrowResetClock n j)
      (liftCopyCfg pre
        ⟨(2, true), 2 * n + 2 * j + 2,
          cpyS n (j + 1) j suffix⟩) =
      liftCopyCfg pre
        ⟨(0, false), 0, cpyS n (j + 1) (j + 1) suffix⟩ := by
  rw [localGrowResetClock, run_add,
    run_grow_cpyS_enterHome pre suffix n j hj,
    run_growHome_resume pre suffix n j hj]

/-- The source mark pass specialized to the evolving round tape. -/
theorem run_mark_cpyS_local (pre suffix : List Bool)
    (n j : ℕ) (hj : j < n) (s : Bool) :
    run localCopyMachine 2
      (liftCopyCfg pre ⟨(0, s), 2 * j, cpyS n j j suffix⟩) =
      liftCopyCfg pre
        ⟨(2, true), 2 * j + 2, cpyS n (j + 1) j suffix⟩ := by
  have h := run_two_mark_local (pre := pre) (s := s)
    (p := 2 * j) (T := cpyS n j j suffix)
    (cpyS_getD_Adata n j j (2 * j) suffix (by omega) (by omega)
      (by omega) (by omega))
    (cpyS_getD_Adata n j j (2 * j + 1) suffix (by omega) (by omega)
      (by omega) (by omega))
    (by rw [cpyS_length n j j suffix (by omega) (by omega)]; omega)
  rw [cpyS_mark n j suffix hj] at h
  exact h

/-- Exact clock of one complete local round. -/
def localRoundClock (n j : ℕ) : ℕ :=
  2 * j + 2 + 2 * n + localGrowResetClock n j

theorem localRoundClock_eq (n j : ℕ) :
    localRoundClock n j = 4 * n + 4 * j + 14 := by
  unfold localRoundClock localGrowResetClock
  ring

/-- One complete physical local-copy round. -/
theorem run_localCopy_round (pre suffix : List Bool)
    (n j : ℕ) (hj : j < n) (s : Bool) :
    run localCopyMachine (localRoundClock n j)
      (liftCopyCfg pre ⟨(0, s), 0, cpyS n j j suffix⟩) =
      liftCopyCfg pre
        ⟨(0, false), 0, cpyS n (j + 1) (j + 1) suffix⟩ := by
  rw [localRoundClock,
    show 2 * j + 2 + 2 * n + localGrowResetClock n j =
      2 * j + (2 + (2 * n + localGrowResetClock n j)) by omega,
    run_add,
    run_findSkip_cpyS_local pre suffix n j (by omega) s,
    run_add,
    run_mark_cpyS_local pre suffix n j hj
      (if j = 0 then s else true),
    run_add,
    run_seekE_cpyS_local pre suffix n j hj,
    run_grow_cpyS_reset pre suffix n j hj]

end PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyRound

#print axioms PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyRound.run_growHome_resume
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyRound.run_localCopy_round
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyRound.localRoundClock_eq
