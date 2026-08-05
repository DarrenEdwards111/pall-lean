import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeRelativePrefix

/-!
# Left-boundary safety calculus for runtime lookup composition

The fixed runtime lookup is assembled from head-preserving sequential
compositors.  This file proves that `LeftSafeRun` composes through their left
phase, one-step handoff, right phase, early halt, and unused frozen slack.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeLeftSafety

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryTerminal
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceCompact
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceLookup

/-- The fixed source selector never issues a left move at all; its backward
control transfer is an explicit reset. -/
theorem sourceSelect_no_left (s : SourceSelectState) (b : Bool) :
    (sourceSelectMachine.δ s b).2.2 ≠ 0 := by
  cases s <;> simp [sourceSelectMachine] <;> split_ifs <;> simp_all

theorem sourceSelect_leftSafe_any (c : Cfg sourceSelectMachine) (n : Nat) :
    LeftSafeRun sourceSelectMachine c n := by
  intro i _ _ hmove
  exact absurd hmove (sourceSelect_no_left _ _)

theorem leftSafeRun_of_halted {M : Machine} {c : Cfg M} (n : Nat)
    (hh : M.halt c.st = true) : LeftSafeRun M c n := by
  intro i _ hlive _
  have hf : run M i c = c := run_of_halted M hh i
  rw [hf] at hlive
  simp [hh] at hlive

theorem headSeqAccept_leftSafe_inl (M1 M2 : Machine) (c : Cfg M1)
    (t : Nat) (hno : ∀ i < t, M1.halt (run M1 i c).st = false)
    (hsafe : LeftSafeRun M1 c t) :
    LeftSafeRun (headSeqAcceptMachine M1 M2)
      (headAcceptInlCfg M1 M2 c) t := by
  intro i hi hhalt hmove
  have hr := headSeqAccept_run_inl M1 M2 c i
    (fun j hj => hno j (by omega))
  rw [hr] at hhalt hmove ⊢
  have hh1 : M1.halt (run M1 i c).st = false := hno i hi
  have hm1 : (M1.δ (run M1 i c).st
      ((run M1 i c).tp.getD (run M1 i c).hd false)).2.2 = 0 := by
    simpa [headSeqAcceptMachine, headAcceptInlCfg, hh1] using hmove
  exact hsafe i hi hh1 hm1

theorem headSeqAccept_leftSafe_handoff (M1 M2 : Machine) (c : Cfg M1)
    (hh : M1.halt c.st = true) :
    LeftSafeRun (headSeqAcceptMachine M1 M2)
      (headAcceptInlCfg M1 M2 c) 1 := by
  apply leftSafeRun_one_of_not_left
  simp [headSeqAcceptMachine, headAcceptInlCfg, hh]

theorem headSeqAccept_leftSafe_inr (M1 M2 : Machine) (c : Cfg M2)
    (t : Nat) (hsafe : LeftSafeRun M2 c t) :
    LeftSafeRun (headSeqAcceptMachine M1 M2)
      (headAcceptInrCfg M1 M2 c) t := by
  intro i hi hhalt hmove
  rw [headSeqAccept_run_inr M1 M2 c i] at hhalt hmove ⊢
  have hh2 : M2.halt (run M2 i c).st = false := by
    simpa [headSeqAcceptMachine, headAcceptInrCfg] using hhalt
  have hm2 : (M2.δ (run M2 i c).st
      ((run M2 i c).tp.getD (run M2 i c).hd false)).2.2 = 0 := by
    simpa [headSeqAcceptMachine, headAcceptInrCfg] using hmove
  exact hsafe i hi hh2 hm2

/-- Complete safety composition with the same least-halt slack absorption as
`headSeqAccept_run`. -/
theorem headSeqAccept_leftSafe (M1 M2 : Machine) (T0 T1 : List Bool)
    (t1 t2 p1 : Nat) (s1 : M1.State)
    (h1 : run M1 t1 (init M1 T0) = ⟨s1, p1, T1⟩)
    (hh1 : M1.halt s1 = true)
    (hsafe1 : LeftSafeRun M1 (init M1 T0) t1)
    (hsafe2 : LeftSafeRun M2 ⟨M2.start, p1, T1⟩ t2)
    (hh2 : M2.halt (run M2 t2 ⟨M2.start, p1, T1⟩).st = true) :
    LeftSafeRun (headSeqAcceptMachine M1 M2)
      (init (headSeqAcceptMachine M1 M2) T0) (t1 + 1 + t2) := by
  have hex : ∃ t, M1.halt (run M1 t (init M1 T0)).st = true :=
    ⟨t1, by rw [h1]; exact hh1⟩
  let tm := Nat.find hex
  have htm : M1.halt (run M1 tm (init M1 T0)).st = true :=
    Nat.find_spec hex
  have htmle : tm ≤ t1 := Nat.find_le (by rw [h1]; exact hh1)
  have hfrozen : run M1 tm (init M1 T0) = ⟨s1, p1, T1⟩ := by
    rw [← run_stable M1 T0 htmle htm, h1]
  have hno : ∀ i < tm,
      M1.halt (run M1 i (init M1 T0)).st = false := by
    intro i hi
    simpa using Nat.find_min hex hi
  have hs1 : LeftSafeRun (headSeqAcceptMachine M1 M2)
      (init (headSeqAcceptMachine M1 M2) T0) tm := by
    change LeftSafeRun (headSeqAcceptMachine M1 M2)
      (headAcceptInlCfg M1 M2 (init M1 T0)) tm
    exact headSeqAccept_leftSafe_inl M1 M2 (init M1 T0) tm hno
      (fun i hi => hsafe1 i (by omega))
  have hrun1 : run (headSeqAcceptMachine M1 M2) tm
      (init (headSeqAcceptMachine M1 M2) T0) =
      headAcceptInlCfg M1 M2 (⟨s1, p1, T1⟩ : Cfg M1) := by
    change run (headSeqAcceptMachine M1 M2) tm
      (headAcceptInlCfg M1 M2 (init M1 T0)) = _
    rw [headSeqAccept_run_inl M1 M2 _ tm hno, hfrozen]
  have hsSwitch : LeftSafeRun (headSeqAcceptMachine M1 M2)
      (run (headSeqAcceptMachine M1 M2) tm
        (init (headSeqAcceptMachine M1 M2) T0)) 1 := by
    rw [hrun1]
    exact headSeqAccept_leftSafe_handoff M1 M2 _ hh1
  have hafter : run (headSeqAcceptMachine M1 M2) 1
      (run (headSeqAcceptMachine M1 M2) tm
        (init (headSeqAcceptMachine M1 M2) T0)) =
      headAcceptInrCfg M1 M2 ⟨M2.start, p1, T1⟩ := by
    rw [hrun1, run_succ, run_zero]
    exact headSeqAccept_step_handoff M1 M2 _ hh1
  have hs2 : LeftSafeRun (headSeqAcceptMachine M1 M2)
      (run (headSeqAcceptMachine M1 M2) (tm + 1)
        (init (headSeqAcceptMachine M1 M2) T0)) t2 := by
    rw [run_add, hafter]
    exact headSeqAccept_leftSafe_inr M1 M2 _ t2 hsafe2
  have hsMain : LeftSafeRun (headSeqAcceptMachine M1 M2)
      (init (headSeqAcceptMachine M1 M2) T0) (tm + 1 + t2) :=
    leftSafeRun_add (leftSafeRun_add hs1 hsSwitch) hs2
  have hhaltAt : (headSeqAcceptMachine M1 M2).halt
      (run (headSeqAcceptMachine M1 M2) (tm + 1 + t2)
        (init (headSeqAcceptMachine M1 M2) T0)).st =
      M2.halt (run M2 t2 ⟨M2.start, p1, T1⟩).st := by
    rw [show tm + 1 + t2 = (tm + 1) + t2 by omega, run_add]
    rw [run_add, hafter, headSeqAccept_run_inr]
    rfl
  have hsSlack : LeftSafeRun (headSeqAcceptMachine M1 M2)
      (run (headSeqAcceptMachine M1 M2) (tm + 1 + t2)
        (init (headSeqAcceptMachine M1 M2) T0)) (t1 - tm) :=
    leftSafeRun_of_halted _ (by rw [hhaltAt, hh2])
  have hsAll := leftSafeRun_add hsMain hsSlack
  convert hsAll using 1 <;> omega

/-- `headSeqMachine` and `headSeqAcceptMachine` have exactly the same
transition graph; only their observational `accept` field differs. -/
def headCfgToAccept (M1 M2 : Machine) (c : Cfg (headSeqMachine M1 M2)) :
    Cfg (headSeqAcceptMachine M1 M2) :=
  ⟨c.st, c.hd, c.tp⟩

theorem headSeq_run_map_accept (M1 M2 : Machine)
    (c : Cfg (headSeqMachine M1 M2))
    (t : Nat) :
    run (headSeqAcceptMachine M1 M2) t (headCfgToAccept M1 M2 c) =
      headCfgToAccept M1 M2 (run (headSeqMachine M1 M2) t c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [run_succ, run_succ, ih]
      cases cs : run (headSeqMachine M1 M2) t c with
      | mk st hd tp =>
        cases st with
        | inl s =>
            simp [step, headSeqMachine, headSeqAcceptMachine, headCfgToAccept]
        | inr s =>
            by_cases hh : M2.halt s = true <;>
              simp [step, headSeqMachine, headSeqAcceptMachine,
                headCfgToAccept, hh]

/-- The ordinary head-preserving compositor inherits the same complete
left-safety composition theorem. -/
theorem headSeq_leftSafe (M1 M2 : Machine) (T0 T1 : List Bool)
    (t1 t2 p1 : Nat) (s1 : M1.State)
    (h1 : run M1 t1 (init M1 T0) = ⟨s1, p1, T1⟩)
    (hh1 : M1.halt s1 = true)
    (hsafe1 : LeftSafeRun M1 (init M1 T0) t1)
    (hsafe2 : LeftSafeRun M2 ⟨M2.start, p1, T1⟩ t2)
    (hh2 : M2.halt (run M2 t2 ⟨M2.start, p1, T1⟩).st = true) :
    LeftSafeRun (headSeqMachine M1 M2)
      (init (headSeqMachine M1 M2) T0) (t1 + 1 + t2) := by
  have hs := headSeqAccept_leftSafe M1 M2 T0 T1 t1 t2 p1 s1
    h1 hh1 hsafe1 hsafe2 hh2
  intro i hi hhalt hmove
  have hrun := headSeq_run_map_accept M1 M2
    (init (headSeqMachine M1 M2) T0) i
  have hhalt' : (headSeqAcceptMachine M1 M2).halt
      (run (headSeqAcceptMachine M1 M2) i
        (init (headSeqAcceptMachine M1 M2) T0)).st = false := by
    rw [show init (headSeqAcceptMachine M1 M2) T0 =
      headCfgToAccept M1 M2 (init (headSeqMachine M1 M2) T0) from rfl,
      hrun]
    simpa [headSeqMachine, headSeqAcceptMachine, headCfgToAccept] using hhalt
  have hmove' : ((headSeqAcceptMachine M1 M2).δ
      (run (headSeqAcceptMachine M1 M2) i
        (init (headSeqAcceptMachine M1 M2) T0)).st
      ((run (headSeqAcceptMachine M1 M2) i
        (init (headSeqAcceptMachine M1 M2) T0)).tp.getD
        (run (headSeqAcceptMachine M1 M2) i
          (init (headSeqAcceptMachine M1 M2) T0)).hd false)).2.2 = 0 := by
    rw [show init (headSeqAcceptMachine M1 M2) T0 =
      headCfgToAccept M1 M2 (init (headSeqMachine M1 M2) T0) from rfl,
      hrun]
    simpa [headSeqMachine, headSeqAcceptMachine, headCfgToAccept] using hmove
  have hp := hs i hi hhalt' hmove'
  rw [show init (headSeqAcceptMachine M1 M2) T0 =
    headCfgToAccept M1 M2 (init (headSeqMachine M1 M2) T0) from rfl,
    hrun] at hp
  simpa [headCfgToAccept] using hp

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeLeftSafety

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeLeftSafety.headSeqAccept_leftSafe
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeLeftSafety.headSeq_leftSafe
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeLeftSafety.sourceSelect_leftSafe_any
