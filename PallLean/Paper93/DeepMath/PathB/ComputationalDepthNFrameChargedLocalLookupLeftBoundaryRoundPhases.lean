import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupLeftBoundaryTerminal
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinRoundInvariant

/-!
# Charged local lookup: variable round-phase left-boundary safety

The two variable-length machines used by every counter-present round are
proved to keep a positive head throughout their canonical runs.  Their runs
are then transported into both corresponding master-machine groups.  These
are the only unbounded phase obligations in the remaining round proof.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryRoundPhases

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinMaster
open PallLean.Paper93.DeepMath.PathB.CookLevinMasterSim
open PallLean.Paper93.DeepMath.PathB.CookLevinRendShift
open PallLean.Paper93.DeepMath.PathB.CookLevinScanLeftSep
open PallLean.Paper93.DeepMath.PathB.CookLevinPhaseBounds
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryTerminal

/-! ## `rendShift`: the head never retreats behind its phase origin -/

theorem rendShift_head_ge {c0 c1 : Bool} {q K : Nat} {T : List Bool}
    (hnr : ∀ j < K,
      (T.getD (q + 2 * j + 2) false && !(T.getD (q + 2 * j + 3) false)) = false)
    {i : Nat} (hi : i < 8 * K + 8) :
    q ≤ (run rendShift i ⟨(0, c0, c1), q, T⟩).hd := by
  have hir : i = 8 * (i / 8) + i % 8 := by omega
  have hjK : i / 8 ≤ K := by omega
  rw [hir, run_add,
    run_shift_k T q c0 c1 (i / 8) (fun j hj => hnr j (by omega))]
  have hr : i % 8 < 8 := Nat.mod_lt _ (by omega)
  interval_cases hrem : i % 8
  all_goals
    simp only [run_zero, run_succ, step_fetch1, step_fetch2, step_readlo,
      CookLevinRendShift.step_readhi, step_back1, step_back2, step_writelo]
    omega

theorem masterSHA_leftSafe {c0 c1 : Bool} {q K : Nat} {T : List Bool}
    (hq : 0 < q)
    (hnr : ∀ j < K,
      (T.getD (q + 2 * j + 2) false && !(T.getD (q + 2 * j + 3) false)) = false) :
    LeftSafeRun masterM ⟨(3, 0, c0, c1), q, T⟩ (8 * K + 8) := by
  intro i hi _ _
  have hmin : ∀ j < i,
      (run rendShift j ⟨(0, c0, c1), q, T⟩).st.1 ≠ 8 :=
    fun j hj => rendShift_no_early_halt hnr j (by omega)
  rw [show (⟨(3, 0, c0, c1), q, T⟩ : Cfg masterM) =
      embedRend 3 ⟨(0, c0, c1), q, T⟩ from rfl,
    sim_run_SHA i ⟨(0, c0, c1), q, T⟩ hmin]
  exact lt_of_lt_of_le hq (rendShift_head_ge hnr hi)

theorem masterSHB_leftSafe {c0 c1 : Bool} {q K : Nat} {T : List Bool}
    (hq : 0 < q)
    (hnr : ∀ j < K,
      (T.getD (q + 2 * j + 2) false && !(T.getD (q + 2 * j + 3) false)) = false) :
    LeftSafeRun masterM ⟨(6, 0, c0, c1), q, T⟩ (8 * K + 8) := by
  intro i hi _ _
  have hmin : ∀ j < i,
      (run rendShift j ⟨(0, c0, c1), q, T⟩).st.1 ≠ 8 :=
    fun j hj => rendShift_no_early_halt hnr j (by omega)
  rw [show (⟨(6, 0, c0, c1), q, T⟩ : Cfg masterM) =
      embedRend 6 ⟨(0, c0, c1), q, T⟩ from rfl,
    sim_run_SHB i ⟨(0, c0, c1), q, T⟩ hmin]
  exact lt_of_lt_of_le hq (rendShift_head_ge hnr hi)

/-! ## `scanLeftSep`: the canonical scan stays above its target low cell -/

theorem scanLeftSep_head_pos {st : Bool} {P m : Nat} {T : List Bool}
    (hbase : 2 * m + 2 ≤ P)
    (hns : ∀ j < m,
      (!(T.getD (P - 2 * j - 1) false) && T.getD (P - 2 * j) false) = false)
    {i : Nat} (hi : i < 2 * m + 2) :
    0 < (run scanLeftSep i ⟨(0, st), P, T⟩).hd := by
  have hir : i = 2 * (i / 2) + i % 2 := by omega
  have hjm : i / 2 ≤ m := by omega
  have htail : 2 ≤ P - 2 * m := by omega
  have hmono : P - 2 * m ≤ P - 2 * (i / 2) :=
    Nat.sub_le_sub_left (Nat.mul_le_mul_left 2 hjm) P
  have hpos : 2 ≤ P - 2 * (i / 2) := htail.trans hmono
  rw [hir, run_add,
    run_scan_left T P st (i / 2) (fun j hj => hns j (by omega))]
  have hr : i % 2 < 2 := Nat.mod_lt _ (by omega)
  interval_cases hrem : i % 2
  · simp
    omega
  · rw [show (1 : Nat) = 0 + 1 from rfl, run_succ, run_zero,
      CookLevinScanLeftSep.step_readhi]
    exact Nat.sub_pos_of_lt hpos

theorem masterRANCH1_leftSafe {st : Bool} {P m : Nat} {T : List Bool}
    (hbase : 2 * m + 2 ≤ P)
    (hns : ∀ j < m,
      (!(T.getD (P - 2 * j - 1) false) && T.getD (P - 2 * j) false) = false) :
    LeftSafeRun masterM ⟨(4, 0, st, false), P, T⟩ (2 * m + 2) := by
  intro i hi _ _
  have hmin : ∀ j < i,
      (run scanLeftSep j ⟨(0, st), P, T⟩).st.1 ≠ 2 :=
    fun j hj => scanLeftSep_no_early_halt hns j (by omega)
  rw [show (⟨(4, 0, st, false), P, T⟩ : Cfg masterM) =
      embedScanL 4 ⟨(0, st), P, T⟩ from rfl,
    sim_run_RANCH1 i ⟨(0, st), P, T⟩ hmin]
  exact scanLeftSep_head_pos hbase hns hi

theorem masterRANCH2_leftSafe {st : Bool} {P m : Nat} {T : List Bool}
    (hbase : 2 * m + 2 ≤ P)
    (hns : ∀ j < m,
      (!(T.getD (P - 2 * j - 1) false) && T.getD (P - 2 * j) false) = false) :
    LeftSafeRun masterM ⟨(7, 0, st, false), P, T⟩ (2 * m + 2) := by
  intro i hi _ _
  have hmin : ∀ j < i,
      (run scanLeftSep j ⟨(0, st), P, T⟩).st.1 ≠ 2 :=
    fun j hj => scanLeftSep_no_early_halt hns j (by omega)
  rw [show (⟨(7, 0, st, false), P, T⟩ : Cfg masterM) =
      embedScanL 7 ⟨(0, st), P, T⟩ from rfl,
    sim_run_RANCH2 i ⟨(0, st), P, T⟩ hmin]
  exact scanLeftSep_head_pos hbase hns hi

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryRoundPhases

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryRoundPhases.rendShift_head_ge
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryRoundPhases.masterSHA_leftSafe
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryRoundPhases.scanLeftSep_head_pos
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryRoundPhases.masterRANCH1_leftSafe
