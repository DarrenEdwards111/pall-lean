import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitHeadFamily

/-!
# Cook–Levin M2 emitter — THE TAPE-COPY FAMILY, ALL TIMES, ONE MACHINE

The two-source families need no triangle: each grand round is ONE stale-bound pass (the bound
mirror is armed at `P+1` once and never moves), a live re-arm, and a `t`-mirror increment.
The increment cannot come from `interGrandMachine` (its resets would kill the constant stale
bound), so this file adds the last support pass:

* **`incT6Machine`** — increment the `t`-mirror ONLY (`jT C1 t ↦ jT C1 (t+1)`), the counters
  and the bound crossed verbatim, halting right after the four-write.

* **`cellCopyRowBody`** — the three-source port of `cellCopyBody`: per inner round `k` it
  emits BOTH clauses of `cellCopyClause t k` (the `t+1` coordinate via the offset splice
  `sA1 = bitsI3 [true] ++ sA`).  `rep_cellFamily_run` wraps `B` rounds:
  `cellEmitOut_tapeFamily` reads the stream as `encodeClause'` of the tableau's `tapeFamily`
  — clause-for-clause, IN ORDER: this family needs no permutation.
  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitCellFamily

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinCNFEncode
open PallLean.Paper93.DeepMath.PathB.CookLevinVarIndex
open PallLean.Paper93.DeepMath.PathB.CookLevinTransition
open PallLean.Paper93.DeepMath.PathB.CookLevinAssembly
open PallLean.Paper93.DeepMath.PathB.CookLevinEmit (encodeNat)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSplice
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRange
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitTemplates
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitNestVar
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg3
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitFamilyBodies
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSeq
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRep
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRepP
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitPairT
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitInterRow
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitInterGrand
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitTriangleHead
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSnoc6
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitHeadFamily

/-! ## The `t`-mirror incrementer

`Fin 15 × Bool`: `0/1`, `2/3` skip the counters, `4/5` walk + `6` hop + `7/8` pad-cross the
bound, `9/10` walk the `t`-mirror, `11,12,13` complete the four-write increment, `14` halt. -/

def incT6Machine : Machine where
  State := Fin 15 × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, false)
  halt := fun s => decide (s.1 = 14)
  δ := fun s b =>
    if s.1 = 0 then ((1, b), none, 1)
    else if s.1 = 1 then
      (if s.2 then ((0, s.2), none, 1)
       else (if b then ((2, s.2), none, 1) else ((14, s.2), none, 2)))
    else if s.1 = 2 then ((3, b), none, 1)
    else if s.1 = 3 then
      (if s.2 then ((2, s.2), none, 1)
       else (if b then ((4, s.2), none, 1) else ((14, s.2), none, 2)))
    else if s.1 = 4 then
      (if b then ((5, b), none, 1) else ((6, s.2), none, 1))
    else if s.1 = 5 then ((4, s.2), none, 1)
    else if s.1 = 6 then ((7, s.2), none, 1)
    else if s.1 = 7 then ((8, b), none, 1)
    else if s.1 = 8 then
      (if s.2 then ((9, false), none, 0)
       else (if b then ((9, false), none, 0) else ((7, s.2), none, 1)))
    else if s.1 = 9 then
      (if b then ((10, b), none, 1) else ((11, s.2), some true, 1))
    else if s.1 = 10 then ((9, s.2), none, 1)
    else if s.1 = 11 then ((12, s.2), some true, 1)
    else if s.1 = 12 then ((13, s.2), some false, 1)
    else if s.1 = 13 then ((14, false), some true, 2)
    else ((s.1, s.2), none, 2)
  accept := fun _ => false

theorem init_ic (t : List Bool) : init incT6Machine t = ⟨(0, false), 0, t⟩ := rfl

section StepsIC
variable {s : Bool} {p : ℕ} {T : List Bool}

theorem ic_skipW (h1 : T.getD p false = true) :
    run incT6Machine 2 ⟨(0, s), p, T⟩ = ⟨(0, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step incT6Machine ⟨(0, s), p, T⟩ = ⟨(1, T.getD p false), p + 1, T⟩ := by
    simp only [step, incT6Machine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, incT6Machine, moveHead]; rfl

theorem ic_crossW (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run incT6Machine 2 ⟨(0, s), p, T⟩ = ⟨(2, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step incT6Machine ⟨(0, s), p, T⟩ = ⟨(1, T.getD p false), p + 1, T⟩ := by
    simp only [step, incT6Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, incT6Machine, moveHead, h2]

theorem ic_skipR (h1 : T.getD p false = true) :
    run incT6Machine 2 ⟨(2, s), p, T⟩ = ⟨(2, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step incT6Machine ⟨(2, s), p, T⟩ = ⟨(3, T.getD p false), p + 1, T⟩ := by
    simp only [step, incT6Machine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, incT6Machine, moveHead]; rfl

theorem ic_crossR (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run incT6Machine 2 ⟨(2, s), p, T⟩ = ⟨(4, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step incT6Machine ⟨(2, s), p, T⟩ = ⟨(3, T.getD p false), p + 1, T⟩ := by
    simp only [step, incT6Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, incT6Machine, moveHead, h2]

theorem ic_walkB (h1 : T.getD p false = true) :
    run incT6Machine 2 ⟨(4, s), p, T⟩ = ⟨(4, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step incT6Machine ⟨(4, s), p, T⟩ = ⟨(5, true), p + 1, T⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, incT6Machine, moveHead, h1']
  rw [e0]
  simp only [step, incT6Machine, moveHead]; rfl

theorem ic_hopB (h1 : T.getD p false = false) :
    run incT6Machine 2 ⟨(4, s), p, T⟩ = ⟨(7, s), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step incT6Machine ⟨(4, s), p, T⟩ = ⟨(6, s), p + 1, T⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, incT6Machine, moveHead, h1']
  rw [e0]
  simp only [step, incT6Machine, moveHead]; rfl

theorem ic_padB (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = false) :
    run incT6Machine 2 ⟨(7, s), p, T⟩ = ⟨(7, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step incT6Machine ⟨(7, s), p, T⟩ = ⟨(8, T.getD p false), p + 1, T⟩ := by
    simp only [step, incT6Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, incT6Machine, moveHead, h2]

theorem ic_padB_boundT (h1 : T.getD p false = true) :
    run incT6Machine 2 ⟨(7, s), p, T⟩ = ⟨(9, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step incT6Machine ⟨(7, s), p, T⟩ = ⟨(8, T.getD p false), p + 1, T⟩ := by
    simp only [step, incT6Machine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, incT6Machine, moveHead]; rfl

theorem ic_padB_boundM (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run incT6Machine 2 ⟨(7, s), p, T⟩ = ⟨(9, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step incT6Machine ⟨(7, s), p, T⟩ = ⟨(8, T.getD p false), p + 1, T⟩ := by
    simp only [step, incT6Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, incT6Machine, moveHead, h2]

theorem ic_padB_bound
    (h : T.getD p false = true ∨ (T.getD p false = false ∧ T.getD (p + 1) false = true)) :
    run incT6Machine 2 ⟨(7, s), p, T⟩ = ⟨(9, false), p, T⟩ := by
  rcases h with h1 | ⟨h1, h2⟩
  · exact ic_padB_boundT h1
  · exact ic_padB_boundM h1 h2

theorem ic_walkT (h1 : T.getD p false = true) :
    run incT6Machine 2 ⟨(9, s), p, T⟩ = ⟨(9, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step incT6Machine ⟨(9, s), p, T⟩ = ⟨(10, true), p + 1, T⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, incT6Machine, moveHead, h1']
  rw [e0]
  simp only [step, incT6Machine, moveHead]; rfl

/-- The four-write increment at the `t`-mirror's marker; the machine halts in place. -/
theorem ic_four_incrT (h1 : T.getD p false = false) :
    run incT6Machine 4 ⟨(9, s), p, T⟩
      = ⟨(14, false), p + 3, writeAt (writeAt (writeAt (writeAt T p true)
          (p + 1) true) (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e0 : step incT6Machine ⟨(9, s), p, T⟩ = ⟨(11, s), p + 1, writeAt T p true⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, incT6Machine, moveHead, h1']
  have e1 : ∀ p' T', step incT6Machine ⟨(11, s), p', T'⟩
      = ⟨(12, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, incT6Machine, moveHead]; rfl
  have e2 : ∀ p' T', step incT6Machine ⟨(12, s), p', T'⟩
      = ⟨(13, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, incT6Machine, moveHead]; rfl
  have e3 : ∀ p' T', step incT6Machine ⟨(13, s), p', T'⟩
      = ⟨(14, false), p', writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, incT6Machine, moveHead]; rfl
  rw [e0, e1, e2, e3]

end StepsIC

theorem ic_skipWs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run incT6Machine (2 * k) ⟨(0, s), q, T⟩
      = ⟨(0, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), ic_skipW (h k (by omega))]
    rfl

theorem ic_skipRs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run incT6Machine (2 * k) ⟨(2, s), q, T⟩
      = ⟨(2, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), ic_skipR (h k (by omega))]
    rfl

theorem ic_walkBs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run incT6Machine (2 * k) ⟨(4, s), q, T⟩
      = ⟨(4, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), ic_walkB (h k (by omega))]
    rfl

theorem ic_padBs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = false
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run incT6Machine (2 * k) ⟨(7, s), q, T⟩
      = ⟨(7, if k = 0 then s else false), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), ic_padB hk.1 hk.2]
    rfl

theorem ic_walkTs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run incT6Machine (2 * k) ⟨(9, s), q, T⟩
      = ⟨(9, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), ic_walkT (h k (by omega))]
    rfl

/-- **The `t`-mirror incrementer run**: `jT C1 t ↦ jT C1 (t+1)`, all else verbatim. -/
theorem incT6_run (G g : ℕ) (hg : g ≤ G) (P2 r : ℕ) (hr : r ≤ P2) (CB C1 v1 t : ℕ)
    (hv1 : v1 ≤ CB) (ht : t < C1) (E : List Bool) :
    run incT6Machine (2 * G + 2 * P2 + 2 * CB + 2 * t + 12)
      (init incT6Machine (cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t ++ E)))))
      = ⟨(14, false), 2 * G + 2 * P2 + 2 * CB + 2 * t + 9,
          cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 (t + 1) ++ E)))⟩ := by
  have hW : (cntT G g).length = 2 * G + 2 := cntT_length G g hg
  have hQ : (cntT P2 r).length = 2 * P2 + 2 := cntT_length P2 r hr
  have hR : (jT CB v1).length = 2 * CB + 2 := jT_length CB v1 hv1
  have f0 := ic_skipWs (cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t ++ E)))) 0 G
    false (fun i hi => by simpa using cntE_lo G g _ i hg hi)
  simp only [Nat.zero_add] at f0
  have f0' := ic_crossW (s := if G = 0 then false else true) (p := 2 * G)
    (T := cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t ++ E))))
    (cntE_cm_lo G g _ hg) (cntE_cm_hi G g _ hg)
  have f1 := ic_skipRs (cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t ++ E))))
    (2 * G + 2) P2 false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * i = 2 * G + 2 + (2 * i) from rfl]
      exact liftJ _ _ hW (cntE_lo P2 r _ i hr hi))
  have f1' := ic_crossR (s := if P2 = 0 then false else true) (p := 2 * G + 2 + 2 * P2)
    (T := cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t ++ E))))
    (by rw [show 2 * G + 2 + 2 * P2 = 2 * G + 2 + (2 * P2) from rfl]
        exact liftJ _ _ hW (cntE_cm_lo P2 r _ hr))
    (by rw [show 2 * G + 2 + 2 * P2 + 1 = 2 * G + 2 + (2 * P2 + 1) from by omega]
        exact liftJ _ _ hW (cntE_cm_hi P2 r _ hr))
  have f2 := ic_walkBs (cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t ++ E))))
    (2 * G + 2 + 2 * P2 + 2) v1 false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * i = 2 * G + 2 + (2 * P2 + 2 + 2 * i)
          from by omega, ← jsT_zero CB v1]
      exact liftJ2 _ _ _ hW hQ
        (jsE_data CB v1 0 _ (2 * i) (by omega) (by omega) (by omega)))
  have f2' := ic_hopB (s := if v1 = 0 then false else true)
    (p := 2 * G + 2 + 2 * P2 + 2 + 2 * v1)
    (T := cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t ++ E))))
    (by rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * v1 = 2 * G + 2 + (2 * P2 + 2 + 2 * v1)
          from by omega, ← jsT_zero CB v1]
        exact liftJ2 _ _ _ hW hQ (jsE_m_lo CB v1 0 _ (by omega)))
  have f3 := ic_padBs (cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t ++ E))))
    (2 * G + 2 + 2 * P2 + 2 + 2 * v1 + 2) (CB - v1) (if v1 = 0 then false else true)
    (fun i hi => ⟨by
      rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * v1 + 2 + 2 * i
          = 2 * G + 2 + (2 * P2 + 2 + (2 * v1 + 2 + 2 * i)) from by omega,
        ← jsT_zero CB v1]
      exact liftJ2 _ _ _ hW hQ (jsE_pad CB v1 0 _ (2 * v1 + 2 + 2 * i)
        (by omega) hv1 (by omega) (by omega)), by
      rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * v1 + 2 + 2 * i + 1
          = 2 * G + 2 + (2 * P2 + 2 + (2 * v1 + 2 + 2 * i + 1)) from by omega,
        ← jsT_zero CB v1]
      exact liftJ2 _ _ _ hW hQ (jsE_pad CB v1 0 _ (2 * v1 + 2 + 2 * i + 1)
        (by omega) hv1 (by omega) (by omega))⟩)
  rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * v1 + 2 + 2 * (CB - v1)
      = 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 from by omega] at f3
  have f3' := ic_padB_bound
    (s := if CB - v1 = 0 then (if v1 = 0 then false else true) else false)
    (p := 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2)
    (T := cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t ++ E))))
    (by rcases Nat.eq_zero_or_pos t with h0 | h0
        · right
          constructor
          · rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2
                = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + 2 * t)) from by omega,
              ← jsT_zero C1 t]
            exact liftJ3 _ _ _ _ hW hQ hR (jsE_m_lo C1 t 0 _ (by omega))
          · rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 1
                = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * t + 1))) from by omega,
              ← jsT_zero C1 t]
            exact liftJ3 _ _ _ _ hW hQ hR (jsE_m_hi C1 t 0 _ (by omega))
        · left
          rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2
              = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2)) from by omega, ← jsT_zero C1 t]
          exact liftJ3 _ _ _ _ hW hQ hR
            (jsE_data C1 t 0 _ 0 (by omega) (by omega) (by omega)))
  have f4 := ic_walkTs (cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t ++ E))))
    (2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2) t false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * i
          = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + 2 * i)) from by omega,
        ← jsT_zero C1 t]
      exact liftJ3 _ _ _ _ hW hQ hR
        (jsE_data C1 t 0 _ (2 * i) (by omega) (by omega) (by omega)))
  have f5 := ic_four_incrT (s := if t = 0 then false else true)
    (p := 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * t)
    (T := cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t ++ E))))
    (by rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * t
          = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + 2 * t)) from by omega,
        ← jsT_zero C1 t]
        exact liftJ3 _ _ _ _ hW hQ hR (jsE_m_lo C1 t 0 _ (by omega)))
  rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * t
      = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + 2 * t)) from by omega,
    W4_append_right3 (cntT G g) (cntT P2 r) (jT CB v1) (jT C1 t ++ E) (2 * G + 2)
      (2 * P2 + 2) (2 * CB + 2) (2 * t) true true false true hW hQ hR
      (by rw [List.length_append, jT_length C1 t (by omega)]; omega),
    jT_incr C1 t _ ht] at f5
  rw [init_ic,
    show 2 * G + 2 * P2 + 2 * CB + 2 * t + 12
      = 2 * G + (2 + (2 * P2 + (2 + (2 * v1 + (2 + (2 * (CB - v1) + (2
          + (2 * t + 4)))))))) from by omega,
    run_add, f0, run_add, f0', run_add, f1, run_add, f1', run_add, f2, run_add, f2',
    run_add, f3, run_add, f3', run_add, f4,
    show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * t
      = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + 2 * t)) from by omega,
    f5,
    show 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + 2 * t)) + 3
      = 2 * G + 2 * P2 + 2 * CB + 2 * t + 9 from by omega]

theorem incT6_halt : incT6Machine.halt ((14 : Fin 15), false) = true := rfl

/-! ## The three-source tape-copy body -/

/-- The offset splice: `encodeNat (a + 1)`. -/
def sA1 : List L3Instr := bitsI3 [true] ++ sA

def cellCopyRowFstBody : List L3Instr :=
  bitsI3 [true, true, true, false] ++ (sA ++ (sJ ++ (bitsI3 [true, false, true]
    ++ (sA1 ++ (sJ ++ (bitsI3 [false, false] ++ (sA ++ (sJ
      ++ bitsI3 [false, true]))))))))

def cellCopyRowSndBody : List L3Instr :=
  bitsI3 [true, true, true, false] ++ (sA ++ (sJ ++ (bitsI3 [true, false, true]
    ++ (sA1 ++ (sJ ++ (bitsI3 [false, true] ++ (sA ++ (sJ
      ++ bitsI3 [false, false]))))))))

def cellCopyRowBody : List L3Instr := cellCopyRowFstBody ++ cellCopyRowSndBody

theorem cellCopyRowFst_prog3Out (t c k : ℕ) :
    prog3Out cellCopyRowFstBody t c k
      = encodeClause' [(headVar t k, true), (cellVar (t + 1) k, false),
          (cellVar t k, true)] := by
  rw [encodeClause'_cellCopy_fst, cellCopyRowFstBody, sA1]
  simp only [prog3Out_append, prog3Out_bits, prog3Out_sA, prog3Out_sJ]
  simp [encodeNat, List.replicate_succ, List.append_assoc]

theorem cellCopyRowSnd_prog3Out (t c k : ℕ) :
    prog3Out cellCopyRowSndBody t c k
      = encodeClause' [(headVar t k, true), (cellVar (t + 1) k, true),
          (cellVar t k, false)] := by
  rw [encodeClause'_cellCopy_snd, cellCopyRowSndBody, sA1]
  simp only [prog3Out_append, prog3Out_bits, prog3Out_sA, prog3Out_sJ]
  simp [encodeNat, List.replicate_succ, List.append_assoc]

/-- One round emits BOTH clauses of `cellCopyClause t k`. -/
theorem cellCopyRow_prog3Out (t c k : ℕ) :
    prog3Out cellCopyRowBody t c k
      = ((cellCopyClause t k).map encodeClause').flatten := by
  rw [cellCopyRowBody, prog3Out_append, cellCopyRowFst_prog3Out, cellCopyRowSnd_prog3Out,
    cellCopyClause_members]
  simp

/-- The tape-copy block at time `t` factors through the loop denotation. -/
theorem cellCopyRow_split (t c P : ℕ) :
    loop3Out cellCopyRowBody t c (P + 1)
      = ((List.range (P + 1)).map (fun p =>
          ((cellCopyClause t p).map encodeClause').flatten)).flatten := by
  rw [loop3Out_eq_flatten]
  exact congrArg List.flatten (List.map_congr_left (fun p _ => cellCopyRow_prog3Out t c p))

/-! ## The stream IS the tableau's tape family — no permutation -/

theorem flatten_map_flatten {α β : Type} (f : α → List β) : ∀ (L : List (List α)),
    ((L.flatten).map f).flatten = (L.map (fun l => (l.map f).flatten)).flatten
  | [] => rfl
  | l :: L => by
    rw [List.flatten_cons, List.map_append, List.flatten_append,
      flatten_map_flatten f L, List.map_cons, List.flatten_cons]

/-- The accumulated tape-family stream. -/
def cellEmitOut (P : ℕ) : ℕ → List Bool
  | 0 => []
  | t + 1 => cellEmitOut P t ++ loop3Out cellCopyRowBody t 1 (P + 1)

/-- **The stream equals `encodeClause'` of the tableau's `tapeFamily` — clause-for-clause,
in order.** -/
theorem tapeFamily_succ (P B : ℕ) :
    tapeFamily P (B + 1)
      = tapeFamily P B
        ++ bigAnd ((List.range (P + 1)).map (fun p => cellCopyClause B p)) := by
  rw [tapeFamily, tapeFamily, bigAnd, bigAnd, List.range_succ (n := B), List.map_append,
    List.flatten_append]
  simp [bigAnd]

theorem cellEmitOut_tapeFamily (P : ℕ) : ∀ B,
    cellEmitOut P B = ((tapeFamily P B).map encodeClause').flatten
  | 0 => by simp [cellEmitOut, tapeFamily, bigAnd]
  | B + 1 => by
    rw [show cellEmitOut P (B + 1)
        = cellEmitOut P B ++ loop3Out cellCopyRowBody B 1 (P + 1) from rfl,
      cellEmitOut_tapeFamily P B, tapeFamily_succ, List.map_append, List.flatten_append]
    congr 1
    rw [cellCopyRow_split, bigAnd, flatten_map_flatten, List.map_map]
    rfl

/-! ## THE TAPE-COPY ROUND AND ITS GRAND LOOP -/

/-- The per-round machine: the stale-bound tape-copy pass, the live re-arm, the `t`-mirror
increment. -/
def cellRoundMachine : Machine :=
  seqMachine (seqMachine (pairTMachine cellCopyRowBody) rearm6Machine) incT6Machine

set_option maxHeartbeats 1600000 in
/-- **One tape-copy round** — the `rep_run` hypothesis shape. -/
theorem cellRound_run (B P CB C1 C2 NV t : ℕ) (hP : 0 < P) (hCB : P < CB) (hC2 : P < C2)
    (hNV : P < NV) (ht : t < B) (hBC1 : B ≤ C1) (out : List Bool) :
    run cellRoundMachine
      (((pairTClock cellCopyRowBody B P CB C1 C2 NV t 1 (P + 1) out.length + 1
        + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * (P + 1) + 18)) + 1
        + (2 * B + 2 * P + 2 * CB + 2 * t + 12)))
      (init cellRoundMachine (cntT B (t + 1) ++ (unaryD P ++ (jT CB (P + 1) ++ (jT C1 t
        ++ (jT C2 1 ++ (jT NV 0 ++ encodeD out)))))))
      = ⟨Sum.inr (14, false), 2 * B + 2 * P + 2 * CB + 2 * t + 9,
          cntT B (t + 1) ++ (unaryD P ++ (jT CB (P + 1) ++ (jT C1 (t + 1) ++ (jT C2 1
            ++ (jT NV 0 ++ encodeD (out ++ loop3Out cellCopyRowBody t 1 (P + 1)))))))⟩ := by
  have hCC := pairT_run cellCopyRowBody B (t + 1) (by omega) P 0 (by omega) CB C1 C2 NV
    (P + 1) t 1 (by omega) (by omega) (by omega) (by omega) out
  rw [cntT_zero P] at hCC
  have hR := rearm6_run B (t + 1) (by omega) P 0 (by omega) CB C1 C2 NV (P + 1) t 1
    (P + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
    (encodeD (out ++ loop3Out cellCopyRowBody t 1 (P + 1)))
  rw [cntT_zero P] at hR
  have hI := incT6_run B (t + 1) (by omega) P 0 (by omega) CB C1 (P + 1) t (by omega)
    (by omega)
    (jT C2 1 ++ (jT NV 0 ++ encodeD (out ++ loop3Out cellCopyRowBody t 1 (P + 1))))
  rw [cntT_zero P] at hI
  have h1 := seq_run (pairTMachine cellCopyRowBody) rearm6Machine _ _ _ _ _ _ _ _ _
    hCC rfl hR rearm6_halt
  have h2 := seq_run _ incT6Machine _ _ _ _ _ _ _ _ _ h1
    (seq_halt_final _ rearm6Machine _ rearm6_halt) hI incT6_halt
  exact h2

theorem cellRound_halt : cellRoundMachine.halt (Sum.inr (14, false)) = true :=
  seq_halt_final _ incT6Machine _ incT6_halt

set_option maxHeartbeats 1600000 in
/-- **THE TAPE-COPY FAMILY STREAM**: `B` rounds — the output is `encodeClause'` of the
tableau's `tapeFamily P B`, clause-for-clause, in order (`cellEmitOut_tapeFamily`).  One
machine, self-halting. -/
theorem rep_cellFamily_run (B P CB C1 C2 NV : ℕ) (hP : 0 < P) (hCB : P < CB)
    (hC2 : P < C2) (hNV : P < NV) (hBC1 : B ≤ C1) (out : List Bool) :
    run (repMachine cellRoundMachine)
      (repRounds (fun t =>
        ((pairTClock cellCopyRowBody B P CB C1 C2 NV t 1 (P + 1)
            (out ++ cellEmitOut P t).length + 1
          + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * (P + 1) + 18)) + 1
          + (2 * B + 2 * P + 2 * CB + 2 * t + 12))) B + (4 * B + 4))
      (init (repMachine cellRoundMachine)
        (cntT B 0 ++ (unaryD P ++ (jT CB (P + 1) ++ (jT C1 0 ++ (jT C2 1 ++ (jT NV 0
          ++ encodeD out)))))))
      = ⟨Sum.inl (4, false), 2 * B + 1,
          unaryD B ++ (unaryD P ++ (jT CB (P + 1) ++ (jT C1 B ++ (jT C2 1 ++ (jT NV 0
            ++ encodeD (out ++ cellEmitOut P B))))))⟩ := by
  have h := rep_run cellRoundMachine B
    (fun t => unaryD P ++ (jT CB (P + 1) ++ (jT C1 t ++ (jT C2 1 ++ (jT NV 0
      ++ encodeD (out ++ cellEmitOut P t))))))
    (fun t =>
      ((pairTClock cellCopyRowBody B P CB C1 C2 NV t 1 (P + 1)
          (out ++ cellEmitOut P t).length + 1
        + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * (P + 1) + 18)) + 1
        + (2 * B + 2 * P + 2 * CB + 2 * t + 12)))
    (fun _ => Sum.inr (14, false))
    (fun t => 2 * B + 2 * P + 2 * CB + 2 * t + 9)
    (fun t ht => by
      constructor
      · have hrd := cellRound_run B P CB C1 C2 NV t hP hCB hC2 hNV ht hBC1
          (out ++ cellEmitOut P t)
        rw [show (out ++ cellEmitOut P t) ++ loop3Out cellCopyRowBody t 1 (P + 1)
            = out ++ cellEmitOut P (t + 1) from by rw [List.append_assoc]; rfl] at hrd
        exact hrd
      · exact cellRound_halt)
  simp only [show cellEmitOut P 0 = [] from rfl, List.append_nil] at h
  exact h

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitCellFamily
