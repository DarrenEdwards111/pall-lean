import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitQcPass

/-!
# Cook–Levin M2 emitter — E6 step 2: THE t-MIRROR RESET (`rst4Machine`)

The inter-family interstitial: between grand loops the chain must return the `t`-mirror from
`B` to `0` (`jT C1 t ↦ jT C1 0`) with every other region verbatim.  The machine is `rearm6`
retargeted two regions earlier: cross the two counters and the bound mirror, then run the
zeroing head-pair + loop on the `t`-mirror (the `zeroT` track), never touching anything beyond
its fence.  `Fin 15 × Bool`; one pass, clock `2G + 2P2 + 2CB + 2t + 10`.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitRst4

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitAppendBlock
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCompare
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSplice
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRange
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitNestVar
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg3
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRearm (W2_append_right3)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitInterRow

/-! ## The machine

`0/1`, `2/3` skip the counters; `4/5` walk + `6` hop + `7/8` pad-cross the bound mirror; the
boundary event backs onto the `t`-mirror's first cell; `9/10` write the new fence `[F,T]`;
`11/12` zero the old content; `13` the closing write; `14` halt. -/

def rst4Machine : Machine where
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
    else if s.1 = 9 then ((10, s.2), some false, 1)
    else if s.1 = 10 then ((11, s.2), some true, 1)
    else if s.1 = 11 then
      (if b then ((12, b), some false, 1) else ((13, b), some false, 1))
    else if s.1 = 12 then ((11, s.2), some false, 1)
    else if s.1 = 13 then ((14, s.2), some false, 2)
    else ((s.1, s.2), none, 2)
  accept := fun _ => false

theorem init_rst4 (t : List Bool) : init rst4Machine t = ⟨(0, false), 0, t⟩ := rfl

theorem rst4_halt : rst4Machine.halt ((14 : Fin 15), false) = true := rfl

/-! ## Step layer -/

section StepsRst4
variable {s : Bool} {p : ℕ} {T : List Bool}

theorem rst4_skipW (h1 : T.getD p false = true) :
    run rst4Machine 2 ⟨(0, s), p, T⟩ = ⟨(0, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rst4Machine ⟨(0, s), p, T⟩ = ⟨(1, T.getD p false), p + 1, T⟩ := by
    simp only [step, rst4Machine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, rst4Machine, moveHead]; rfl

theorem rst4_crossW (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run rst4Machine 2 ⟨(0, s), p, T⟩ = ⟨(2, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rst4Machine ⟨(0, s), p, T⟩ = ⟨(1, T.getD p false), p + 1, T⟩ := by
    simp only [step, rst4Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, rst4Machine, moveHead, h2]

theorem rst4_skipR (h1 : T.getD p false = true) :
    run rst4Machine 2 ⟨(2, s), p, T⟩ = ⟨(2, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rst4Machine ⟨(2, s), p, T⟩ = ⟨(3, T.getD p false), p + 1, T⟩ := by
    simp only [step, rst4Machine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, rst4Machine, moveHead]; rfl

theorem rst4_crossR (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run rst4Machine 2 ⟨(2, s), p, T⟩ = ⟨(4, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rst4Machine ⟨(2, s), p, T⟩ = ⟨(3, T.getD p false), p + 1, T⟩ := by
    simp only [step, rst4Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, rst4Machine, moveHead, h2]

theorem rst4_walkB (h1 : T.getD p false = true) :
    run rst4Machine 2 ⟨(4, s), p, T⟩ = ⟨(4, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rst4Machine ⟨(4, s), p, T⟩ = ⟨(5, true), p + 1, T⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, rst4Machine, moveHead, h1']
  rw [e0]
  simp only [step, rst4Machine, moveHead]; rfl

theorem rst4_hopB (h1 : T.getD p false = false) :
    run rst4Machine 2 ⟨(4, s), p, T⟩ = ⟨(7, s), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rst4Machine ⟨(4, s), p, T⟩ = ⟨(6, s), p + 1, T⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, rst4Machine, moveHead, h1']
  rw [e0]
  simp only [step, rst4Machine, moveHead]; rfl

theorem rst4_padB (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = false) :
    run rst4Machine 2 ⟨(7, s), p, T⟩ = ⟨(7, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rst4Machine ⟨(7, s), p, T⟩ = ⟨(8, T.getD p false), p + 1, T⟩ := by
    simp only [step, rst4Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, rst4Machine, moveHead, h2]

theorem rst4_padB_boundT (h1 : T.getD p false = true) :
    run rst4Machine 2 ⟨(7, s), p, T⟩ = ⟨(9, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rst4Machine ⟨(7, s), p, T⟩ = ⟨(8, T.getD p false), p + 1, T⟩ := by
    simp only [step, rst4Machine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, rst4Machine, moveHead]; rfl

theorem rst4_two_head {s' : Bool} :
    run rst4Machine 2 ⟨(9, s'), p, T⟩
      = ⟨(11, s'), p + 2, writeAt (writeAt T p false) (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e4 : step rst4Machine ⟨(9, s'), p, T⟩
      = ⟨(10, s'), p + 1, writeAt T p false⟩ := by
    simp only [step, rst4Machine, moveHead]; rfl
  have e5 : ∀ p' T', step rst4Machine ⟨(10, s'), p', T'⟩
      = ⟨(11, s'), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, rst4Machine, moveHead]; rfl
  rw [e4, e5]

theorem rst4_zero_step (h : T.getD p false = true) :
    run rst4Machine 2 ⟨(11, s), p, T⟩
      = ⟨(11, true), p + 2, writeAt (writeAt T p false) (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e6 : step rst4Machine ⟨(11, s), p, T⟩
      = ⟨(12, true), p + 1, writeAt T p false⟩ := by
    have h' := h
    rw [List.getD_eq_getElem?_getD] at h'
    simp [step, rst4Machine, moveHead, h']
  rw [e6]
  simp only [step, rst4Machine, moveHead]; rfl

theorem rst4_zero_last (h : T.getD p false = false) :
    run rst4Machine 2 ⟨(11, s), p, T⟩
      = ⟨(14, false), p + 1, writeAt (writeAt T p false) (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e6 : step rst4Machine ⟨(11, s), p, T⟩
      = ⟨(13, false), p + 1, writeAt T p false⟩ := by
    have h' := h
    rw [List.getD_eq_getElem?_getD] at h'
    simp [step, rst4Machine, moveHead, h']
  rw [e6]
  simp only [step, rst4Machine, moveHead]; rfl

end StepsRst4

/-! ## The iterated walks -/

theorem rst4_skipWs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run rst4Machine (2 * k) ⟨(0, s), q, T⟩
      = ⟨(0, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), rst4_skipW (h k (by omega))]
    rfl

theorem rst4_skipRs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run rst4Machine (2 * k) ⟨(2, s), q, T⟩
      = ⟨(2, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), rst4_skipR (h k (by omega))]
    rfl

theorem rst4_walkBs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run rst4Machine (2 * k) ⟨(4, s), q, T⟩
      = ⟨(4, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), rst4_walkB (h k (by omega))]
    rfl

theorem rst4_padBs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = false
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run rst4Machine (2 * k) ⟨(7, s), q, T⟩
      = ⟨(7, if k = 0 then s else false), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), rst4_padB hk.1 hk.2]
    rfl

/-- The zeroing walk (evolving `zeroT`, three prefixes). -/
theorem rst4_zeros (W Q R : List Bool) (G P2 CB P : ℕ) (E : List Bool)
    (hW : W.length = 2 * G + 2) (hQ : Q.length = 2 * P2 + 2) (hR : R.length = 2 * CB + 2)
    (hP : 0 < P) (s : Bool) (m : ℕ) (hm : m ≤ P - 1) :
    run rst4Machine (2 * m)
      ⟨(11, s), 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2,
        W ++ (Q ++ (R ++ (zeroT P 0 ++ E)))⟩
      = ⟨(11, if m = 0 then s else true),
          2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 + 2 * m,
          W ++ (Q ++ (R ++ (zeroT P m ++ E)))⟩ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hlo : (W ++ (Q ++ (R ++ (zeroT P m ++ E)))).getD
        (2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 + 2 * m) false = true := by
      rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 + 2 * m
          = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + 2 * (m + 1))) from by omega]
      exact liftJ3 _ _ _ _ hW hQ hR (zeroE_data_lo P m E (by omega))
    have hw : writeAt (writeAt (W ++ (Q ++ (R ++ (zeroT P m ++ E))))
        (2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 + 2 * m) false)
        (2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 + 2 * m + 1) false
        = W ++ (Q ++ (R ++ (zeroT P (m + 1) ++ E))) := by
      rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 + 2 * m
          = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + 2 * (m + 1))) from by omega,
        W2_append_right3 W Q R _ (2 * G + 2) (2 * P2 + 2) (2 * CB + 2)
          (2 * (m + 1)) false false hW hQ hR
          (by rw [List.length_append, zeroT_length P m (by omega) hP]; omega),
        zeroT_step P m E (by omega)]
    rw [show 2 * (m + 1) = 2 * m + 2 from by ring, run_add, ih (by omega),
      rst4_zero_step hlo, hw]
    rfl

/-! ## THE t-MIRROR RESET RUN -/

set_option maxHeartbeats 800000 in
/-- **The `t`-mirror reset**: one pass, `jT C1 t ↦ jT C1 0` (`0 < t`), every other region
verbatim — the inter-family interstitial of the E6 master chain. -/
theorem rst4_run (G g : ℕ) (hg : g ≤ G) (P2 r : ℕ) (hr : r ≤ P2) (CB v1 C1 t : ℕ)
    (hv1 : v1 ≤ CB) (ht : t ≤ C1) (ht0 : 0 < t) (E : List Bool) :
    run rst4Machine (2 * G + 2 * P2 + 2 * CB + 2 * t + 10)
      (init rst4Machine (cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t ++ E)))))
      = ⟨(14, false), 2 * G + 2 * P2 + 2 * CB + 2 * t + 7,
          cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 0 ++ E)))⟩ := by
  have hW : (cntT G g).length = 2 * G + 2 := cntT_length G g hg
  have hQ : (cntT P2 r).length = 2 * P2 + 2 := cntT_length P2 r hr
  have hR : (jT CB v1).length = 2 * CB + 2 := jT_length CB v1 hv1
  have f0 := rst4_skipWs (cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t ++ E))))
    0 G false (fun i hi => by simpa using cntE_lo G g _ i hg hi)
  simp only [Nat.zero_add] at f0
  have f0' := rst4_crossW (s := if G = 0 then false else true) (p := 2 * G)
    (T := cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t ++ E))))
    (cntE_cm_lo G g _ hg) (cntE_cm_hi G g _ hg)
  have f1 := rst4_skipRs (cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t ++ E))))
    (2 * G + 2) P2 false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * i = 2 * G + 2 + (2 * i) from rfl]
      exact liftJ _ _ hW (cntE_lo P2 r _ i hr hi))
  have f1' := rst4_crossR (s := if P2 = 0 then false else true) (p := 2 * G + 2 + 2 * P2)
    (T := cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t ++ E))))
    (by rw [show 2 * G + 2 + 2 * P2 = 2 * G + 2 + (2 * P2) from rfl]
        exact liftJ _ _ hW (cntE_cm_lo P2 r _ hr))
    (by rw [show 2 * G + 2 + 2 * P2 + 1 = 2 * G + 2 + (2 * P2 + 1) from by omega]
        exact liftJ _ _ hW (cntE_cm_hi P2 r _ hr))
  have f2 := rst4_walkBs (cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t ++ E))))
    (2 * G + 2 + 2 * P2 + 2) v1 false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * i = 2 * G + 2 + (2 * P2 + 2 + 2 * i)
          from by omega, ← jsT_zero CB v1]
      exact liftJ2 _ _ _ hW hQ
        (jsE_data CB v1 0 _ (2 * i) (by omega) (by omega) (by omega)))
  have f2' := rst4_hopB (s := if v1 = 0 then false else true)
    (p := 2 * G + 2 + 2 * P2 + 2 + 2 * v1)
    (T := cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t ++ E))))
    (by rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * v1 = 2 * G + 2 + (2 * P2 + 2 + 2 * v1)
          from by omega, ← jsT_zero CB v1]
        exact liftJ2 _ _ _ hW hQ (jsE_m_lo CB v1 0 _ (by omega)))
  have f3 := rst4_padBs (cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t ++ E))))
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
  have f3' := rst4_padB_boundT
    (s := if CB - v1 = 0 then (if v1 = 0 then false else true) else false)
    (p := 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2)
    (T := cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t ++ E))))
    (by rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2
          = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + 0)) from by omega,
        ← jsT_zero C1 t]
        exact liftJ3 _ _ _ _ hW hQ hR
          (jsE_data C1 t 0 _ 0 (by omega) (by omega) (by omega)))
  have f8 := rst4_two_head (s' := false)
    (p := 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2)
    (T := cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t ++ E))))
  have hw8 : writeAt (writeAt (cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t ++ E))))
      (2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2) false)
      (2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 1) true
      = cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (zeroT t 0
          ++ (List.replicate (2 * (C1 - t)) false ++ E)))) := by
    rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2
        = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + 0)) from by omega,
      W2_append_right3 (cntT G g) (cntT P2 r) (jT CB v1) _
        (2 * G + 2) (2 * P2 + 2) (2 * CB + 2) 0 false true hW hQ hR
        (by rw [List.length_append, jT_length C1 t ht]; omega),
      jT_split_pad C1 t E, show (0 : ℕ) + 1 = 1 from rfl, zeroT_head t _ ht0]
  rw [hw8] at f8
  have f9 := rst4_zeros (cntT G g) (cntT P2 r) (jT CB v1) G P2 CB t
    (List.replicate (2 * (C1 - t)) false ++ E) hW hQ hR ht0 false (t - 1) (le_refl _)
  have hlo10 : (cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (zeroT t (t - 1)
      ++ (List.replicate (2 * (C1 - t)) false ++ E))))).getD
      (2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 + 2 * (t - 1)) false = false := by
    rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 + 2 * (t - 1)
        = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + 2 * t)) from by omega]
    exact liftJ3 _ _ _ _ hW hQ hR (zeroE_m_lo t _ ht0)
  have f10 := rst4_zero_last (s := if t - 1 = 0 then false else true)
    (p := 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 + 2 * (t - 1))
    (T := cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (zeroT t (t - 1)
      ++ (List.replicate (2 * (C1 - t)) false ++ E))))) hlo10
  have hw10 : writeAt (writeAt (cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (zeroT t (t - 1)
      ++ (List.replicate (2 * (C1 - t)) false ++ E)))))
      (2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 + 2 * (t - 1)) false)
      (2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 + 2 * (t - 1) + 1) false
      = cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 0 ++ E))) := by
    rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 + 2 * (t - 1)
        = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + 2 * t)) from by omega,
      W2_append_right3 (cntT G g) (cntT P2 r) (jT CB v1) _
        (2 * G + 2) (2 * P2 + 2) (2 * CB + 2) (2 * t) false false hW hQ hR
        (by rw [List.length_append, zeroT_length t (t - 1) (le_refl _) ht0]; omega),
      zeroT_last t _ ht0, jT_join_pad C1 t ht E]
  rw [hw10] at f10
  rw [init_rst4,
    show 2 * G + 2 * P2 + 2 * CB + 2 * t + 10
      = 2 * G + (2 + (2 * P2 + (2 + (2 * v1 + (2 + (2 * (CB - v1) + (2 + (2
          + (2 * (t - 1) + 2))))))))) from by omega,
    run_add, f0, run_add, f0', run_add, f1, run_add, f1', run_add, f2, run_add, f2',
    run_add, f3, run_add, f3', run_add, f8, run_add, f9, f10,
    show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 + 2 * (t - 1) + 1
      = 2 * G + 2 * P2 + 2 * CB + 2 * t + 7 from by omega]

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitRst4
