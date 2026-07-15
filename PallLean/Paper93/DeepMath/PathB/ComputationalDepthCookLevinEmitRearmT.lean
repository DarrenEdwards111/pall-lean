import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitInterT

/-!
# Cook–Levin M2 emitter — the mirror-layout re-armer and THE MULTI-FAMILY LIVE-`t` CHAIN

`rearmTMachine` is the between-families interstitial for the mirror layout: on
`cntT G g ++ (unaryD N ++ (jT C t ++ (jT N N ++ E)))` it zeroes the saturated live variable and
**leaves the mirror untouched** — within one grand round, `t` must not change between families.
(The `interTMachine` from the previous brick — re-arm AND increment — closes the round.)

**The payoff** is `rep_liveFam2_run`: the per-`t` body
`engine(body₁) ⨟ rearmT ⨟ engine(body₂) ⨟ interT` under `repMachine` — every grand round emits BOTH
families' streams at the live index `t` **in order**, then re-arms and advances the mirror.  The
final output is `⋃_{t<B} (loop2Out body₁ t N ++ loop2Out body₂ t N)` — the exact interleaved
family order the tableau requires, from ONE machine.  Extending the chain to any fixed list of
two-source family bodies is the same `seq_run` fold, one application per family.
`rep_cellCopyWriteLive_run` instantiates it with the real tape-copy and write families.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitRearmT

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinCNFEncode
open PallLean.Paper93.DeepMath.PathB.CookLevinVarIndex
open PallLean.Paper93.DeepMath.PathB.CookLevinOneHotWindow
open PallLean.Paper93.DeepMath.PathB.CookLevinDynamics
open PallLean.Paper93.DeepMath.PathB.CookLevinWrite
open PallLean.Paper93.DeepMath.PathB.CookLevinEmit (encodeNat)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSplice
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRange
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitNestVar
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg2
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg3 (liftJ3 writeAt_append_right3)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitFamilyBodies
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSeq
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRearm (W2_append_right3)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg2T
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitInterT
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRep

/-! ## The machine

`Fin 15 × Bool`: `0/1` skip the grand counter, `2/3` skip the bound, `4/5` walk the mirror's
filled pairs, `6` cross the value marker, `7/8` cross the padding, `9/10` the zeroing head pair,
`11/12/13` the zeroing loop, `14` halt. -/

def rearmTMachine : Machine where
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
    else if s.1 = 6 then
      (if b then ((7, false), none, 1) else ((14, s.2), none, 2))
    else if s.1 = 7 then ((8, b), none, 1)
    else if s.1 = 8 then
      (if s.2 then ((9, s.2), none, 0)
       else (if b then ((9, s.2), none, 0) else ((7, s.2), none, 1)))
    else if s.1 = 9 then ((10, s.2), some false, 1)
    else if s.1 = 10 then ((11, s.2), some true, 1)
    else if s.1 = 11 then
      (if b then ((12, b), some false, 1) else ((13, b), some false, 1))
    else if s.1 = 12 then ((11, s.2), some false, 1)
    else if s.1 = 13 then ((14, s.2), some false, 2)
    else ((s.1, s.2), none, 2)
  accept := fun _ => false

theorem init_rt (t : List Bool) : init rearmTMachine t = ⟨(0, false), 0, t⟩ := rfl

/-! ## The step layer -/

section StepsRT
variable {s : Bool} {p : ℕ} {T : List Bool}

theorem rt_skipW (h1 : T.getD p false = true) :
    run rearmTMachine 2 ⟨(0, s), p, T⟩ = ⟨(0, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rearmTMachine ⟨(0, s), p, T⟩ = ⟨(1, T.getD p false), p + 1, T⟩ := by
    simp only [step, rearmTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, rearmTMachine, moveHead]; rfl

theorem rt_crossW (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run rearmTMachine 2 ⟨(0, s), p, T⟩ = ⟨(2, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rearmTMachine ⟨(0, s), p, T⟩ = ⟨(1, T.getD p false), p + 1, T⟩ := by
    simp only [step, rearmTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, rearmTMachine, moveHead, h2]

theorem rt_skipR1 (h1 : T.getD p false = true) :
    run rearmTMachine 2 ⟨(2, s), p, T⟩ = ⟨(2, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rearmTMachine ⟨(2, s), p, T⟩ = ⟨(3, T.getD p false), p + 1, T⟩ := by
    simp only [step, rearmTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, rearmTMachine, moveHead]; rfl

theorem rt_crossR1 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run rearmTMachine 2 ⟨(2, s), p, T⟩ = ⟨(4, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rearmTMachine ⟨(2, s), p, T⟩ = ⟨(3, T.getD p false), p + 1, T⟩ := by
    simp only [step, rearmTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, rearmTMachine, moveHead, h2]

theorem rt_walk (h1 : T.getD p false = true) :
    run rearmTMachine 2 ⟨(4, s), p, T⟩ = ⟨(4, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rearmTMachine ⟨(4, s), p, T⟩ = ⟨(5, true), p + 1, T⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, rearmTMachine, moveHead, h1']
  rw [e0]
  simp only [step, rearmTMachine, moveHead]; rfl

/-- Crossing the mirror's value marker. -/
theorem rt_crossM (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run rearmTMachine 2 ⟨(4, s), p, T⟩ = ⟨(7, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rearmTMachine ⟨(4, s), p, T⟩ = ⟨(6, s), p + 1, T⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, rearmTMachine, moveHead, h1']
  rw [e0]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, rearmTMachine, moveHead, h2]

theorem rt_pad (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = false) :
    run rearmTMachine 2 ⟨(7, s), p, T⟩ = ⟨(7, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rearmTMachine ⟨(7, s), p, T⟩ = ⟨(8, T.getD p false), p + 1, T⟩ := by
    simp only [step, rearmTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, rearmTMachine, moveHead, h2]

theorem rt_padBoundT (h1 : T.getD p false = true) :
    run rearmTMachine 2 ⟨(7, s), p, T⟩ = ⟨(9, true), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rearmTMachine ⟨(7, s), p, T⟩ = ⟨(8, T.getD p false), p + 1, T⟩ := by
    simp only [step, rearmTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, rearmTMachine, moveHead]; rfl

/-- The zeroing head-pair. -/
theorem rt_two_head :
    run rearmTMachine 2 ⟨(9, s), p, T⟩
      = ⟨(11, s), p + 2, writeAt (writeAt T p false) (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e4 : step rearmTMachine ⟨(9, s), p, T⟩ = ⟨(10, s), p + 1, writeAt T p false⟩ := by
    simp only [step, rearmTMachine, moveHead]; rfl
  have e5 : ∀ p' T', step rearmTMachine ⟨(10, s), p', T'⟩
      = ⟨(11, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, rearmTMachine, moveHead]; rfl
  rw [e4, e5]

theorem rt_two_step (h : T.getD p false = true) :
    run rearmTMachine 2 ⟨(11, s), p, T⟩
      = ⟨(11, true), p + 2, writeAt (writeAt T p false) (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e6 : step rearmTMachine ⟨(11, s), p, T⟩
      = ⟨(12, true), p + 1, writeAt T p false⟩ := by
    have h' := h
    rw [List.getD_eq_getElem?_getD] at h'
    simp [step, rearmTMachine, moveHead, h']
  rw [e6]
  simp only [step, rearmTMachine, moveHead]; rfl

theorem rt_two_last (h : T.getD p false = false) :
    run rearmTMachine 2 ⟨(11, s), p, T⟩
      = ⟨(14, false), p + 1, writeAt (writeAt T p false) (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e6 : step rearmTMachine ⟨(11, s), p, T⟩
      = ⟨(13, false), p + 1, writeAt T p false⟩ := by
    have h' := h
    rw [List.getD_eq_getElem?_getD] at h'
    simp [step, rearmTMachine, moveHead, h']
  rw [e6]
  simp only [step, rearmTMachine, moveHead]; rfl

end StepsRT

theorem rt_skipWs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run rearmTMachine (2 * k) ⟨(0, s), q, T⟩
      = ⟨(0, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), rt_skipW (h k (by omega))]
    rfl

theorem rt_skipR1s (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run rearmTMachine (2 * k) ⟨(2, s), q, T⟩
      = ⟨(2, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), rt_skipR1 (h k (by omega))]
    rfl

theorem rt_walks (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run rearmTMachine (2 * k) ⟨(4, s), q, T⟩
      = ⟨(4, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), rt_walk (h k (by omega))]
    rfl

theorem rt_pads (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = false
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run rearmTMachine (2 * k) ⟨(7, s), q, T⟩
      = ⟨(7, if k = 0 then s else false), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), rt_pad hk.1 hk.2]
    rfl

/-- The zeroing walk (three prefixes). -/
theorem rt_zeros (W Q R : List Bool) (G N C P : ℕ) (E : List Bool)
    (hW : W.length = 2 * G + 2) (hQ : Q.length = 2 * N + 2) (hR : R.length = 2 * C + 2)
    (hP : 0 < P) (s : Bool) (m : ℕ) (hm : m ≤ P - 1) :
    run rearmTMachine (2 * m)
      ⟨(11, s), 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2, W ++ (Q ++ (R ++ (zeroT P 0 ++ E)))⟩
      = ⟨(11, if m = 0 then s else true), 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 + 2 * m,
          W ++ (Q ++ (R ++ (zeroT P m ++ E)))⟩ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hlo : (W ++ (Q ++ (R ++ (zeroT P m ++ E)))).getD
        (2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 + 2 * m) false = true := by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 + 2 * m
          = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + 2 * (m + 1))) from by omega]
      exact liftJ3 _ _ _ _ hW hQ hR (zeroE_data_lo P m E (by omega))
    have hw : writeAt (writeAt (W ++ (Q ++ (R ++ (zeroT P m ++ E))))
        (2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 + 2 * m) false)
        (2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 + 2 * m + 1) false
        = W ++ (Q ++ (R ++ (zeroT P (m + 1) ++ E))) := by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 + 2 * m
          = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + 2 * (m + 1))) from by omega,
        W2_append_right3 W Q R _ (2 * G + 2) (2 * N + 2) (2 * C + 2) (2 * (m + 1))
          false false hW hQ hR
          (by rw [List.length_append, zeroT_length P m (by omega) hP]; omega),
        zeroT_step P m E (by omega)]
    rw [show 2 * (m + 1) = 2 * m + 2 from by ring, run_add, ih (by omega),
      rt_two_step hlo, hw]
    rfl

/-! ## THE MIRROR-LAYOUT RE-ARMER RUN -/

/-- **The between-families re-armer**: zero the saturated live variable, mirror UNTOUCHED. -/
theorem rearmT_run (G g : ℕ) (hg : g ≤ G) (N C t : ℕ) (hN : 0 < N) (htC : t ≤ C)
    (E : List Bool) :
    run rearmTMachine (2 * G + 4 * N + 2 * C + 10)
      (init rearmTMachine (cntT G g ++ (unaryD N ++ (jT C t ++ (jT N N ++ E)))))
      = ⟨(14, false), 2 * G + 2 * N + 2 * C + 2 * N + 7,
          cntT G g ++ (unaryD N ++ (jT C t ++ (jT N 0 ++ E)))⟩ := by
  have hW : (cntT G g).length = 2 * G + 2 := cntT_length G g hg
  have hQ : (unaryD N).length = 2 * N + 2 := unaryD_length N
  have hR : (jT C t).length = 2 * C + 2 := jT_length C t htC
  have f0 := rt_skipWs (cntT G g ++ (unaryD N ++ (jT C t ++ (jT N N ++ E)))) 0 G false
    (fun i hi => by simpa using cntE_lo G g _ i hg hi)
  simp only [Nat.zero_add] at f0
  have f0' := rt_crossW (s := if G = 0 then false else true) (p := 2 * G)
    (T := cntT G g ++ (unaryD N ++ (jT C t ++ (jT N N ++ E))))
    (cntE_cm_lo G g _ hg) (cntE_cm_hi G g _ hg)
  have f1 := rt_skipR1s (cntT G g ++ (unaryD N ++ (jT C t ++ (jT N N ++ E))))
    (2 * G + 2) N false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * i = 2 * G + 2 + (2 * i) from rfl, ← cntT_zero N]
      exact liftJ _ _ hW (cntE_lo N 0 _ i (by omega) hi))
  have f2 := rt_crossR1 (s := if N = 0 then false else true) (p := 2 * G + 2 + 2 * N)
    (T := cntT G g ++ (unaryD N ++ (jT C t ++ (jT N N ++ E))))
    (by rw [show 2 * G + 2 + 2 * N = 2 * G + 2 + (2 * N) from rfl, ← cntT_zero N]
        exact liftJ _ _ hW (cntE_cm_lo N 0 _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 1 = 2 * G + 2 + (2 * N + 1) from by omega,
        ← cntT_zero N]
        exact liftJ _ _ hW (cntE_cm_hi N 0 _ (by omega)))
  have f3 := rt_walks (cntT G g ++ (unaryD N ++ (jT C t ++ (jT N N ++ E))))
    (2 * G + 2 + 2 * N + 2) t false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * i = 2 * G + 2 + (2 * N + 2 + 2 * i)
          from by omega, ← jsT_zero C t]
      exact liftJ2 _ _ _ hW hQ
        (jsE_data C t 0 _ (2 * i) (by omega) (by omega) (by omega)))
  have f4 := rt_crossM (s := if t = 0 then false else true)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * t)
    (T := cntT G g ++ (unaryD N ++ (jT C t ++ (jT N N ++ E))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * t = 2 * G + 2 + (2 * N + 2 + 2 * t)
          from by omega, ← jsT_zero C t]
        exact liftJ2 _ _ _ hW hQ (jsE_m_lo C t 0 _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * t + 1 = 2 * G + 2 + (2 * N + 2 + (2 * t + 1))
          from by omega, ← jsT_zero C t]
        exact liftJ2 _ _ _ hW hQ (jsE_m_hi C t 0 _ (by omega)))
  have f5 := rt_pads (cntT G g ++ (unaryD N ++ (jT C t ++ (jT N N ++ E))))
    (2 * G + 2 + 2 * N + 2 + 2 * t + 2) (C - t) false
    (fun i hi => ⟨by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * t + 2 + 2 * i
          = 2 * G + 2 + (2 * N + 2 + (2 * t + 2 + 2 * i)) from by omega, ← jsT_zero C t]
      exact liftJ2 _ _ _ hW hQ (jsE_pad C t 0 _ (2 * t + 2 + 2 * i) (by omega) (by omega)
        (by omega) (by omega)), by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * t + 2 + 2 * i + 1
          = 2 * G + 2 + (2 * N + 2 + (2 * t + 2 + 2 * i + 1)) from by omega,
        ← jsT_zero C t]
      exact liftJ2 _ _ _ hW hQ (jsE_pad C t 0 _ (2 * t + 2 + 2 * i + 1) (by omega)
        (by omega) (by omega) (by omega))⟩)
  rw [show 2 * G + 2 + 2 * N + 2 + 2 * t + 2 + 2 * (C - t)
      = 2 * G + 2 + 2 * N + 2 + 2 * C + 2 from by omega] at f5
  have f6 := rt_padBoundT (s := if C - t = 0 then false else false)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * C + 2)
    (T := cntT G g ++ (unaryD N ++ (jT C t ++ (jT N N ++ E))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2
          = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + 0)) from by omega, ← jsT_zero N N]
        exact liftJ3 _ _ _ _ hW hQ hR
          (jsE_data N N 0 _ 0 (by omega) (by omega) (by omega)))
  have f7 := rt_two_head (s := true) (p := 2 * G + 2 + 2 * N + 2 + 2 * C + 2)
    (T := cntT G g ++ (unaryD N ++ (jT C t ++ (jT N N ++ E))))
  have hw7 : writeAt (writeAt (cntT G g ++ (unaryD N ++ (jT C t ++ (jT N N ++ E))))
      (2 * G + 2 + 2 * N + 2 + 2 * C + 2) false)
      (2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 1) true
      = cntT G g ++ (unaryD N ++ (jT C t ++ (zeroT N 0 ++ E))) := by
    rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2
        = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + 0)) from by omega,
      W2_append_right3 (cntT G g) (unaryD N) (jT C t) _ (2 * G + 2) (2 * N + 2)
        (2 * C + 2) 0 false true hW hQ hR
        (by rw [List.length_append, jT_length N N (le_refl N)]; omega)]
    rw [show (0 : ℕ) + 1 = 1 from rfl, zeroT_head N E hN]
  rw [hw7] at f7
  have f8 := rt_zeros (cntT G g) (unaryD N) (jT C t) G N C N E hW hQ hR hN true
    (N - 1) (le_refl _)
  have hlo9 : (cntT G g ++ (unaryD N ++ (jT C t ++ (zeroT N (N - 1) ++ E)))).getD
      (2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 + 2 * (N - 1)) false = false := by
    rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 + 2 * (N - 1)
        = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + 2 * N)) from by omega]
    exact liftJ3 _ _ _ _ hW hQ hR (zeroE_m_lo N E hN)
  have f9 := rt_two_last (s := if N - 1 = 0 then true else true)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 + 2 * (N - 1))
    (T := cntT G g ++ (unaryD N ++ (jT C t ++ (zeroT N (N - 1) ++ E)))) hlo9
  have hw9 : writeAt (writeAt (cntT G g ++ (unaryD N ++ (jT C t ++ (zeroT N (N - 1) ++ E))))
      (2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 + 2 * (N - 1)) false)
      (2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 + 2 * (N - 1) + 1) false
      = cntT G g ++ (unaryD N ++ (jT C t ++ (jT N 0 ++ E))) := by
    rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 + 2 * (N - 1)
        = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + 2 * N)) from by omega,
      W2_append_right3 (cntT G g) (unaryD N) (jT C t) _ (2 * G + 2) (2 * N + 2)
        (2 * C + 2) (2 * N) false false hW hQ hR
        (by rw [List.length_append, zeroT_length N (N - 1) (le_refl _) hN]; omega),
      zeroT_last N E hN]
  rw [hw9] at f9
  rw [init_rt,
    show 2 * G + 4 * N + 2 * C + 10
      = 2 * G + (2 + (2 * N + (2 + (2 * t + (2 + (2 * (C - t) + (2 + (2
          + (2 * (N - 1) + 2))))))))) from by omega,
    run_add, f0, run_add, f0', run_add, f1, run_add, f2, run_add, f3, run_add, f4,
    run_add, f5, run_add, f6, run_add, f7, run_add, f8, f9,
    show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 + 2 * (N - 1) + 1
      = 2 * G + 2 * N + 2 * C + 2 * N + 7 from by omega]

theorem rearmT_halt : rearmTMachine.halt ((14 : Fin 15), false) = true := rfl

/-! ## THE MULTI-FAMILY LIVE-`t` CHAIN -/

/-- The accumulated two-family live streams, in order. -/
def liveFam2Out (b1 b2 : List LInstr) (N : ℕ) : ℕ → List Bool
  | 0 => []
  | t + 1 => liveFam2Out b1 b2 N t ++ (loop2Out b1 t N ++ loop2Out b2 t N)

/-- **THE MULTI-FAMILY LIVE-`t` GRAND CHAIN**: per grand round, the per-`t` body
`engine(b₁) ⨟ rearmT ⨟ engine(b₂) ⨟ interT` emits BOTH families' streams at the live index in
order; `B` rounds give `⋃_{t<B} (stream₁(t) ++ stream₂(t))`.  Extending to any fixed family list
is one more `seq_run` per family. -/
theorem rep_liveFam2_run (b1 b2 : List LInstr) (N : ℕ) (hN : 0 < N) (B : ℕ)
    (out : List Bool) :
    run (repMachine (seqMachine (seqMachine (seqMachine
          (loopProg2TMachine b1) rearmTMachine) (loopProg2TMachine b2)) interTMachine))
      (repRounds (fun t =>
          ltClock b1 B N B t (out ++ liveFam2Out b1 b2 N t).length + 1
            + (2 * B + 4 * N + 2 * B + 10) + 1
            + ltClock b2 B N B t
                ((out ++ liveFam2Out b1 b2 N t) ++ loop2Out b1 t N).length + 1
            + (2 * B + 4 * N + 2 * B + 10)) B + (4 * B + 4))
      (init (repMachine (seqMachine (seqMachine (seqMachine
          (loopProg2TMachine b1) rearmTMachine) (loopProg2TMachine b2)) interTMachine))
        (cntT B 0 ++ (unaryD N ++ (jT B 0 ++ (jT N 0 ++ encodeD out)))))
      = ⟨Sum.inl (4, false), 2 * B + 1,
          unaryD B ++ (unaryD N ++ (jT B B ++ (jT N 0
            ++ encodeD (out ++ liveFam2Out b1 b2 N B))))⟩ := by
  have h := rep_run (seqMachine (seqMachine (seqMachine
      (loopProg2TMachine b1) rearmTMachine) (loopProg2TMachine b2)) interTMachine) B
    (fun t => unaryD N ++ (jT B t ++ (jT N 0 ++ encodeD (out ++ liveFam2Out b1 b2 N t))))
    (fun t => ltClock b1 B N B t (out ++ liveFam2Out b1 b2 N t).length + 1
        + (2 * B + 4 * N + 2 * B + 10) + 1
        + ltClock b2 B N B t
            ((out ++ liveFam2Out b1 b2 N t) ++ loop2Out b1 t N).length + 1
        + (2 * B + 4 * N + 2 * B + 10))
    (fun _ => Sum.inr (16, false)) (fun _ => 2 * B + 2 * N + 2 * B + 2 * N + 7)
    (fun t ht => by
      constructor
      · have heng1 := loopProg2T_run b1 B (t + 1) (by omega) N B t (by omega)
          (out ++ liveFam2Out b1 b2 N t)
        have hrt := rearmT_run B (t + 1) (by omega) N B t hN (by omega)
          (encodeD ((out ++ liveFam2Out b1 b2 N t) ++ loop2Out b1 t N))
        rw [show jT N N = unaryD N from jT_full N] at hrt
        have hseq1 := seq_run (loopProg2TMachine b1) rearmTMachine _ _ _ _ _ _ _ _ _
          heng1 rfl hrt rfl
        have heng2 := loopProg2T_run b2 B (t + 1) (by omega) N B t (by omega)
          ((out ++ liveFam2Out b1 b2 N t) ++ loop2Out b1 t N)
        have hseq2 := seq_run (seqMachine (loopProg2TMachine b1) rearmTMachine)
          (loopProg2TMachine b2) _ _ _ _ _ _ _ _ _
          hseq1 (seq_halt_final _ _ _ rfl) heng2 rfl
        have hinter := interT_run B (t + 1) (by omega) N B t hN ht
          (encodeD (((out ++ liveFam2Out b1 b2 N t) ++ loop2Out b1 t N)
            ++ loop2Out b2 t N))
        rw [show jT N N = unaryD N from jT_full N] at hinter
        have hseq3 := seq_run (seqMachine (seqMachine (loopProg2TMachine b1)
            rearmTMachine) (loopProg2TMachine b2)) interTMachine _ _ _ _ _ _ _ _ _
          hseq2 (seq_halt_final _ _ _ rfl) hinter rfl
        rw [show ((out ++ liveFam2Out b1 b2 N t) ++ loop2Out b1 t N) ++ loop2Out b2 t N
            = out ++ liveFam2Out b1 b2 N (t + 1) from by
          show _ = out ++ (liveFam2Out b1 b2 N t ++ (loop2Out b1 t N ++ loop2Out b2 t N))
          simp [List.append_assoc]] at hseq3
        exact hseq3
      · rfl)
  simp only [show liveFam2Out b1 b2 N 0 = [] from rfl, List.append_nil] at h
  exact h

/-- **Two real tableau families, all times, exact order, one machine**: the tape-copy family then
the write family, per grand round `t = 0..B-1`. -/
theorem rep_cellCopyWriteLive_run (qi : ℕ) (b wb : Bool) (P B : ℕ) (out : List Bool) :
    run (repMachine (seqMachine (seqMachine (seqMachine
          (loopProg2TMachine cellCopyBody) rearmTMachine)
          (loopProg2TMachine (writeBody qi b wb))) interTMachine))
      (repRounds (fun t =>
          ltClock cellCopyBody B (P + 1) B t
              (out ++ liveFam2Out cellCopyBody (writeBody qi b wb) (P + 1) t).length + 1
            + (2 * B + 4 * (P + 1) + 2 * B + 10) + 1
            + ltClock (writeBody qi b wb) B (P + 1) B t
                ((out ++ liveFam2Out cellCopyBody (writeBody qi b wb) (P + 1) t)
                  ++ loop2Out cellCopyBody t (P + 1)).length + 1
            + (2 * B + 4 * (P + 1) + 2 * B + 10)) B + (4 * B + 4))
      (init (repMachine (seqMachine (seqMachine (seqMachine
          (loopProg2TMachine cellCopyBody) rearmTMachine)
          (loopProg2TMachine (writeBody qi b wb))) interTMachine))
        (cntT B 0 ++ (unaryD (P + 1) ++ (jT B 0 ++ (jT (P + 1) 0 ++ encodeD out)))))
      = ⟨Sum.inl (4, false), 2 * B + 1,
          unaryD B ++ (unaryD (P + 1) ++ (jT B B ++ (jT (P + 1) 0
            ++ encodeD (out
              ++ liveFam2Out cellCopyBody (writeBody qi b wb) (P + 1) B))))⟩ :=
  rep_liveFam2_run cellCopyBody (writeBody qi b wb) (P + 1) (by omega) B out

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitRearmT