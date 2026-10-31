import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitRearm
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitLoopProg3P

/-!
# Cook–Levin M2 emitter — the prefixed interstitial counter-management machines

The re-armers re-derived for the grand-prefixed layouts: `rearm2PMachine` for
`cntT G g ++ (unaryD N ++ (unaryD a ++ (jT P P ++ E)))` and `rearm3PMachine` for the triple-source
layout — one extra leading skip pair each, every position shifted by `2G+2`, the zeroing walk one
lift level up (`W2_append_right2 → W2_append_right3 → W2_append_right4`).  **The payoff is the
prefixed chain demonstration** `familyP_chain_run`: the prefixed tape-copy emitter, the prefixed
re-armer, and the prefixed write emitter — composed by `seq_run` twice into **one machine** — emit
both families' clause streams in order at time `t` UNDER THE GRAND PREFIX, self-halting at the
explicit summed clock.  This is the per-`t` body pattern for the grand loop: engines chain because
each leaves the prefix verbatim and the re-armer restores the variable interface.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitRearmP

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinCNFEncode
open PallLean.Paper93.DeepMath.PathB.CookLevinVarIndex
open PallLean.Paper93.DeepMath.PathB.CookLevinTransition
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
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
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg3
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg2P
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg3P (liftJ4 writeAt_append_right4)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitFamilyBodies
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSeq
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRearm

/-! ## A two-write lift under four prefixes -/

theorem W2_append_right4 (A B C D X : List Bool) (qa qb qc qd p : ℕ) (b1 b2 : Bool)
    (ha : A.length = qa) (hb : B.length = qb) (hc : C.length = qc) (hd : D.length = qd)
    (hp : p + 1 < X.length) :
    writeAt (writeAt (A ++ (B ++ (C ++ (D ++ X)))) (qa + (qb + (qc + (qd + p)))) b1)
        (qa + (qb + (qc + (qd + p))) + 1) b2
      = A ++ (B ++ (C ++ (D ++ writeAt (writeAt X p b1) (p + 1) b2))) := by
  have hl1 : (writeAt X p b1).length = X.length := by
    rw [writeAt_of_lt b1 (by omega), List.length_set]
  rw [writeAt_append_right4 A B C D X qa qb qc qd p b1 ha hb hc hd (by omega),
    show qa + (qb + (qc + (qd + p))) + 1 = qa + (qb + (qc + (qd + (p + 1)))) from by omega,
    writeAt_append_right4 A B C D _ qa qb qc qd (p + 1) b2 ha hb hc hd (by rw [hl1]; omega)]

/-! ## The prefixed two-source re-armer

Layout `cntT G g ++ (unaryD N ++ (unaryD a ++ (jT P P ++ E)))`: skip the grand prefix, skip the two
counters, zero the variable, halt. -/

def rearm2PMachine : Machine where
  State := Fin 12 × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, false)
  halt := fun s => decide (s.1 = 11)
  δ := fun s b =>
    if s.1 = 0 then ((1, b), none, 1)
    else if s.1 = 1 then
      (if s.2 then ((0, s.2), none, 1)
       else (if b then ((2, s.2), none, 1) else ((11, s.2), none, 2)))
    else if s.1 = 2 then ((3, b), none, 1)
    else if s.1 = 3 then
      (if s.2 then ((2, s.2), none, 1)
       else (if b then ((4, s.2), none, 1) else ((11, s.2), none, 2)))
    else if s.1 = 4 then ((5, b), none, 1)
    else if s.1 = 5 then
      (if s.2 then ((4, s.2), none, 1)
       else (if b then ((6, s.2), none, 1) else ((11, s.2), none, 2)))
    else if s.1 = 6 then ((7, s.2), some false, 1)
    else if s.1 = 7 then ((8, s.2), some true, 1)
    else if s.1 = 8 then
      (if b then ((9, b), some false, 1) else ((10, b), some false, 1))
    else if s.1 = 9 then ((8, s.2), some false, 1)
    else if s.1 = 10 then ((11, s.2), some false, 2)
    else ((s.1, s.2), none, 2)
  accept := fun _ => false

theorem init_r2p (t : List Bool) : init rearm2PMachine t = ⟨(0, false), 0, t⟩ := rfl

section StepsR2P
variable {s : Bool} {p : ℕ} {T : List Bool}

theorem r2p_skipW (h1 : T.getD p false = true) :
    run rearm2PMachine 2 ⟨(0, s), p, T⟩ = ⟨(0, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rearm2PMachine ⟨(0, s), p, T⟩ = ⟨(1, T.getD p false), p + 1, T⟩ := by
    simp only [step, rearm2PMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, rearm2PMachine, moveHead]; rfl

theorem r2p_crossW (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run rearm2PMachine 2 ⟨(0, s), p, T⟩ = ⟨(2, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rearm2PMachine ⟨(0, s), p, T⟩ = ⟨(1, T.getD p false), p + 1, T⟩ := by
    simp only [step, rearm2PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, rearm2PMachine, moveHead, h2]

theorem r2p_skipR1 (h1 : T.getD p false = true) :
    run rearm2PMachine 2 ⟨(2, s), p, T⟩ = ⟨(2, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rearm2PMachine ⟨(2, s), p, T⟩ = ⟨(3, T.getD p false), p + 1, T⟩ := by
    simp only [step, rearm2PMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, rearm2PMachine, moveHead]; rfl

theorem r2p_crossR1 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run rearm2PMachine 2 ⟨(2, s), p, T⟩ = ⟨(4, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rearm2PMachine ⟨(2, s), p, T⟩ = ⟨(3, T.getD p false), p + 1, T⟩ := by
    simp only [step, rearm2PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, rearm2PMachine, moveHead, h2]

theorem r2p_skipR2 (h1 : T.getD p false = true) :
    run rearm2PMachine 2 ⟨(4, s), p, T⟩ = ⟨(4, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rearm2PMachine ⟨(4, s), p, T⟩ = ⟨(5, T.getD p false), p + 1, T⟩ := by
    simp only [step, rearm2PMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, rearm2PMachine, moveHead]; rfl

theorem r2p_crossR2 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run rearm2PMachine 2 ⟨(4, s), p, T⟩ = ⟨(6, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rearm2PMachine ⟨(4, s), p, T⟩ = ⟨(5, T.getD p false), p + 1, T⟩ := by
    simp only [step, rearm2PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, rearm2PMachine, moveHead, h2]

/-- The zeroing head-pair: `false, true` blind writes. -/
theorem r2p_two_head :
    run rearm2PMachine 2 ⟨(6, s), p, T⟩
      = ⟨(8, s), p + 2, writeAt (writeAt T p false) (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e4 : step rearm2PMachine ⟨(6, s), p, T⟩ = ⟨(7, s), p + 1, writeAt T p false⟩ := by
    simp only [step, rearm2PMachine, moveHead]; rfl
  have e5 : ∀ p' T', step rearm2PMachine ⟨(7, s), p', T'⟩
      = ⟨(8, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, rearm2PMachine, moveHead]; rfl
  rw [e4, e5]

/-- A zeroing step-pair: the stage's low cell reads `true` (a data pair remains). -/
theorem r2p_two_step (h : T.getD p false = true) :
    run rearm2PMachine 2 ⟨(8, s), p, T⟩
      = ⟨(8, true), p + 2, writeAt (writeAt T p false) (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e6 : step rearm2PMachine ⟨(8, s), p, T⟩ = ⟨(9, true), p + 1, writeAt T p false⟩ := by
    have h' := h
    rw [List.getD_eq_getElem?_getD] at h'
    simp [step, rearm2PMachine, moveHead, h']
  rw [e6]
  simp only [step, rearm2PMachine, moveHead]; rfl

/-- The zeroing last-pair: the low cell reads `false` (the old marker) — write and halt. -/
theorem r2p_two_last (h : T.getD p false = false) :
    run rearm2PMachine 2 ⟨(8, s), p, T⟩
      = ⟨(11, false), p + 1, writeAt (writeAt T p false) (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e6 : step rearm2PMachine ⟨(8, s), p, T⟩
      = ⟨(10, false), p + 1, writeAt T p false⟩ := by
    have h' := h
    rw [List.getD_eq_getElem?_getD] at h'
    simp [step, rearm2PMachine, moveHead, h']
  rw [e6]
  simp only [step, rearm2PMachine, moveHead]; rfl

end StepsR2P

theorem r2p_skipWs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run rearm2PMachine (2 * k) ⟨(0, s), q, T⟩
      = ⟨(0, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), r2p_skipW (h k (by omega))]
    rfl

theorem r2p_skipR1s (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run rearm2PMachine (2 * k) ⟨(2, s), q, T⟩
      = ⟨(2, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), r2p_skipR1 (h k (by omega))]
    rfl

theorem r2p_skipR2s (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run rearm2PMachine (2 * k) ⟨(4, s), q, T⟩
      = ⟨(4, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), r2p_skipR2 (h k (by omega))]
    rfl

/-- The zeroing walk (evolving `zeroT`, three prefixes). -/
theorem r2p_zeros (W Q R : List Bool) (G N a P : ℕ) (E : List Bool)
    (hW : W.length = 2 * G + 2) (hQ : Q.length = 2 * N + 2) (hR : R.length = 2 * a + 2)
    (hP : 0 < P) (s : Bool) (m : ℕ) (hm : m ≤ P - 1) :
    run rearm2PMachine (2 * m)
      ⟨(8, s), 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2, W ++ (Q ++ (R ++ (zeroT P 0 ++ E)))⟩
      = ⟨(8, if m = 0 then s else true), 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 + 2 * m,
          W ++ (Q ++ (R ++ (zeroT P m ++ E)))⟩ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hlo : (W ++ (Q ++ (R ++ (zeroT P m ++ E)))).getD
        (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 + 2 * m) false = true := by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 + 2 * m
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + 2 * (m + 1))) from by omega]
      exact liftJ3 _ _ _ _ hW hQ hR (zeroE_data_lo P m E (by omega))
    have hw : writeAt (writeAt (W ++ (Q ++ (R ++ (zeroT P m ++ E))))
        (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 + 2 * m) false)
        (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 + 2 * m + 1) false
        = W ++ (Q ++ (R ++ (zeroT P (m + 1) ++ E))) := by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 + 2 * m
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + 2 * (m + 1))) from by omega,
        W2_append_right3 W Q R _ (2 * G + 2) (2 * N + 2) (2 * a + 2) (2 * (m + 1))
          false false hW hQ hR
          (by rw [List.length_append, zeroT_length P m (by omega) hP]; omega),
        zeroT_step P m E (by omega)]
    rw [show 2 * (m + 1) = 2 * m + 2 from by ring, run_add, ih (by omega),
      r2p_two_step hlo, hw]
    rfl

/-- **The prefixed two-source re-armer**: on any tape
`cntT G g ++ (unaryD N ++ (unaryD a ++ (jT P P ++ E)))` it halts by itself at the explicit clock
having zeroed the variable — `jT P 0` — with everything else, the prefix included, untouched. -/
theorem rearm2P_run (G g : ℕ) (hg : g ≤ G) (N a P : ℕ) (hP : 0 < P) (E : List Bool) :
    run rearm2PMachine (2 * G + 2 * N + 2 * a + 2 * P + 8)
      (init rearm2PMachine (cntT G g ++ (unaryD N ++ (unaryD a ++ (jT P P ++ E)))))
      = ⟨(11, false), 2 * G + 2 * N + 2 * a + 2 * P + 7,
          cntT G g ++ (unaryD N ++ (unaryD a ++ (jT P 0 ++ E)))⟩ := by
  have hW : (cntT G g).length = 2 * G + 2 := cntT_length G g hg
  have hQ : (unaryD N).length = 2 * N + 2 := unaryD_length N
  have hR : (unaryD a).length = 2 * a + 2 := unaryD_length a
  have f0 := r2p_skipWs (cntT G g ++ (unaryD N ++ (unaryD a ++ (jT P P ++ E)))) 0 G false
    (fun i hi => by simpa using cntE_lo G g _ i hg hi)
  simp only [Nat.zero_add] at f0
  have f0' := r2p_crossW (s := if G = 0 then false else true) (p := 2 * G)
    (T := cntT G g ++ (unaryD N ++ (unaryD a ++ (jT P P ++ E))))
    (cntE_cm_lo G g _ hg) (cntE_cm_hi G g _ hg)
  have f1 := r2p_skipR1s (cntT G g ++ (unaryD N ++ (unaryD a ++ (jT P P ++ E))))
    (2 * G + 2) N false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * i = 2 * G + 2 + (2 * i) from rfl, ← cntT_zero N]
      exact liftJ _ _ hW (cntE_lo N 0 _ i (by omega) hi))
  have f2 := r2p_crossR1 (s := if N = 0 then false else true) (p := 2 * G + 2 + 2 * N)
    (T := cntT G g ++ (unaryD N ++ (unaryD a ++ (jT P P ++ E))))
    (by rw [show 2 * G + 2 + 2 * N = 2 * G + 2 + (2 * N) from rfl, ← cntT_zero N]
        exact liftJ _ _ hW (cntE_cm_lo N 0 _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 1 = 2 * G + 2 + (2 * N + 1) from by omega,
        ← cntT_zero N]
        exact liftJ _ _ hW (cntE_cm_hi N 0 _ (by omega)))
  have f3 := r2p_skipR2s (cntT G g ++ (unaryD N ++ (unaryD a ++ (jT P P ++ E))))
    (2 * G + 2 + 2 * N + 2) a false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * i = 2 * G + 2 + (2 * N + 2 + 2 * i)
          from by omega, ← cntT_zero a]
      exact liftJ2 _ _ _ hW hQ (cntE_lo a 0 _ i (by omega) hi))
  have f4 := r2p_crossR2 (s := if a = 0 then false else true)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * a)
    (T := cntT G g ++ (unaryD N ++ (unaryD a ++ (jT P P ++ E))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a = 2 * G + 2 + (2 * N + 2 + 2 * a)
          from by omega, ← cntT_zero a]
        exact liftJ2 _ _ _ hW hQ (cntE_cm_lo a 0 _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 1 = 2 * G + 2 + (2 * N + 2 + (2 * a + 1))
          from by omega, ← cntT_zero a]
        exact liftJ2 _ _ _ hW hQ (cntE_cm_hi a 0 _ (by omega)))
  have f5 := r2p_two_head (s := false) (p := 2 * G + 2 + 2 * N + 2 + 2 * a + 2)
    (T := cntT G g ++ (unaryD N ++ (unaryD a ++ (jT P P ++ E))))
  have hw5 : writeAt (writeAt (cntT G g ++ (unaryD N ++ (unaryD a ++ (jT P P ++ E))))
      (2 * G + 2 + 2 * N + 2 + 2 * a + 2) false)
      (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 1) true
      = cntT G g ++ (unaryD N ++ (unaryD a ++ (zeroT P 0 ++ E))) := by
    rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2
        = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + 0)) from by omega,
      W2_append_right3 (cntT G g) (unaryD N) (unaryD a) _ (2 * G + 2) (2 * N + 2)
        (2 * a + 2) 0 false true hW hQ hR
        (by rw [List.length_append, jT_length P P (le_refl P)]; omega)]
    rw [show (0 : ℕ) + 1 = 1 from rfl, zeroT_head P E hP]
  rw [hw5] at f5
  have f6 := r2p_zeros (cntT G g) (unaryD N) (unaryD a) G N a P E hW hQ hR hP false
    (P - 1) (le_refl _)
  have hlo7 : (cntT G g ++ (unaryD N ++ (unaryD a ++ (zeroT P (P - 1) ++ E)))).getD
      (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 + 2 * (P - 1)) false = false := by
    rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 + 2 * (P - 1)
        = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + 2 * P)) from by omega]
    exact liftJ3 _ _ _ _ hW hQ hR (zeroE_m_lo P E hP)
  have f7 := r2p_two_last (s := if P - 1 = 0 then false else true)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 + 2 * (P - 1))
    (T := cntT G g ++ (unaryD N ++ (unaryD a ++ (zeroT P (P - 1) ++ E)))) hlo7
  have hw7 : writeAt (writeAt (cntT G g ++ (unaryD N ++ (unaryD a ++ (zeroT P (P - 1) ++ E))))
      (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 + 2 * (P - 1)) false)
      (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 + 2 * (P - 1) + 1) false
      = cntT G g ++ (unaryD N ++ (unaryD a ++ (jT P 0 ++ E))) := by
    rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 + 2 * (P - 1)
        = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + 2 * P)) from by omega,
      W2_append_right3 (cntT G g) (unaryD N) (unaryD a) _ (2 * G + 2) (2 * N + 2)
        (2 * a + 2) (2 * P) false false hW hQ hR
        (by rw [List.length_append, zeroT_length P (P - 1) (le_refl _) hP]; omega),
      zeroT_last P E hP]
  rw [hw7] at f7
  rw [init_r2p,
    show 2 * G + 2 * N + 2 * a + 2 * P + 8
      = 2 * G + (2 + (2 * N + (2 + (2 * a + (2 + (2 + (2 * (P - 1) + 2)))))))
      from by omega,
    run_add, f0, run_add, f0', run_add, f1, run_add, f2, run_add, f3, run_add, f4,
    run_add, f5, run_add, f6, f7,
    show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 + 2 * (P - 1) + 1
      = 2 * G + 2 * N + 2 * a + 2 * P + 7 from by omega]

theorem rearm2P_halt : rearm2PMachine.halt ((11 : Fin 12), false) = true := rfl

/-! ## The prefixed triple-source re-armer

Layout `cntT G g ++ (unaryD N ++ (unaryD a ++ (unaryD c ++ (jT P P ++ E))))`: one more skip pair. -/

def rearm3PMachine : Machine where
  State := Fin 14 × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, false)
  halt := fun s => decide (s.1 = 13)
  δ := fun s b =>
    if s.1 = 0 then ((1, b), none, 1)
    else if s.1 = 1 then
      (if s.2 then ((0, s.2), none, 1)
       else (if b then ((2, s.2), none, 1) else ((13, s.2), none, 2)))
    else if s.1 = 2 then ((3, b), none, 1)
    else if s.1 = 3 then
      (if s.2 then ((2, s.2), none, 1)
       else (if b then ((4, s.2), none, 1) else ((13, s.2), none, 2)))
    else if s.1 = 4 then ((5, b), none, 1)
    else if s.1 = 5 then
      (if s.2 then ((4, s.2), none, 1)
       else (if b then ((6, s.2), none, 1) else ((13, s.2), none, 2)))
    else if s.1 = 6 then ((7, b), none, 1)
    else if s.1 = 7 then
      (if s.2 then ((6, s.2), none, 1)
       else (if b then ((8, s.2), none, 1) else ((13, s.2), none, 2)))
    else if s.1 = 8 then ((9, s.2), some false, 1)
    else if s.1 = 9 then ((10, s.2), some true, 1)
    else if s.1 = 10 then
      (if b then ((11, b), some false, 1) else ((12, b), some false, 1))
    else if s.1 = 11 then ((10, s.2), some false, 1)
    else if s.1 = 12 then ((13, s.2), some false, 2)
    else ((s.1, s.2), none, 2)
  accept := fun _ => false

theorem init_r3p (t : List Bool) : init rearm3PMachine t = ⟨(0, false), 0, t⟩ := rfl

section StepsR3P
variable {s : Bool} {p : ℕ} {T : List Bool}

theorem r3p_skipW (h1 : T.getD p false = true) :
    run rearm3PMachine 2 ⟨(0, s), p, T⟩ = ⟨(0, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rearm3PMachine ⟨(0, s), p, T⟩ = ⟨(1, T.getD p false), p + 1, T⟩ := by
    simp only [step, rearm3PMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, rearm3PMachine, moveHead]; rfl

theorem r3p_crossW (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run rearm3PMachine 2 ⟨(0, s), p, T⟩ = ⟨(2, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rearm3PMachine ⟨(0, s), p, T⟩ = ⟨(1, T.getD p false), p + 1, T⟩ := by
    simp only [step, rearm3PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, rearm3PMachine, moveHead, h2]

theorem r3p_skipR1 (h1 : T.getD p false = true) :
    run rearm3PMachine 2 ⟨(2, s), p, T⟩ = ⟨(2, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rearm3PMachine ⟨(2, s), p, T⟩ = ⟨(3, T.getD p false), p + 1, T⟩ := by
    simp only [step, rearm3PMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, rearm3PMachine, moveHead]; rfl

theorem r3p_crossR1 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run rearm3PMachine 2 ⟨(2, s), p, T⟩ = ⟨(4, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rearm3PMachine ⟨(2, s), p, T⟩ = ⟨(3, T.getD p false), p + 1, T⟩ := by
    simp only [step, rearm3PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, rearm3PMachine, moveHead, h2]

theorem r3p_skipR2 (h1 : T.getD p false = true) :
    run rearm3PMachine 2 ⟨(4, s), p, T⟩ = ⟨(4, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rearm3PMachine ⟨(4, s), p, T⟩ = ⟨(5, T.getD p false), p + 1, T⟩ := by
    simp only [step, rearm3PMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, rearm3PMachine, moveHead]; rfl

theorem r3p_crossR2 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run rearm3PMachine 2 ⟨(4, s), p, T⟩ = ⟨(6, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rearm3PMachine ⟨(4, s), p, T⟩ = ⟨(5, T.getD p false), p + 1, T⟩ := by
    simp only [step, rearm3PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, rearm3PMachine, moveHead, h2]

theorem r3p_skipR3 (h1 : T.getD p false = true) :
    run rearm3PMachine 2 ⟨(6, s), p, T⟩ = ⟨(6, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rearm3PMachine ⟨(6, s), p, T⟩ = ⟨(7, T.getD p false), p + 1, T⟩ := by
    simp only [step, rearm3PMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, rearm3PMachine, moveHead]; rfl

theorem r3p_crossR3 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run rearm3PMachine 2 ⟨(6, s), p, T⟩ = ⟨(8, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rearm3PMachine ⟨(6, s), p, T⟩ = ⟨(7, T.getD p false), p + 1, T⟩ := by
    simp only [step, rearm3PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, rearm3PMachine, moveHead, h2]

theorem r3p_two_head :
    run rearm3PMachine 2 ⟨(8, s), p, T⟩
      = ⟨(10, s), p + 2, writeAt (writeAt T p false) (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e4 : step rearm3PMachine ⟨(8, s), p, T⟩ = ⟨(9, s), p + 1, writeAt T p false⟩ := by
    simp only [step, rearm3PMachine, moveHead]; rfl
  have e5 : ∀ p' T', step rearm3PMachine ⟨(9, s), p', T'⟩
      = ⟨(10, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, rearm3PMachine, moveHead]; rfl
  rw [e4, e5]

theorem r3p_two_step (h : T.getD p false = true) :
    run rearm3PMachine 2 ⟨(10, s), p, T⟩
      = ⟨(10, true), p + 2, writeAt (writeAt T p false) (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e6 : step rearm3PMachine ⟨(10, s), p, T⟩
      = ⟨(11, true), p + 1, writeAt T p false⟩ := by
    have h' := h
    rw [List.getD_eq_getElem?_getD] at h'
    simp [step, rearm3PMachine, moveHead, h']
  rw [e6]
  simp only [step, rearm3PMachine, moveHead]; rfl

theorem r3p_two_last (h : T.getD p false = false) :
    run rearm3PMachine 2 ⟨(10, s), p, T⟩
      = ⟨(13, false), p + 1, writeAt (writeAt T p false) (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e6 : step rearm3PMachine ⟨(10, s), p, T⟩
      = ⟨(12, false), p + 1, writeAt T p false⟩ := by
    have h' := h
    rw [List.getD_eq_getElem?_getD] at h'
    simp [step, rearm3PMachine, moveHead, h']
  rw [e6]
  simp only [step, rearm3PMachine, moveHead]; rfl

end StepsR3P

theorem r3p_skipWs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run rearm3PMachine (2 * k) ⟨(0, s), q, T⟩
      = ⟨(0, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), r3p_skipW (h k (by omega))]
    rfl

theorem r3p_skipR1s (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run rearm3PMachine (2 * k) ⟨(2, s), q, T⟩
      = ⟨(2, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), r3p_skipR1 (h k (by omega))]
    rfl

theorem r3p_skipR2s (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run rearm3PMachine (2 * k) ⟨(4, s), q, T⟩
      = ⟨(4, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), r3p_skipR2 (h k (by omega))]
    rfl

theorem r3p_skipR3s (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run rearm3PMachine (2 * k) ⟨(6, s), q, T⟩
      = ⟨(6, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), r3p_skipR3 (h k (by omega))]
    rfl

/-- The zeroing walk (evolving `zeroT`, four prefixes). -/
theorem r3p_zeros (W Q R S : List Bool) (G N a c P : ℕ) (E : List Bool)
    (hW : W.length = 2 * G + 2) (hQ : Q.length = 2 * N + 2) (hR : R.length = 2 * a + 2)
    (hS : S.length = 2 * c + 2) (hP : 0 < P) (s : Bool) (m : ℕ) (hm : m ≤ P - 1) :
    run rearm3PMachine (2 * m)
      ⟨(10, s), 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2,
        W ++ (Q ++ (R ++ (S ++ (zeroT P 0 ++ E))))⟩
      = ⟨(10, if m = 0 then s else true),
          2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 + 2 * m,
          W ++ (Q ++ (R ++ (S ++ (zeroT P m ++ E))))⟩ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hlo : (W ++ (Q ++ (R ++ (S ++ (zeroT P m ++ E))))).getD
        (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 + 2 * m) false = true := by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 + 2 * m
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 2 + 2 * (m + 1))))
          from by omega]
      exact liftJ4 _ _ _ _ _ hW hQ hR hS (zeroE_data_lo P m E (by omega))
    have hw : writeAt (writeAt (W ++ (Q ++ (R ++ (S ++ (zeroT P m ++ E)))))
        (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 + 2 * m) false)
        (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 + 2 * m + 1) false
        = W ++ (Q ++ (R ++ (S ++ (zeroT P (m + 1) ++ E)))) := by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 + 2 * m
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 2 + 2 * (m + 1))))
          from by omega,
        W2_append_right4 W Q R S _ (2 * G + 2) (2 * N + 2) (2 * a + 2) (2 * c + 2)
          (2 * (m + 1)) false false hW hQ hR hS
          (by rw [List.length_append, zeroT_length P m (by omega) hP]; omega),
        zeroT_step P m E (by omega)]
    rw [show 2 * (m + 1) = 2 * m + 2 from by ring, run_add, ih (by omega),
      r3p_two_step hlo, hw]
    rfl

/-- **The prefixed triple-source re-armer**: zero the fifth-region variable, everything else — the
prefix included — untouched. -/
theorem rearm3P_run (G g : ℕ) (hg : g ≤ G) (N a c P : ℕ) (hP : 0 < P) (E : List Bool) :
    run rearm3PMachine (2 * G + 2 * N + 2 * a + 2 * c + 2 * P + 10)
      (init rearm3PMachine
        (cntT G g ++ (unaryD N ++ (unaryD a ++ (unaryD c ++ (jT P P ++ E))))))
      = ⟨(13, false), 2 * G + 2 * N + 2 * a + 2 * c + 2 * P + 9,
          cntT G g ++ (unaryD N ++ (unaryD a ++ (unaryD c ++ (jT P 0 ++ E))))⟩ := by
  have hW : (cntT G g).length = 2 * G + 2 := cntT_length G g hg
  have hQ : (unaryD N).length = 2 * N + 2 := unaryD_length N
  have hR : (unaryD a).length = 2 * a + 2 := unaryD_length a
  have hS : (unaryD c).length = 2 * c + 2 := unaryD_length c
  have f0 := r3p_skipWs (cntT G g ++ (unaryD N ++ (unaryD a ++ (unaryD c
      ++ (jT P P ++ E))))) 0 G false
    (fun i hi => by simpa using cntE_lo G g _ i hg hi)
  simp only [Nat.zero_add] at f0
  have f0' := r3p_crossW (s := if G = 0 then false else true) (p := 2 * G)
    (T := cntT G g ++ (unaryD N ++ (unaryD a ++ (unaryD c ++ (jT P P ++ E)))))
    (cntE_cm_lo G g _ hg) (cntE_cm_hi G g _ hg)
  have f1 := r3p_skipR1s (cntT G g ++ (unaryD N ++ (unaryD a ++ (unaryD c
      ++ (jT P P ++ E))))) (2 * G + 2) N false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * i = 2 * G + 2 + (2 * i) from rfl, ← cntT_zero N]
      exact liftJ _ _ hW (cntE_lo N 0 _ i (by omega) hi))
  have f2 := r3p_crossR1 (s := if N = 0 then false else true) (p := 2 * G + 2 + 2 * N)
    (T := cntT G g ++ (unaryD N ++ (unaryD a ++ (unaryD c ++ (jT P P ++ E)))))
    (by rw [show 2 * G + 2 + 2 * N = 2 * G + 2 + (2 * N) from rfl, ← cntT_zero N]
        exact liftJ _ _ hW (cntE_cm_lo N 0 _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 1 = 2 * G + 2 + (2 * N + 1) from by omega,
        ← cntT_zero N]
        exact liftJ _ _ hW (cntE_cm_hi N 0 _ (by omega)))
  have f3 := r3p_skipR2s (cntT G g ++ (unaryD N ++ (unaryD a ++ (unaryD c
      ++ (jT P P ++ E))))) (2 * G + 2 + 2 * N + 2) a false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * i = 2 * G + 2 + (2 * N + 2 + 2 * i)
          from by omega, ← cntT_zero a]
      exact liftJ2 _ _ _ hW hQ (cntE_lo a 0 _ i (by omega) hi))
  have f4 := r3p_crossR2 (s := if a = 0 then false else true)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * a)
    (T := cntT G g ++ (unaryD N ++ (unaryD a ++ (unaryD c ++ (jT P P ++ E)))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a = 2 * G + 2 + (2 * N + 2 + 2 * a)
          from by omega, ← cntT_zero a]
        exact liftJ2 _ _ _ hW hQ (cntE_cm_lo a 0 _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 1 = 2 * G + 2 + (2 * N + 2 + (2 * a + 1))
          from by omega, ← cntT_zero a]
        exact liftJ2 _ _ _ hW hQ (cntE_cm_hi a 0 _ (by omega)))
  have f5 := r3p_skipR3s (cntT G g ++ (unaryD N ++ (unaryD a ++ (unaryD c
      ++ (jT P P ++ E))))) (2 * G + 2 + 2 * N + 2 + 2 * a + 2) c false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * i
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + 2 * i)) from by omega, ← cntT_zero c]
      exact liftJ3 _ _ _ _ hW hQ hR (cntE_lo c 0 _ i (by omega) hi))
  have f6 := r3p_crossR3 (s := if c = 0 then false else true)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c)
    (T := cntT G g ++ (unaryD N ++ (unaryD a ++ (unaryD c ++ (jT P P ++ E)))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + 2 * c)) from by omega, ← cntT_zero c]
        exact liftJ3 _ _ _ _ hW hQ hR (cntE_cm_lo c 0 _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 1
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 1))) from by omega,
        ← cntT_zero c]
        exact liftJ3 _ _ _ _ hW hQ hR (cntE_cm_hi c 0 _ (by omega)))
  have f7 := r3p_two_head (s := false)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2)
    (T := cntT G g ++ (unaryD N ++ (unaryD a ++ (unaryD c ++ (jT P P ++ E)))))
  have hw7 : writeAt (writeAt (cntT G g ++ (unaryD N ++ (unaryD a ++ (unaryD c
      ++ (jT P P ++ E))))) (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2) false)
      (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 1) true
      = cntT G g ++ (unaryD N ++ (unaryD a ++ (unaryD c ++ (zeroT P 0 ++ E)))) := by
    rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2
        = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 2 + 0))) from by omega,
      W2_append_right4 (cntT G g) (unaryD N) (unaryD a) (unaryD c) _ (2 * G + 2)
        (2 * N + 2) (2 * a + 2) (2 * c + 2) 0 false true hW hQ hR hS
        (by rw [List.length_append, jT_length P P (le_refl P)]; omega)]
    rw [show (0 : ℕ) + 1 = 1 from rfl, zeroT_head P E hP]
  rw [hw7] at f7
  have f8 := r3p_zeros (cntT G g) (unaryD N) (unaryD a) (unaryD c) G N a c P E hW hQ hR hS
    hP false (P - 1) (le_refl _)
  have hlo9 : (cntT G g ++ (unaryD N ++ (unaryD a ++ (unaryD c
      ++ (zeroT P (P - 1) ++ E))))).getD
      (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 + 2 * (P - 1)) false = false := by
    rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 + 2 * (P - 1)
        = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 2 + 2 * P))) from by omega]
    exact liftJ4 _ _ _ _ _ hW hQ hR hS (zeroE_m_lo P E hP)
  have f9 := r3p_two_last (s := if P - 1 = 0 then false else true)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 + 2 * (P - 1))
    (T := cntT G g ++ (unaryD N ++ (unaryD a ++ (unaryD c ++ (zeroT P (P - 1) ++ E)))))
    hlo9
  have hw9 : writeAt (writeAt (cntT G g ++ (unaryD N ++ (unaryD a ++ (unaryD c
      ++ (zeroT P (P - 1) ++ E)))))
      (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 + 2 * (P - 1)) false)
      (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 + 2 * (P - 1) + 1) false
      = cntT G g ++ (unaryD N ++ (unaryD a ++ (unaryD c ++ (jT P 0 ++ E)))) := by
    rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 + 2 * (P - 1)
        = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 2 + 2 * P))) from by omega,
      W2_append_right4 (cntT G g) (unaryD N) (unaryD a) (unaryD c) _ (2 * G + 2)
        (2 * N + 2) (2 * a + 2) (2 * c + 2) (2 * P) false false hW hQ hR hS
        (by rw [List.length_append, zeroT_length P (P - 1) (le_refl _) hP]; omega),
      zeroT_last P E hP]
  rw [hw9] at f9
  rw [init_r3p,
    show 2 * G + 2 * N + 2 * a + 2 * c + 2 * P + 10
      = 2 * G + (2 + (2 * N + (2 + (2 * a + (2 + (2 * c + (2 + (2 + (2 * (P - 1) + 2)))))))))
      from by omega,
    run_add, f0, run_add, f0', run_add, f1, run_add, f2, run_add, f3, run_add, f4,
    run_add, f5, run_add, f6, run_add, f7, run_add, f8, f9,
    show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 + 2 * (P - 1) + 1
      = 2 * G + 2 * N + 2 * a + 2 * c + 2 * P + 9 from by omega]

theorem rearm3P_halt : rearm3PMachine.halt ((13 : Fin 14), false) = true := rfl

/-! ## THE PREFIXED CHAIN DEMONSTRATION

Two real families through one machine UNDER THE GRAND PREFIX: the prefixed tape-copy emitter, the
prefixed re-armer, and the prefixed write emitter — `seq_run` applied twice.  This is the per-`t`
body pattern for the grand loop. -/

/-- **A prefixed two-family chain**: `cellCopyP ⨟ rearm2P ⨟ writeP` emits both families' clause
streams in order under the grand prefix, self-halting at the explicit summed clock. -/
theorem familyP_chain_run (G g : ℕ) (hg : g ≤ G) (qi : ℕ) (b wb : Bool) (t P : ℕ)
    (out : List Bool) :
    run (seqMachine (seqMachine (loopProg2PMachine cellCopyBody) rearm2PMachine)
          (loopProg2PMachine (writeBody qi b wb)))
      ((lp2pClock cellCopyBody G (P + 1) t out.length + 1
          + (2 * G + 2 * (P + 1) + 2 * t + 2 * (P + 1) + 8)) + 1
        + lp2pClock (writeBody qi b wb) G (P + 1) t
            (out ++ ((List.range (P + 1)).map (fun p =>
              encodeClause' [(headVar t p, true), (cellVar (t + 1) p, false),
                (cellVar t p, true)]
                ++ encodeClause' [(headVar t p, true), (cellVar (t + 1) p, true),
                     (cellVar t p, false)])).flatten).length)
      (init (seqMachine (seqMachine (loopProg2PMachine cellCopyBody) rearm2PMachine)
          (loopProg2PMachine (writeBody qi b wb)))
        (cntT G g ++ (unaryD (P + 1) ++ (unaryD t ++ (jT (P + 1) 0 ++ encodeD out)))))
      = ⟨Sum.inr (94, ⟨0, Nat.succ_pos _⟩, false), 2 * G + 2 + 2 * (P + 1) + 1,
          cntT G g ++ (unaryD (P + 1) ++ (unaryD t ++ (unaryD (P + 1) ++ encodeD
            ((out ++ ((List.range (P + 1)).map (fun p =>
                encodeClause' [(headVar t p, true), (cellVar (t + 1) p, false),
                  (cellVar t p, true)]
                  ++ encodeClause' [(headVar t p, true), (cellVar (t + 1) p, true),
                       (cellVar t p, false)])).flatten)
              ++ ((List.range (P + 1)).map (fun p =>
                encodeClause' (implClause (stateVar t qi, true) (headVar t p, true)
                  (cellVar t p, b) (cellVar (t + 1) p, wb)))).flatten))))⟩ := by
  have hrearm := rearm2P_run G g hg (P + 1) t (P + 1) (by omega)
    (encodeD (out ++ ((List.range (P + 1)).map (fun p =>
      encodeClause' [(headVar t p, true), (cellVar (t + 1) p, false), (cellVar t p, true)]
        ++ encodeClause' [(headVar t p, true), (cellVar (t + 1) p, true),
             (cellVar t p, false)])).flatten))
  rw [jT_full] at hrearm
  have hwrite := loopProg2P_run (writeBody qi b wb) G g hg (P + 1) t
    (out ++ ((List.range (P + 1)).map (fun p =>
      encodeClause' [(headVar t p, true), (cellVar (t + 1) p, false), (cellVar t p, true)]
        ++ encodeClause' [(headVar t p, true), (cellVar (t + 1) p, true),
             (cellVar t p, false)])).flatten)
  rw [write_split] at hwrite
  exact seq_run _ _ _ _ _ _ _ _ _ _ _
    (seq_run _ _ _ _ _ _ _ _ _ _ _
      (cellCopyP_family_run G g hg t P out) rfl hrearm rfl)
    (seq_halt_final _ _ _ rfl)
    hwrite rfl

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitRearmP