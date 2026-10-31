import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitSeq

/-!
# Cook–Levin M2 emitter — the interstitial counter-management machines

A finished loop-engine run leaves its live variable **saturated** (`jT N N = unaryD N`); chaining
another loop run over the same layout needs it re-armed to `jT N 0`.  This file builds the two
re-armers — `rearm2Machine` for the two-source layout (variable in the third region) and
`rearm3Machine` for the triple-source layout (fourth region) — as tiny standalone machines consuming
the E4-iv zeroing algebra (`zeroT_head`/`zeroT_step`/`zeroT_last`): walk to the variable region, zero
it in place (the walk discriminates its own termination by the stage-`m` low cell: `true` at a data
pair, `false` at the old marker), halt.  Both leave every other region untouched, with any suffix.

**The payoff is the chain demonstration** `family_chain_run`: the tape-copy family emitter, the
re-armer, and the write family emitter — composed by `seq_run` twice into **one machine** — emit both
families' clause streams in order at time `t`, at the explicit summed clock.  This is the E6 assembly
pattern in miniature: engine runs chain whenever their tape interfaces meet, and the interstitial
machines are what make loop engines meet.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitRearm

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
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitFamilyBodies
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSeq

/-! ## A two-write lift under three prefixes -/

theorem W2_append_right3 (A B C X : List Bool) (qa qb qc p : ℕ) (b1 b2 : Bool)
    (ha : A.length = qa) (hb : B.length = qb) (hc : C.length = qc) (hp : p + 1 < X.length) :
    writeAt (writeAt (A ++ (B ++ (C ++ X))) (qa + (qb + (qc + p))) b1)
        (qa + (qb + (qc + p)) + 1) b2
      = A ++ (B ++ (C ++ writeAt (writeAt X p b1) (p + 1) b2)) := by
  have hl1 : (writeAt X p b1).length = X.length := by
    rw [writeAt_of_lt b1 (by omega), List.length_set]
  rw [writeAt_append_right3 A B C X qa qb qc p b1 ha hb hc (by omega),
    show qa + (qb + (qc + p)) + 1 = qa + (qb + (qc + (p + 1))) from by omega,
    writeAt_append_right3 A B C _ qa qb qc (p + 1) b2 ha hb hc (by rw [hl1]; omega)]

/-! ## The two-source re-armer

Layout `unaryD N ++ (unaryD a ++ (jT P P ++ E))`: skip the two counters, zero the variable, halt. -/

def rearm2Machine : Machine where
  State := Fin 10 × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, false)
  halt := fun s => decide (s.1 = 9)
  δ := fun s b =>
    if s.1 = 0 then ((1, b), none, 1)
    else if s.1 = 1 then
      (if s.2 then ((0, s.2), none, 1)
       else (if b then ((2, s.2), none, 1) else ((9, s.2), none, 2)))
    else if s.1 = 2 then ((3, b), none, 1)
    else if s.1 = 3 then
      (if s.2 then ((2, s.2), none, 1)
       else (if b then ((4, s.2), none, 1) else ((9, s.2), none, 2)))
    else if s.1 = 4 then ((5, s.2), some false, 1)
    else if s.1 = 5 then ((6, s.2), some true, 1)
    else if s.1 = 6 then
      (if b then ((7, b), some false, 1) else ((8, b), some false, 1))
    else if s.1 = 7 then ((6, s.2), some false, 1)
    else if s.1 = 8 then ((9, s.2), some false, 2)
    else ((s.1, s.2), none, 2)
  accept := fun _ => false

theorem init_r2 (t : List Bool) : init rearm2Machine t = ⟨(0, false), 0, t⟩ := rfl

section StepsR2
variable {s : Bool} {p : ℕ} {T : List Bool}

theorem r2_skipR1 (h1 : T.getD p false = true) :
    run rearm2Machine 2 ⟨(0, s), p, T⟩ = ⟨(0, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rearm2Machine ⟨(0, s), p, T⟩ = ⟨(1, T.getD p false), p + 1, T⟩ := by
    simp only [step, rearm2Machine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, rearm2Machine, moveHead]; rfl

theorem r2_crossR1 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run rearm2Machine 2 ⟨(0, s), p, T⟩ = ⟨(2, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rearm2Machine ⟨(0, s), p, T⟩ = ⟨(1, T.getD p false), p + 1, T⟩ := by
    simp only [step, rearm2Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, rearm2Machine, moveHead, h2]

theorem r2_skipR2 (h1 : T.getD p false = true) :
    run rearm2Machine 2 ⟨(2, s), p, T⟩ = ⟨(2, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rearm2Machine ⟨(2, s), p, T⟩ = ⟨(3, T.getD p false), p + 1, T⟩ := by
    simp only [step, rearm2Machine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, rearm2Machine, moveHead]; rfl

theorem r2_crossR2 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run rearm2Machine 2 ⟨(2, s), p, T⟩ = ⟨(4, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rearm2Machine ⟨(2, s), p, T⟩ = ⟨(3, T.getD p false), p + 1, T⟩ := by
    simp only [step, rearm2Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, rearm2Machine, moveHead, h2]

/-- The zeroing head-pair: `false, true` blind writes. -/
theorem r2_two_head :
    run rearm2Machine 2 ⟨(4, s), p, T⟩
      = ⟨(6, s), p + 2, writeAt (writeAt T p false) (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e4 : step rearm2Machine ⟨(4, s), p, T⟩ = ⟨(5, s), p + 1, writeAt T p false⟩ := by
    simp only [step, rearm2Machine, moveHead]; rfl
  have e5 : ∀ p' T', step rearm2Machine ⟨(5, s), p', T'⟩
      = ⟨(6, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, rearm2Machine, moveHead]; rfl
  rw [e4, e5]

/-- A zeroing step-pair: the stage's low cell reads `true` (a data pair remains). -/
theorem r2_two_step (h : T.getD p false = true) :
    run rearm2Machine 2 ⟨(6, s), p, T⟩
      = ⟨(6, true), p + 2, writeAt (writeAt T p false) (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e6 : step rearm2Machine ⟨(6, s), p, T⟩ = ⟨(7, true), p + 1, writeAt T p false⟩ := by
    have h' := h
    rw [List.getD_eq_getElem?_getD] at h'
    simp [step, rearm2Machine, moveHead, h']
  rw [e6]
  simp only [step, rearm2Machine, moveHead]; rfl

/-- The zeroing last-pair: the low cell reads `false` (the old marker) — write and halt. -/
theorem r2_two_last (h : T.getD p false = false) :
    run rearm2Machine 2 ⟨(6, s), p, T⟩
      = ⟨(9, false), p + 1, writeAt (writeAt T p false) (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e6 : step rearm2Machine ⟨(6, s), p, T⟩ = ⟨(8, false), p + 1, writeAt T p false⟩ := by
    have h' := h
    rw [List.getD_eq_getElem?_getD] at h'
    simp [step, rearm2Machine, moveHead, h']
  rw [e6]
  simp only [step, rearm2Machine, moveHead]; rfl

end StepsR2

theorem r2_skipR1s (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run rearm2Machine (2 * k) ⟨(0, s), q, T⟩
      = ⟨(0, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), r2_skipR1 (h k (by omega))]
    rfl

theorem r2_skipR2s (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run rearm2Machine (2 * k) ⟨(2, s), q, T⟩
      = ⟨(2, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), r2_skipR2 (h k (by omega))]
    rfl

/-- The zeroing walk (evolving `zeroT`, two prefixes). -/
theorem r2_zeros (Q R : List Bool) (N a P : ℕ) (E : List Bool)
    (hQ : Q.length = 2 * N + 2) (hR : R.length = 2 * a + 2) (hP : 0 < P) (s : Bool)
    (m : ℕ) (hm : m ≤ P - 1) :
    run rearm2Machine (2 * m) ⟨(6, s), 2 * N + 2 + 2 * a + 2 + 2, Q ++ (R ++ (zeroT P 0 ++ E))⟩
      = ⟨(6, if m = 0 then s else true), 2 * N + 2 + 2 * a + 2 + 2 + 2 * m,
          Q ++ (R ++ (zeroT P m ++ E))⟩ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hlo : (Q ++ (R ++ (zeroT P m ++ E))).getD
        (2 * N + 2 + 2 * a + 2 + 2 + 2 * m) false = true := by
      rw [show 2 * N + 2 + 2 * a + 2 + 2 + 2 * m = 2 * N + 2 + (2 * a + 2 + 2 * (m + 1))
          from by omega]
      exact liftJ2 _ _ _ hQ hR (zeroE_data_lo P m E (by omega))
    have hw : writeAt (writeAt (Q ++ (R ++ (zeroT P m ++ E)))
        (2 * N + 2 + 2 * a + 2 + 2 + 2 * m) false)
        (2 * N + 2 + 2 * a + 2 + 2 + 2 * m + 1) false
        = Q ++ (R ++ (zeroT P (m + 1) ++ E)) := by
      rw [show 2 * N + 2 + 2 * a + 2 + 2 + 2 * m = 2 * N + 2 + (2 * a + 2 + 2 * (m + 1))
          from by omega,
        W2_append_right2 Q R _ (2 * N + 2) (2 * a + 2) (2 * (m + 1)) false false hQ hR
          (by rw [List.length_append, zeroT_length P m (by omega) hP]; omega),
        zeroT_step P m E (by omega)]
    rw [show 2 * (m + 1) = 2 * m + 2 from by ring, run_add, ih (by omega),
      r2_two_step hlo, hw]
    rfl

/-- **The two-source re-armer**: on any tape `unaryD N ++ (unaryD a ++ (jT P P ++ E))` it halts by
itself at the explicit clock having zeroed the variable — `jT P 0` — with everything else untouched. -/
theorem rearm2_run (N a P : ℕ) (hP : 0 < P) (E : List Bool) :
    run rearm2Machine (2 * N + 2 * a + 2 * P + 6)
      (init rearm2Machine (unaryD N ++ (unaryD a ++ (jT P P ++ E))))
      = ⟨(9, false), 2 * N + 2 * a + 2 * P + 5,
          unaryD N ++ (unaryD a ++ (jT P 0 ++ E))⟩ := by
  have hQ : (unaryD N).length = 2 * N + 2 := unaryD_length N
  have hR : (unaryD a).length = 2 * a + 2 := unaryD_length a
  have f1 := r2_skipR1s (unaryD N ++ (unaryD a ++ (jT P P ++ E))) 0 N false
    (fun i hi => by
      rw [show 0 + 2 * i = 2 * i from by omega, ← cntT_zero N]
      exact cntE_lo N 0 _ i (by omega) hi)
  simp only [Nat.zero_add] at f1
  have f2 := r2_crossR1 (s := if N = 0 then false else true) (p := 2 * N)
    (T := unaryD N ++ (unaryD a ++ (jT P P ++ E)))
    (by rw [← cntT_zero N]; exact cntE_cm_lo N 0 _ (by omega))
    (by rw [show 2 * N + 1 = 2 * N + 1 from rfl, ← cntT_zero N]
        exact cntE_cm_hi N 0 _ (by omega))
  have f3 := r2_skipR2s (unaryD N ++ (unaryD a ++ (jT P P ++ E))) (2 * N + 2) a false
    (fun i hi => by
      rw [show 2 * N + 2 + 2 * i = 2 * N + 2 + (2 * i) from rfl, ← cntT_zero a]
      exact liftJ _ _ hQ (cntE_lo a 0 _ i (by omega) hi))
  have f4 := r2_crossR2 (s := if a = 0 then false else true) (p := 2 * N + 2 + 2 * a)
    (T := unaryD N ++ (unaryD a ++ (jT P P ++ E)))
    (by rw [show 2 * N + 2 + 2 * a = 2 * N + 2 + (2 * a) from rfl, ← cntT_zero a]
        exact liftJ _ _ hQ (cntE_cm_lo a 0 _ (by omega)))
    (by rw [show 2 * N + 2 + 2 * a + 1 = 2 * N + 2 + (2 * a + 1) from by omega, ← cntT_zero a]
        exact liftJ _ _ hQ (cntE_cm_hi a 0 _ (by omega)))
  have f5 := r2_two_head (s := false) (p := 2 * N + 2 + 2 * a + 2)
    (T := unaryD N ++ (unaryD a ++ (jT P P ++ E)))
  have hw5 : writeAt (writeAt (unaryD N ++ (unaryD a ++ (jT P P ++ E)))
      (2 * N + 2 + 2 * a + 2) false) (2 * N + 2 + 2 * a + 2 + 1) true
      = unaryD N ++ (unaryD a ++ (zeroT P 0 ++ E)) := by
    rw [show 2 * N + 2 + 2 * a + 2 = 2 * N + 2 + (2 * a + 2 + 0) from by omega,
      W2_append_right2 (unaryD N) (unaryD a) _ (2 * N + 2) (2 * a + 2) 0 false true hQ hR
        (by rw [List.length_append, jT_length P P (le_refl P)]; omega)]
    rw [show (0 : ℕ) + 1 = 1 from rfl, zeroT_head P E hP]
  rw [hw5] at f5
  have f6 := r2_zeros (unaryD N) (unaryD a) N a P E hQ hR hP false (P - 1) (le_refl _)
  have hlo7 : (unaryD N ++ (unaryD a ++ (zeroT P (P - 1) ++ E))).getD
      (2 * N + 2 + 2 * a + 2 + 2 + 2 * (P - 1)) false = false := by
    rw [show 2 * N + 2 + 2 * a + 2 + 2 + 2 * (P - 1) = 2 * N + 2 + (2 * a + 2 + 2 * P)
        from by omega]
    exact liftJ2 _ _ _ hQ hR (zeroE_m_lo P E hP)
  have f7 := r2_two_last (s := if P - 1 = 0 then false else true)
    (p := 2 * N + 2 + 2 * a + 2 + 2 + 2 * (P - 1))
    (T := unaryD N ++ (unaryD a ++ (zeroT P (P - 1) ++ E))) hlo7
  have hw7 : writeAt (writeAt (unaryD N ++ (unaryD a ++ (zeroT P (P - 1) ++ E)))
      (2 * N + 2 + 2 * a + 2 + 2 + 2 * (P - 1)) false)
      (2 * N + 2 + 2 * a + 2 + 2 + 2 * (P - 1) + 1) false
      = unaryD N ++ (unaryD a ++ (jT P 0 ++ E)) := by
    rw [show 2 * N + 2 + 2 * a + 2 + 2 + 2 * (P - 1) = 2 * N + 2 + (2 * a + 2 + 2 * P)
        from by omega,
      W2_append_right2 (unaryD N) (unaryD a) _ (2 * N + 2) (2 * a + 2) (2 * P) false false
        hQ hR (by rw [List.length_append, zeroT_length P (P - 1) (le_refl _) hP]; omega),
      zeroT_last P E hP]
  rw [hw7] at f7
  rw [init_r2,
    show 2 * N + 2 * a + 2 * P + 6
      = 2 * N + (2 + (2 * a + (2 + (2 + (2 * (P - 1) + 2))))) from by omega,
    run_add, f1, run_add, f2, run_add, f3, run_add, f4, run_add, f5, run_add, f6, f7,
    show 2 * N + 2 + 2 * a + 2 + 2 + 2 * (P - 1) + 1 = 2 * N + 2 * a + 2 * P + 5
      from by omega]

theorem rearm2_halt : rearm2Machine.halt ((9 : Fin 10), false) = true := rfl

/-! ## The triple-source re-armer

Layout `unaryD N ++ (unaryD a ++ (unaryD c ++ (jT P P ++ E)))`: one more skip pair. -/

def rearm3Machine : Machine where
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

theorem init_r3 (t : List Bool) : init rearm3Machine t = ⟨(0, false), 0, t⟩ := rfl

section StepsR3
variable {s : Bool} {p : ℕ} {T : List Bool}

theorem r3_skipR1 (h1 : T.getD p false = true) :
    run rearm3Machine 2 ⟨(0, s), p, T⟩ = ⟨(0, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rearm3Machine ⟨(0, s), p, T⟩ = ⟨(1, T.getD p false), p + 1, T⟩ := by
    simp only [step, rearm3Machine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, rearm3Machine, moveHead]; rfl

theorem r3_skipR2 (h1 : T.getD p false = true) :
    run rearm3Machine 2 ⟨(2, s), p, T⟩ = ⟨(2, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rearm3Machine ⟨(2, s), p, T⟩ = ⟨(3, T.getD p false), p + 1, T⟩ := by
    simp only [step, rearm3Machine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, rearm3Machine, moveHead]; rfl

theorem r3_skipR3 (h1 : T.getD p false = true) :
    run rearm3Machine 2 ⟨(4, s), p, T⟩ = ⟨(4, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rearm3Machine ⟨(4, s), p, T⟩ = ⟨(5, T.getD p false), p + 1, T⟩ := by
    simp only [step, rearm3Machine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, rearm3Machine, moveHead]; rfl

theorem r3_crossR1 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run rearm3Machine 2 ⟨(0, s), p, T⟩ = ⟨(2, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rearm3Machine ⟨(0, s), p, T⟩ = ⟨(1, T.getD p false), p + 1, T⟩ := by
    simp only [step, rearm3Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, rearm3Machine, moveHead, h2]

theorem r3_crossR2 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run rearm3Machine 2 ⟨(2, s), p, T⟩ = ⟨(4, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rearm3Machine ⟨(2, s), p, T⟩ = ⟨(3, T.getD p false), p + 1, T⟩ := by
    simp only [step, rearm3Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, rearm3Machine, moveHead, h2]

theorem r3_crossR3 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run rearm3Machine 2 ⟨(4, s), p, T⟩ = ⟨(6, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rearm3Machine ⟨(4, s), p, T⟩ = ⟨(5, T.getD p false), p + 1, T⟩ := by
    simp only [step, rearm3Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, rearm3Machine, moveHead, h2]

theorem r3_two_head :
    run rearm3Machine 2 ⟨(6, s), p, T⟩
      = ⟨(8, s), p + 2, writeAt (writeAt T p false) (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e6 : step rearm3Machine ⟨(6, s), p, T⟩ = ⟨(7, s), p + 1, writeAt T p false⟩ := by
    simp only [step, rearm3Machine, moveHead]; rfl
  have e7 : ∀ p' T', step rearm3Machine ⟨(7, s), p', T'⟩
      = ⟨(8, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, rearm3Machine, moveHead]; rfl
  rw [e6, e7]

theorem r3_two_step (h : T.getD p false = true) :
    run rearm3Machine 2 ⟨(8, s), p, T⟩
      = ⟨(8, true), p + 2, writeAt (writeAt T p false) (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e8 : step rearm3Machine ⟨(8, s), p, T⟩ = ⟨(9, true), p + 1, writeAt T p false⟩ := by
    have h' := h
    rw [List.getD_eq_getElem?_getD] at h'
    simp [step, rearm3Machine, moveHead, h']
  rw [e8]
  simp only [step, rearm3Machine, moveHead]; rfl

theorem r3_two_last (h : T.getD p false = false) :
    run rearm3Machine 2 ⟨(8, s), p, T⟩
      = ⟨(11, false), p + 1, writeAt (writeAt T p false) (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e8 : step rearm3Machine ⟨(8, s), p, T⟩ = ⟨(10, false), p + 1, writeAt T p false⟩ := by
    have h' := h
    rw [List.getD_eq_getElem?_getD] at h'
    simp [step, rearm3Machine, moveHead, h']
  rw [e8]
  simp only [step, rearm3Machine, moveHead]; rfl

end StepsR3

theorem r3_skipR1s (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run rearm3Machine (2 * k) ⟨(0, s), q, T⟩
      = ⟨(0, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), r3_skipR1 (h k (by omega))]
    rfl

theorem r3_skipR2s (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run rearm3Machine (2 * k) ⟨(2, s), q, T⟩
      = ⟨(2, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), r3_skipR2 (h k (by omega))]
    rfl

theorem r3_skipR3s (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run rearm3Machine (2 * k) ⟨(4, s), q, T⟩
      = ⟨(4, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), r3_skipR3 (h k (by omega))]
    rfl

/-- The zeroing walk (evolving `zeroT`, three prefixes). -/
theorem r3_zeros (Q R S : List Bool) (N a c P : ℕ) (E : List Bool)
    (hQ : Q.length = 2 * N + 2) (hR : R.length = 2 * a + 2) (hS : S.length = 2 * c + 2)
    (hP : 0 < P) (s : Bool) (m : ℕ) (hm : m ≤ P - 1) :
    run rearm3Machine (2 * m)
      ⟨(8, s), 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2, Q ++ (R ++ (S ++ (zeroT P 0 ++ E)))⟩
      = ⟨(8, if m = 0 then s else true), 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 + 2 * m,
          Q ++ (R ++ (S ++ (zeroT P m ++ E)))⟩ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hlo : (Q ++ (R ++ (S ++ (zeroT P m ++ E)))).getD
        (2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 + 2 * m) false = true := by
      rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 + 2 * m
          = 2 * N + 2 + (2 * a + 2 + (2 * c + 2 + 2 * (m + 1))) from by omega]
      exact liftJ3 _ _ _ _ hQ hR hS (zeroE_data_lo P m E (by omega))
    have hw : writeAt (writeAt (Q ++ (R ++ (S ++ (zeroT P m ++ E))))
        (2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 + 2 * m) false)
        (2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 + 2 * m + 1) false
        = Q ++ (R ++ (S ++ (zeroT P (m + 1) ++ E))) := by
      rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 + 2 * m
          = 2 * N + 2 + (2 * a + 2 + (2 * c + 2 + 2 * (m + 1))) from by omega,
        W2_append_right3 Q R S _ (2 * N + 2) (2 * a + 2) (2 * c + 2) (2 * (m + 1))
          false false hQ hR hS
          (by rw [List.length_append, zeroT_length P m (by omega) hP]; omega),
        zeroT_step P m E (by omega)]
    rw [show 2 * (m + 1) = 2 * m + 2 from by ring, run_add, ih (by omega),
      r3_two_step hlo, hw]
    rfl

/-- **The triple-source re-armer**: zero the fourth-region variable, everything else untouched. -/
theorem rearm3_run (N a c P : ℕ) (hP : 0 < P) (E : List Bool) :
    run rearm3Machine (2 * N + 2 * a + 2 * c + 2 * P + 8)
      (init rearm3Machine (unaryD N ++ (unaryD a ++ (unaryD c ++ (jT P P ++ E)))))
      = ⟨(11, false), 2 * N + 2 * a + 2 * c + 2 * P + 7,
          unaryD N ++ (unaryD a ++ (unaryD c ++ (jT P 0 ++ E)))⟩ := by
  have hQ : (unaryD N).length = 2 * N + 2 := unaryD_length N
  have hR : (unaryD a).length = 2 * a + 2 := unaryD_length a
  have hS : (unaryD c).length = 2 * c + 2 := unaryD_length c
  have f1 := r3_skipR1s (unaryD N ++ (unaryD a ++ (unaryD c ++ (jT P P ++ E))))
    0 N false
    (fun i hi => by
      rw [show 0 + 2 * i = 2 * i from by omega, ← cntT_zero N]
      exact cntE_lo N 0 _ i (by omega) hi)
  simp only [Nat.zero_add] at f1
  have f2 := r3_crossR1 (s := if N = 0 then false else true) (p := 2 * N)
    (T := unaryD N ++ (unaryD a ++ (unaryD c ++ (jT P P ++ E))))
    (by rw [← cntT_zero N]; exact cntE_cm_lo N 0 _ (by omega))
    (by rw [show 2 * N + 1 = 2 * N + 1 from rfl, ← cntT_zero N]
        exact cntE_cm_hi N 0 _ (by omega))
  have f3 := r3_skipR2s (unaryD N ++ (unaryD a ++ (unaryD c ++ (jT P P ++ E))))
    (2 * N + 2) a false
    (fun i hi => by
      rw [show 2 * N + 2 + 2 * i = 2 * N + 2 + (2 * i) from rfl, ← cntT_zero a]
      exact liftJ _ _ hQ (cntE_lo a 0 _ i (by omega) hi))
  have f4 := r3_crossR2 (s := if a = 0 then false else true) (p := 2 * N + 2 + 2 * a)
    (T := unaryD N ++ (unaryD a ++ (unaryD c ++ (jT P P ++ E))))
    (by rw [show 2 * N + 2 + 2 * a = 2 * N + 2 + (2 * a) from rfl, ← cntT_zero a]
        exact liftJ _ _ hQ (cntE_cm_lo a 0 _ (by omega)))
    (by rw [show 2 * N + 2 + 2 * a + 1 = 2 * N + 2 + (2 * a + 1) from by omega, ← cntT_zero a]
        exact liftJ _ _ hQ (cntE_cm_hi a 0 _ (by omega)))
  have f5 := r3_skipR3s (unaryD N ++ (unaryD a ++ (unaryD c ++ (jT P P ++ E))))
    (2 * N + 2 + 2 * a + 2) c false
    (fun i hi => by
      rw [show 2 * N + 2 + 2 * a + 2 + 2 * i = 2 * N + 2 + (2 * a + 2 + 2 * i) from by omega,
        ← cntT_zero c]
      exact liftJ2 _ _ _ hQ hR (cntE_lo c 0 _ i (by omega) hi))
  have f6 := r3_crossR3 (s := if c = 0 then false else true)
    (p := 2 * N + 2 + 2 * a + 2 + 2 * c)
    (T := unaryD N ++ (unaryD a ++ (unaryD c ++ (jT P P ++ E))))
    (by rw [show 2 * N + 2 + 2 * a + 2 + 2 * c = 2 * N + 2 + (2 * a + 2 + 2 * c)
          from by omega, ← cntT_zero c]
        exact liftJ2 _ _ _ hQ hR (cntE_cm_lo c 0 _ (by omega)))
    (by rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 1 = 2 * N + 2 + (2 * a + 2 + (2 * c + 1))
          from by omega, ← cntT_zero c]
        exact liftJ2 _ _ _ hQ hR (cntE_cm_hi c 0 _ (by omega)))
  have f7 := r3_two_head (s := false) (p := 2 * N + 2 + 2 * a + 2 + 2 * c + 2)
    (T := unaryD N ++ (unaryD a ++ (unaryD c ++ (jT P P ++ E))))
  have hw7 : writeAt (writeAt (unaryD N ++ (unaryD a ++ (unaryD c ++ (jT P P ++ E))))
      (2 * N + 2 + 2 * a + 2 + 2 * c + 2) false)
      (2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 1) true
      = unaryD N ++ (unaryD a ++ (unaryD c ++ (zeroT P 0 ++ E))) := by
    rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 = 2 * N + 2 + (2 * a + 2 + (2 * c + 2 + 0))
        from by omega,
      W2_append_right3 (unaryD N) (unaryD a) (unaryD c) _ (2 * N + 2) (2 * a + 2)
        (2 * c + 2) 0 false true hQ hR hS
        (by rw [List.length_append, jT_length P P (le_refl P)]; omega)]
    rw [show (0 : ℕ) + 1 = 1 from rfl, zeroT_head P E hP]
  rw [hw7] at f7
  have f8 := r3_zeros (unaryD N) (unaryD a) (unaryD c) N a c P E hQ hR hS hP false (P - 1)
    (le_refl _)
  have hlo9 : (unaryD N ++ (unaryD a ++ (unaryD c ++ (zeroT P (P - 1) ++ E)))).getD
      (2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 + 2 * (P - 1)) false = false := by
    rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 + 2 * (P - 1)
        = 2 * N + 2 + (2 * a + 2 + (2 * c + 2 + 2 * P)) from by omega]
    exact liftJ3 _ _ _ _ hQ hR hS (zeroE_m_lo P E hP)
  have f9 := r3_two_last (s := if P - 1 = 0 then false else true)
    (p := 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 + 2 * (P - 1))
    (T := unaryD N ++ (unaryD a ++ (unaryD c ++ (zeroT P (P - 1) ++ E)))) hlo9
  have hw9 : writeAt (writeAt (unaryD N ++ (unaryD a ++ (unaryD c ++ (zeroT P (P - 1) ++ E))))
      (2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 + 2 * (P - 1)) false)
      (2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 + 2 * (P - 1) + 1) false
      = unaryD N ++ (unaryD a ++ (unaryD c ++ (jT P 0 ++ E))) := by
    rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 + 2 * (P - 1)
        = 2 * N + 2 + (2 * a + 2 + (2 * c + 2 + 2 * P)) from by omega,
      W2_append_right3 (unaryD N) (unaryD a) (unaryD c) _ (2 * N + 2) (2 * a + 2)
        (2 * c + 2) (2 * P) false false hQ hR hS
        (by rw [List.length_append, zeroT_length P (P - 1) (le_refl _) hP]; omega),
      zeroT_last P E hP]
  rw [hw9] at f9
  rw [init_r3,
    show 2 * N + 2 * a + 2 * c + 2 * P + 8
      = 2 * N + (2 + (2 * a + (2 + (2 * c + (2 + (2 + (2 * (P - 1) + 2))))))) from by omega,
    run_add, f1, run_add, f2, run_add, f3, run_add, f4, run_add, f5, run_add, f6,
    run_add, f7, run_add, f8, f9,
    show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 + 2 * (P - 1) + 1
      = 2 * N + 2 * a + 2 * c + 2 * P + 7 from by omega]

theorem rearm3_halt : rearm3Machine.halt ((11 : Fin 12), false) = true := rfl

/-! ## THE CHAIN DEMONSTRATION

Two real families through one machine: the tape-copy family, the re-armer, and the write family at
time `t` — `seq_run` applied twice.  This is the E6 assembly pattern in miniature. -/

/-- **A two-family chain**: `cellCopy ⨟ rearm ⨟ write` emits both families' clause streams in order,
self-halting at the explicit summed clock. -/
theorem family_chain_run (qi : ℕ) (b wb : Bool) (t P : ℕ) (out : List Bool) :
    run (seqMachine (seqMachine (loopProg2Machine cellCopyBody) rearm2Machine)
          (loopProg2Machine (writeBody qi b wb)))
      ((lp2Clock cellCopyBody (P + 1) t out.length + 1
          + (2 * (P + 1) + 2 * t + 2 * (P + 1) + 6)) + 1
        + lp2Clock (writeBody qi b wb) (P + 1) t
            (out ++ ((List.range (P + 1)).map (fun p =>
              encodeClause' [(headVar t p, true), (cellVar (t + 1) p, false),
                (cellVar t p, true)]
                ++ encodeClause' [(headVar t p, true), (cellVar (t + 1) p, true),
                     (cellVar t p, false)])).flatten).length)
      (init (seqMachine (seqMachine (loopProg2Machine cellCopyBody) rearm2Machine)
          (loopProg2Machine (writeBody qi b wb)))
        (unaryD (P + 1) ++ (unaryD t ++ (jT (P + 1) 0 ++ encodeD out))))
      = ⟨Sum.inr (78, ⟨0, Nat.succ_pos _⟩, false), 2 * (P + 1) + 1,
          unaryD (P + 1) ++ (unaryD t ++ (unaryD (P + 1) ++ encodeD
            ((out ++ ((List.range (P + 1)).map (fun p =>
                encodeClause' [(headVar t p, true), (cellVar (t + 1) p, false),
                  (cellVar t p, true)]
                  ++ encodeClause' [(headVar t p, true), (cellVar (t + 1) p, true),
                       (cellVar t p, false)])).flatten)
              ++ ((List.range (P + 1)).map (fun p =>
                encodeClause' (implClause (stateVar t qi, true) (headVar t p, true)
                  (cellVar t p, b) (cellVar (t + 1) p, wb)))).flatten)))⟩ := by
  have hrearm := rearm2_run (P + 1) t (P + 1) (by omega)
    (encodeD (out ++ ((List.range (P + 1)).map (fun p =>
      encodeClause' [(headVar t p, true), (cellVar (t + 1) p, false), (cellVar t p, true)]
        ++ encodeClause' [(headVar t p, true), (cellVar (t + 1) p, true),
             (cellVar t p, false)])).flatten))
  rw [jT_full] at hrearm
  exact seq_run _ _ _ _ _ _ _ _ _ _ _
    (seq_run _ _ _ _ _ _ _ _ _ _ _
      (cellCopy_family_run t P out) rfl hrearm rfl)
    (seq_halt_final _ _ _ rfl)
    (write_family_run qi b wb t P _) rfl

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitRearm