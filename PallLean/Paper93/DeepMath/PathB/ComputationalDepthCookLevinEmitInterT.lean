import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitLoopProg2T
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitRep

/-!
# Cook–Levin M2 emitter — the mirror interstitial and THE LIVE-`t` GRAND CHAIN

Two deliverables close the grand-round design:

* **`interTMachine`** — the mirror interstitial: on the post-engine layout
  `cntT G g ++ (unaryD N ++ (jT C t ++ (jT N N ++ E)))` it makes ONE left-to-right pass — skip the
  grand counter, skip the bound, walk the mirror's filled pairs, apply the in-place four-write
  increment at the value marker (`jT_incr`: `jT C t ↦ jT C (t+1)`), cross the remaining padding,
  and zero the saturated live variable (`zeroT` walk: `jT N N ↦ jT N 0`) — then halts.  One tiny
  machine (`Fin 17`) re-arms BOTH counters for the next grand round.

* **`rep_liveChain_run`** — THE REAL PER-`t` GRAND CHAIN: `repMachine` over
  `seqMachine (loopProg2TMachine body) interTMachine` runs `B` grand rounds; round `t` emits the
  family stream **at the live index `t`** (read from the mirror) and the interstitial re-arms; the
  final tape carries `⋃_{t<B} loop2Out body t N` — the `t`-indexed family concatenation the tableau
  needs.  `rep_cellCopyLive_run` instantiates it with the real tape-copy family: every clause of
  every `cellCopyClause t p`, `t = 0..B-1`, `p = 0..P`, in tableau order, from ONE machine.
  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitInterT

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinCNFEncode
open PallLean.Paper93.DeepMath.PathB.CookLevinVarIndex
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
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRep

/-! ## The machine

`Fin 17 × Bool`: `0/1` skip the grand counter, `2/3` skip the bound, `4/5` walk the mirror's
filled pairs, `4(else),6,7,8` the four-write increment at the marker, `9/10` cross the remaining
padding, `11/12` the zeroing head pair, `13/14/15` the zeroing loop, `16` halt. -/

def interTMachine : Machine where
  State := Fin 17 × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, false)
  halt := fun s => decide (s.1 = 16)
  δ := fun s b =>
    if s.1 = 0 then ((1, b), none, 1)
    else if s.1 = 1 then
      (if s.2 then ((0, s.2), none, 1)
       else (if b then ((2, s.2), none, 1) else ((16, s.2), none, 2)))
    else if s.1 = 2 then ((3, b), none, 1)
    else if s.1 = 3 then
      (if s.2 then ((2, s.2), none, 1)
       else (if b then ((4, s.2), none, 1) else ((16, s.2), none, 2)))
    else if s.1 = 4 then
      (if b then ((5, b), none, 1) else ((6, s.2), some true, 1))
    else if s.1 = 5 then ((4, s.2), none, 1)
    else if s.1 = 6 then ((7, s.2), some true, 1)
    else if s.1 = 7 then ((8, s.2), some false, 1)
    else if s.1 = 8 then ((9, s.2), some true, 1)
    else if s.1 = 9 then ((10, b), none, 1)
    else if s.1 = 10 then
      (if s.2 then ((11, s.2), none, 0)
       else (if b then ((11, s.2), none, 0) else ((9, s.2), none, 1)))
    else if s.1 = 11 then ((12, s.2), some false, 1)
    else if s.1 = 12 then ((13, s.2), some true, 1)
    else if s.1 = 13 then
      (if b then ((14, b), some false, 1) else ((15, b), some false, 1))
    else if s.1 = 14 then ((13, s.2), some false, 1)
    else if s.1 = 15 then ((16, s.2), some false, 2)
    else ((s.1, s.2), none, 2)
  accept := fun _ => false

theorem init_it (t : List Bool) : init interTMachine t = ⟨(0, false), 0, t⟩ := rfl

/-! ## The step layer -/

section StepsIT
variable {s : Bool} {p : ℕ} {T : List Bool}

theorem it_skipW (h1 : T.getD p false = true) :
    run interTMachine 2 ⟨(0, s), p, T⟩ = ⟨(0, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step interTMachine ⟨(0, s), p, T⟩ = ⟨(1, T.getD p false), p + 1, T⟩ := by
    simp only [step, interTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, interTMachine, moveHead]; rfl

theorem it_crossW (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run interTMachine 2 ⟨(0, s), p, T⟩ = ⟨(2, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step interTMachine ⟨(0, s), p, T⟩ = ⟨(1, T.getD p false), p + 1, T⟩ := by
    simp only [step, interTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, interTMachine, moveHead, h2]

theorem it_skipR1 (h1 : T.getD p false = true) :
    run interTMachine 2 ⟨(2, s), p, T⟩ = ⟨(2, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step interTMachine ⟨(2, s), p, T⟩ = ⟨(3, T.getD p false), p + 1, T⟩ := by
    simp only [step, interTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, interTMachine, moveHead]; rfl

theorem it_crossR1 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run interTMachine 2 ⟨(2, s), p, T⟩ = ⟨(4, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step interTMachine ⟨(2, s), p, T⟩ = ⟨(3, T.getD p false), p + 1, T⟩ := by
    simp only [step, interTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, interTMachine, moveHead, h2]

theorem it_walk (h1 : T.getD p false = true) :
    run interTMachine 2 ⟨(4, s), p, T⟩ = ⟨(4, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step interTMachine ⟨(4, s), p, T⟩ = ⟨(5, true), p + 1, T⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, interTMachine, moveHead, h1']
  rw [e0]
  simp only [step, interTMachine, moveHead]; rfl

/-- The four-write increment at the mirror's marker. -/
theorem it_four_incr (h1 : T.getD p false = false) :
    run interTMachine 4 ⟨(4, s), p, T⟩
      = ⟨(9, s), p + 4, writeAt (writeAt (writeAt (writeAt T p true)
          (p + 1) true) (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e0 : step interTMachine ⟨(4, s), p, T⟩ = ⟨(6, s), p + 1, writeAt T p true⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, interTMachine, moveHead, h1']
  have e1 : ∀ p' T', step interTMachine ⟨(6, s), p', T'⟩
      = ⟨(7, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, interTMachine, moveHead]; rfl
  have e2 : ∀ p' T', step interTMachine ⟨(7, s), p', T'⟩
      = ⟨(8, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, interTMachine, moveHead]; rfl
  have e3 : ∀ p' T', step interTMachine ⟨(8, s), p', T'⟩
      = ⟨(9, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, interTMachine, moveHead]; rfl
  rw [e0, e1, e2, e3]

theorem it_pad (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = false) :
    run interTMachine 2 ⟨(9, s), p, T⟩ = ⟨(9, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step interTMachine ⟨(9, s), p, T⟩ = ⟨(10, T.getD p false), p + 1, T⟩ := by
    simp only [step, interTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, interTMachine, moveHead, h2]

theorem it_padBoundT (h1 : T.getD p false = true) :
    run interTMachine 2 ⟨(9, s), p, T⟩ = ⟨(11, true), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step interTMachine ⟨(9, s), p, T⟩ = ⟨(10, T.getD p false), p + 1, T⟩ := by
    simp only [step, interTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, interTMachine, moveHead]; rfl

theorem it_padBoundM (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run interTMachine 2 ⟨(9, s), p, T⟩ = ⟨(11, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step interTMachine ⟨(9, s), p, T⟩ = ⟨(10, T.getD p false), p + 1, T⟩ := by
    simp only [step, interTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, interTMachine, moveHead, h2]

/-- The zeroing head-pair: `false, true` blind writes. -/
theorem it_two_head {s' : Bool} :
    run interTMachine 2 ⟨(11, s'), p, T⟩
      = ⟨(13, s'), p + 2, writeAt (writeAt T p false) (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e4 : step interTMachine ⟨(11, s'), p, T⟩ = ⟨(12, s'), p + 1, writeAt T p false⟩ := by
    simp only [step, interTMachine, moveHead]; rfl
  have e5 : ∀ p' T', step interTMachine ⟨(12, s'), p', T'⟩
      = ⟨(13, s'), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, interTMachine, moveHead]; rfl
  rw [e4, e5]

theorem it_two_step (h : T.getD p false = true) :
    run interTMachine 2 ⟨(13, s), p, T⟩
      = ⟨(13, true), p + 2, writeAt (writeAt T p false) (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e6 : step interTMachine ⟨(13, s), p, T⟩ = ⟨(14, true), p + 1, writeAt T p false⟩ := by
    have h' := h
    rw [List.getD_eq_getElem?_getD] at h'
    simp [step, interTMachine, moveHead, h']
  rw [e6]
  simp only [step, interTMachine, moveHead]; rfl

theorem it_two_last (h : T.getD p false = false) :
    run interTMachine 2 ⟨(13, s), p, T⟩
      = ⟨(16, false), p + 1, writeAt (writeAt T p false) (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e6 : step interTMachine ⟨(13, s), p, T⟩
      = ⟨(15, false), p + 1, writeAt T p false⟩ := by
    have h' := h
    rw [List.getD_eq_getElem?_getD] at h'
    simp [step, interTMachine, moveHead, h']
  rw [e6]
  simp only [step, interTMachine, moveHead]; rfl

end StepsIT

theorem it_skipWs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run interTMachine (2 * k) ⟨(0, s), q, T⟩
      = ⟨(0, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), it_skipW (h k (by omega))]
    rfl

theorem it_skipR1s (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run interTMachine (2 * k) ⟨(2, s), q, T⟩
      = ⟨(2, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), it_skipR1 (h k (by omega))]
    rfl

theorem it_walks (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run interTMachine (2 * k) ⟨(4, s), q, T⟩
      = ⟨(4, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), it_walk (h k (by omega))]
    rfl

theorem it_pads (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = false
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run interTMachine (2 * k) ⟨(9, s), q, T⟩
      = ⟨(9, if k = 0 then s else false), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), it_pad hk.1 hk.2]
    rfl

/-- The zeroing walk (evolving `zeroT`, three prefixes). -/
theorem it_zeros (W Q R : List Bool) (G N C P : ℕ) (E : List Bool)
    (hW : W.length = 2 * G + 2) (hQ : Q.length = 2 * N + 2) (hR : R.length = 2 * C + 2)
    (hP : 0 < P) (s : Bool) (m : ℕ) (hm : m ≤ P - 1) :
    run interTMachine (2 * m)
      ⟨(13, s), 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2, W ++ (Q ++ (R ++ (zeroT P 0 ++ E)))⟩
      = ⟨(13, if m = 0 then s else true), 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 + 2 * m,
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
      it_two_step hlo, hw]
    rfl

/-! ## THE MIRROR INTERSTITIAL RUN -/

/-- **The mirror interstitial**: one pass increments the mirror in place (`jT C t ↦ jT C (t+1)`)
and re-arms the saturated live variable (`jT N N ↦ jT N 0`) — grand prefix and bound untouched. -/
theorem interT_run (G g : ℕ) (hg : g ≤ G) (N C t : ℕ) (hN : 0 < N) (htC : t < C)
    (E : List Bool) :
    run interTMachine (2 * G + 4 * N + 2 * C + 10)
      (init interTMachine (cntT G g ++ (unaryD N ++ (jT C t ++ (jT N N ++ E)))))
      = ⟨(16, false), 2 * G + 2 * N + 2 * C + 2 * N + 7,
          cntT G g ++ (unaryD N ++ (jT C (t + 1) ++ (jT N 0 ++ E)))⟩ := by
  have hW : (cntT G g).length = 2 * G + 2 := cntT_length G g hg
  have hQ : (unaryD N).length = 2 * N + 2 := unaryD_length N
  have hR : (jT C (t + 1)).length = 2 * C + 2 := jT_length C (t + 1) (by omega)
  have f0 := it_skipWs (cntT G g ++ (unaryD N ++ (jT C t ++ (jT N N ++ E)))) 0 G false
    (fun i hi => by simpa using cntE_lo G g _ i hg hi)
  simp only [Nat.zero_add] at f0
  have f0' := it_crossW (s := if G = 0 then false else true) (p := 2 * G)
    (T := cntT G g ++ (unaryD N ++ (jT C t ++ (jT N N ++ E))))
    (cntE_cm_lo G g _ hg) (cntE_cm_hi G g _ hg)
  have f1 := it_skipR1s (cntT G g ++ (unaryD N ++ (jT C t ++ (jT N N ++ E))))
    (2 * G + 2) N false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * i = 2 * G + 2 + (2 * i) from rfl, ← cntT_zero N]
      exact liftJ _ _ hW (cntE_lo N 0 _ i (by omega) hi))
  have f2 := it_crossR1 (s := if N = 0 then false else true) (p := 2 * G + 2 + 2 * N)
    (T := cntT G g ++ (unaryD N ++ (jT C t ++ (jT N N ++ E))))
    (by rw [show 2 * G + 2 + 2 * N = 2 * G + 2 + (2 * N) from rfl, ← cntT_zero N]
        exact liftJ _ _ hW (cntE_cm_lo N 0 _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 1 = 2 * G + 2 + (2 * N + 1) from by omega,
        ← cntT_zero N]
        exact liftJ _ _ hW (cntE_cm_hi N 0 _ (by omega)))
  have f3 := it_walks (cntT G g ++ (unaryD N ++ (jT C t ++ (jT N N ++ E))))
    (2 * G + 2 + 2 * N + 2) t false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * i = 2 * G + 2 + (2 * N + 2 + 2 * i)
          from by omega, ← jsT_zero C t]
      exact liftJ2 _ _ _ hW hQ
        (jsE_data C t 0 _ (2 * i) (by omega) (by omega) (by omega)))
  have f4 := it_four_incr (s := if t = 0 then false else true)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * t)
    (T := cntT G g ++ (unaryD N ++ (jT C t ++ (jT N N ++ E))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * t = 2 * G + 2 + (2 * N + 2 + 2 * t)
          from by omega, ← jsT_zero C t]
        exact liftJ2 _ _ _ hW hQ (jsE_m_lo C t 0 _ (by omega)))
  rw [show 2 * G + 2 + 2 * N + 2 + 2 * t = 2 * G + 2 + (2 * N + 2 + 2 * t) from by omega,
    W4_append_right2 (cntT G g) (unaryD N)
      (jT C t ++ (jT N N ++ E)) (2 * G + 2) (2 * N + 2) (2 * t) true true false true hW hQ
      (by rw [List.length_append, jT_length C t (by omega)]; omega),
    jT_incr C t _ htC] at f4
  have f5 := it_pads (cntT G g ++ (unaryD N ++ (jT C (t + 1) ++ (jT N N ++ E))))
    (2 * G + 2 + 2 * N + 2 + 2 * t + 4) (C - t - 1) (if t = 0 then false else true)
    (fun i hi => ⟨by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * t + 4 + 2 * i
          = 2 * G + 2 + (2 * N + 2 + (2 * (t + 1) + 2 + 2 * i)) from by omega,
        ← jsT_zero C (t + 1)]
      exact liftJ2 _ _ _ hW hQ (jsE_pad C (t + 1) 0 _ (2 * (t + 1) + 2 + 2 * i) (by omega)
        (by omega) (by omega) (by omega)), by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * t + 4 + 2 * i + 1
          = 2 * G + 2 + (2 * N + 2 + (2 * (t + 1) + 2 + 2 * i + 1)) from by omega,
        ← jsT_zero C (t + 1)]
      exact liftJ2 _ _ _ hW hQ (jsE_pad C (t + 1) 0 _ (2 * (t + 1) + 2 + 2 * i + 1)
        (by omega) (by omega) (by omega) (by omega))⟩)
  rw [show 2 * G + 2 + 2 * N + 2 + 2 * t + 4 + 2 * (C - t - 1)
      = 2 * G + 2 + 2 * N + 2 + 2 * C + 2 from by omega] at f5
  have f6 := it_padBoundT
    (s := if C - t - 1 = 0 then (if t = 0 then false else true) else false)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * C + 2)
    (T := cntT G g ++ (unaryD N ++ (jT C (t + 1) ++ (jT N N ++ E))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2
          = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + 0)) from by omega, ← jsT_zero N N]
        exact liftJ3 _ _ _ _ hW hQ hR
          (jsE_data N N 0 _ 0 (by omega) (by omega) (by omega)))
  have f7 := it_two_head (s' := true) (p := 2 * G + 2 + 2 * N + 2 + 2 * C + 2)
    (T := cntT G g ++ (unaryD N ++ (jT C (t + 1) ++ (jT N N ++ E))))
  have hw7 : writeAt (writeAt (cntT G g ++ (unaryD N ++ (jT C (t + 1) ++ (jT N N ++ E))))
      (2 * G + 2 + 2 * N + 2 + 2 * C + 2) false)
      (2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 1) true
      = cntT G g ++ (unaryD N ++ (jT C (t + 1) ++ (zeroT N 0 ++ E))) := by
    rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2
        = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + 0)) from by omega,
      W2_append_right3 (cntT G g) (unaryD N) (jT C (t + 1)) _ (2 * G + 2) (2 * N + 2)
        (2 * C + 2) 0 false true hW hQ hR
        (by rw [List.length_append, jT_length N N (le_refl N)]; omega)]
    rw [show (0 : ℕ) + 1 = 1 from rfl, zeroT_head N E hN]
  rw [hw7] at f7
  have f8 := it_zeros (cntT G g) (unaryD N) (jT C (t + 1)) G N C N E hW hQ hR hN true
    (N - 1) (le_refl _)
  have hlo9 : (cntT G g ++ (unaryD N ++ (jT C (t + 1) ++ (zeroT N (N - 1) ++ E)))).getD
      (2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 + 2 * (N - 1)) false = false := by
    rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 + 2 * (N - 1)
        = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + 2 * N)) from by omega]
    exact liftJ3 _ _ _ _ hW hQ hR (zeroE_m_lo N E hN)
  have f9 := it_two_last (s := if N - 1 = 0 then true else true)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 + 2 * (N - 1))
    (T := cntT G g ++ (unaryD N ++ (jT C (t + 1) ++ (zeroT N (N - 1) ++ E)))) hlo9
  have hw9 : writeAt (writeAt (cntT G g ++ (unaryD N
      ++ (jT C (t + 1) ++ (zeroT N (N - 1) ++ E))))
      (2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 + 2 * (N - 1)) false)
      (2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 + 2 * (N - 1) + 1) false
      = cntT G g ++ (unaryD N ++ (jT C (t + 1) ++ (jT N 0 ++ E))) := by
    rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 + 2 * (N - 1)
        = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + 2 * N)) from by omega,
      W2_append_right3 (cntT G g) (unaryD N) (jT C (t + 1)) _ (2 * G + 2) (2 * N + 2)
        (2 * C + 2) (2 * N) false false hW hQ hR
        (by rw [List.length_append, zeroT_length N (N - 1) (le_refl _) hN]; omega),
      zeroT_last N E hN]
  rw [hw9] at f9
  rw [init_it,
    show 2 * G + 4 * N + 2 * C + 10
      = 2 * G + (2 + (2 * N + (2 + (2 * t + (4 + (2 * (C - t - 1) + (2 + (2
          + (2 * (N - 1) + 2))))))))) from by omega,
    run_add, f0, run_add, f0', run_add, f1, run_add, f2, run_add, f3,
    show 2 * G + 2 + 2 * N + 2 + 2 * t = 2 * G + 2 + (2 * N + 2 + 2 * t) from by omega,
    run_add, f4,
    show 2 * G + 2 + (2 * N + 2 + 2 * t) + 4 = 2 * G + 2 + 2 * N + 2 + 2 * t + 4
      from by omega,
    run_add, f5, run_add, f6, run_add, f7, run_add, f8, f9,
    show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 + 2 * (N - 1) + 1
      = 2 * G + 2 * N + 2 * C + 2 * N + 7 from by omega]

theorem interT_halt : interTMachine.halt ((16 : Fin 17), false) = true := rfl

/-! ## THE LIVE-`t` GRAND CHAIN -/

/-- The accumulated live-index family streams: `⋃_{t' < t} loop2Out body t' N`. -/
def liveChainOut (body : List LInstr) (N : ℕ) : ℕ → List Bool
  | 0 => []
  | t + 1 => liveChainOut body N t ++ loop2Out body t N

/-- **THE LIVE-`t` GRAND CHAIN**: `B` grand rounds of the mirror engine sequenced with the mirror
interstitial — round `t` reads the LIVE index `t` from the mirror and emits the family stream at
time `t`; the interstitial increments the mirror and re-arms the variable.  One machine,
self-halting at the explicit clock, final output `⋃_{t<B} loop2Out body t N`. -/
theorem rep_liveChain_run (body : List LInstr) (N : ℕ) (hN : 0 < N) (B : ℕ)
    (out : List Bool) :
    run (repMachine (seqMachine (loopProg2TMachine body) interTMachine))
      (repRounds (fun t =>
          ltClock body B N B t (out ++ liveChainOut body N t).length + 1
            + (2 * B + 4 * N + 2 * B + 10)) B + (4 * B + 4))
      (init (repMachine (seqMachine (loopProg2TMachine body) interTMachine))
        (cntT B 0 ++ (unaryD N ++ (jT B 0 ++ (jT N 0 ++ encodeD out)))))
      = ⟨Sum.inl (4, false), 2 * B + 1,
          unaryD B ++ (unaryD N ++ (jT B B ++ (jT N 0
            ++ encodeD (out ++ liveChainOut body N B))))⟩ := by
  have h := rep_run (seqMachine (loopProg2TMachine body) interTMachine) B
    (fun t => unaryD N ++ (jT B t ++ (jT N 0 ++ encodeD (out ++ liveChainOut body N t))))
    (fun t => ltClock body B N B t (out ++ liveChainOut body N t).length + 1
        + (2 * B + 4 * N + 2 * B + 10))
    (fun _ => Sum.inr (16, false)) (fun _ => 2 * B + 2 * N + 2 * B + 2 * N + 7)
    (fun t ht => by
      constructor
      · have heng := loopProg2T_run body B (t + 1) (by omega) N B t (by omega)
          (out ++ liveChainOut body N t)
        have hinter := interT_run B (t + 1) (by omega) N B t hN ht
          (encodeD ((out ++ liveChainOut body N t) ++ loop2Out body t N))
        rw [show jT N N = unaryD N from jT_full N] at hinter
        have hseq := seq_run (loopProg2TMachine body) interTMachine _ _ _ _ _ _ _ _ _
          heng rfl hinter rfl
        rw [List.append_assoc,
          show liveChainOut body N t ++ loop2Out body t N = liveChainOut body N (t + 1)
            from rfl] at hseq
        exact hseq
      · rfl)
  simp only [show liveChainOut body N 0 = [] from rfl, List.append_nil] at h
  exact h

/-- **THE TABLEAU'S TAPE-COPY FAMILY, ALL TIMES, ONE MACHINE**: every clause of every
`cellCopyClause t p`, `t = 0..B-1`, `p = 0..P`, in tableau order. -/
theorem rep_cellCopyLive_run (P B : ℕ) (out : List Bool) :
    run (repMachine (seqMachine (loopProg2TMachine cellCopyBody) interTMachine))
      (repRounds (fun t =>
          ltClock cellCopyBody B (P + 1) B t
              (out ++ liveChainOut cellCopyBody (P + 1) t).length + 1
            + (2 * B + 4 * (P + 1) + 2 * B + 10)) B + (4 * B + 4))
      (init (repMachine (seqMachine (loopProg2TMachine cellCopyBody) interTMachine))
        (cntT B 0 ++ (unaryD (P + 1) ++ (jT B 0 ++ (jT (P + 1) 0 ++ encodeD out)))))
      = ⟨Sum.inl (4, false), 2 * B + 1,
          unaryD B ++ (unaryD (P + 1) ++ (jT B B ++ (jT (P + 1) 0
            ++ encodeD (out ++ liveChainOut cellCopyBody (P + 1) B))))⟩ :=
  rep_liveChain_run cellCopyBody (P + 1) (by omega) B out

/-- Round `t`'s contribution to the live chain is the full time-`t` family. -/
theorem liveChainOut_cellCopy_succ (P t : ℕ) :
    liveChainOut cellCopyBody (P + 1) (t + 1)
      = liveChainOut cellCopyBody (P + 1) t
        ++ ((List.range (P + 1)).map (fun p =>
            encodeClause' [(headVar t p, true), (cellVar (t + 1) p, false),
              (cellVar t p, true)]
              ++ encodeClause' [(headVar t p, true), (cellVar (t + 1) p, true),
                   (cellVar t p, false)])).flatten := by
  rw [show liveChainOut cellCopyBody (P + 1) (t + 1)
      = liveChainOut cellCopyBody (P + 1) t ++ loop2Out cellCopyBody t (P + 1) from rfl,
    cellCopy_split]

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitInterT