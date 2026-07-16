import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitInterGrand

/-!
# Cook–Levin M2 emitter — the six-region support passes (`rearm6`, `snoc6`)

The stale-bound choreography for the head-family interleave (rounds
`[count-trues ⨟ rearm ⨟ snoc F ⨟ alo-literals ⨟ interGrand ⨟ rearm ⨟ row loop]`) needs two
small one-pass machines on the triangle layout
`cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t ++ (jT C2 v2 ++ (jT NV w ++ encodeD out)))))`:

* **`rearm6Machine`** — re-arm the live variable ONLY (`jT NV w ↦ jT NV 0`, `0 < w`), every
  other region untouched: skip both counters, walk-hop-pad through the three mirrors, run the
  `zeroT` walk on the live (via the brick-40 padding split), halt.

* **`snoc6Machine b`** — append ONE fixed doubled bit to the output: skip both counters,
  walk-hop-pad through the three mirrors AND the live, then the boundary-event scan absorbs
  the live pad and the doubled output data, detects the end marker, and the four-write snoc
  lands `b` (`encodeD out ↦ encodeD (out ++ [b])`).  Fixed strings chain by `seq_run`.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitSnoc6

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinCNFEncode
open PallLean.Paper93.DeepMath.PathB.CookLevinVarIndex
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitAppendBlock
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCompare
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSplice
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRange
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitNestVar
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg3
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg3P (liftJ4)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitFamilyBodies
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSeq
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitPairT
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitInterRow

/-! ## The live-only re-armer

`Fin 25 × Bool`: `0/1`, `2/3` skip the counters; `4/5` walk + `6,7` hop + `7/8`… the three
mirrors each get walk (`lo = T`), marker hop, pad-cross; then the zeroing head pair and loop
on the live; `24` halt.  Pad exits reset the carried bit. -/

def rearm6Machine : Machine where
  State := Fin 25 × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, false)
  halt := fun s => decide (s.1 = 24)
  δ := fun s b =>
    if s.1 = 0 then ((1, b), none, 1)
    else if s.1 = 1 then
      (if s.2 then ((0, s.2), none, 1)
       else (if b then ((2, s.2), none, 1) else ((24, s.2), none, 2)))
    else if s.1 = 2 then ((3, b), none, 1)
    else if s.1 = 3 then
      (if s.2 then ((2, s.2), none, 1)
       else (if b then ((4, s.2), none, 1) else ((24, s.2), none, 2)))
    else if s.1 = 4 then
      (if b then ((5, b), none, 1) else ((6, s.2), none, 1))
    else if s.1 = 5 then ((4, s.2), none, 1)
    else if s.1 = 6 then ((7, s.2), none, 1)
    else if s.1 = 7 then ((8, b), none, 1)
    else if s.1 = 8 then
      (if s.2 then ((9, false), none, 0)
       else (if b then ((9, false), none, 0) else ((7, s.2), none, 1)))
    else if s.1 = 9 then
      (if b then ((10, b), none, 1) else ((11, s.2), none, 1))
    else if s.1 = 10 then ((9, s.2), none, 1)
    else if s.1 = 11 then ((12, s.2), none, 1)
    else if s.1 = 12 then ((13, b), none, 1)
    else if s.1 = 13 then
      (if s.2 then ((14, false), none, 0)
       else (if b then ((14, false), none, 0) else ((12, s.2), none, 1)))
    else if s.1 = 14 then
      (if b then ((15, b), none, 1) else ((16, s.2), none, 1))
    else if s.1 = 15 then ((14, s.2), none, 1)
    else if s.1 = 16 then ((17, s.2), none, 1)
    else if s.1 = 17 then ((18, b), none, 1)
    else if s.1 = 18 then
      (if s.2 then ((19, false), none, 0)
       else (if b then ((19, false), none, 0) else ((17, s.2), none, 1)))
    else if s.1 = 19 then ((20, s.2), some false, 1)
    else if s.1 = 20 then ((21, s.2), some true, 1)
    else if s.1 = 21 then
      (if b then ((22, b), some false, 1) else ((23, b), some false, 1))
    else if s.1 = 22 then ((21, s.2), some false, 1)
    else if s.1 = 23 then ((24, s.2), some false, 2)
    else ((s.1, s.2), none, 2)
  accept := fun _ => false

theorem init_r6 (t : List Bool) : init rearm6Machine t = ⟨(0, false), 0, t⟩ := rfl

/-! ## The one-bit output appender

`Fin 29 × Bool`: counters, three mirror walk-hop-pads, the live walk + hop, the boundary-event
scan (`22/23`), the end-marker detect, the four-write snoc (`24,25,26,27`), `28` halt. -/

def snoc6Machine (bv : Bool) : Machine where
  State := Fin 29 × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, false)
  halt := fun s => decide (s.1 = 28)
  δ := fun s b =>
    if s.1 = 0 then ((1, b), none, 1)
    else if s.1 = 1 then
      (if s.2 then ((0, s.2), none, 1)
       else (if b then ((2, s.2), none, 1) else ((28, s.2), none, 2)))
    else if s.1 = 2 then ((3, b), none, 1)
    else if s.1 = 3 then
      (if s.2 then ((2, s.2), none, 1)
       else (if b then ((4, s.2), none, 1) else ((28, s.2), none, 2)))
    else if s.1 = 4 then
      (if b then ((5, b), none, 1) else ((6, s.2), none, 1))
    else if s.1 = 5 then ((4, s.2), none, 1)
    else if s.1 = 6 then ((7, s.2), none, 1)
    else if s.1 = 7 then ((8, b), none, 1)
    else if s.1 = 8 then
      (if s.2 then ((9, false), none, 0)
       else (if b then ((9, false), none, 0) else ((7, s.2), none, 1)))
    else if s.1 = 9 then
      (if b then ((10, b), none, 1) else ((11, s.2), none, 1))
    else if s.1 = 10 then ((9, s.2), none, 1)
    else if s.1 = 11 then ((12, s.2), none, 1)
    else if s.1 = 12 then ((13, b), none, 1)
    else if s.1 = 13 then
      (if s.2 then ((14, false), none, 0)
       else (if b then ((14, false), none, 0) else ((12, s.2), none, 1)))
    else if s.1 = 14 then
      (if b then ((15, b), none, 1) else ((16, s.2), none, 1))
    else if s.1 = 15 then ((14, s.2), none, 1)
    else if s.1 = 16 then ((17, s.2), none, 1)
    else if s.1 = 17 then ((18, b), none, 1)
    else if s.1 = 18 then
      (if s.2 then ((19, false), none, 0)
       else (if b then ((19, false), none, 0) else ((17, s.2), none, 1)))
    else if s.1 = 19 then
      (if b then ((20, b), none, 1) else ((21, s.2), none, 1))
    else if s.1 = 20 then ((19, s.2), none, 1)
    else if s.1 = 21 then ((22, s.2), none, 1)
    else if s.1 = 22 then ((23, b), none, 1)
    else if s.1 = 23 then
      (if b = s.2 then ((22, s.2), none, 1) else ((24, s.2), none, 0))
    else if s.1 = 24 then ((25, s.2), some bv, 1)
    else if s.1 = 25 then ((26, s.2), some bv, 1)
    else if s.1 = 26 then ((27, s.2), some false, 1)
    else if s.1 = 27 then ((28, s.2), some true, 2)
    else ((s.1, s.2), none, 2)
  accept := fun _ => false

theorem init_s6 (bv : Bool) (t : List Bool) :
    init (snoc6Machine bv) t = ⟨(0, false), 0, t⟩ := rfl

/-! ## Step layers -/

section StepsR6
variable {s : Bool} {p : ℕ} {T : List Bool}

theorem r6_skipW (h1 : T.getD p false = true) :
    run rearm6Machine 2 ⟨(0, s), p, T⟩ = ⟨(0, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rearm6Machine ⟨(0, s), p, T⟩ = ⟨(1, T.getD p false), p + 1, T⟩ := by
    simp only [step, rearm6Machine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, rearm6Machine, moveHead]; rfl

theorem r6_crossW (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run rearm6Machine 2 ⟨(0, s), p, T⟩ = ⟨(2, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rearm6Machine ⟨(0, s), p, T⟩ = ⟨(1, T.getD p false), p + 1, T⟩ := by
    simp only [step, rearm6Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, rearm6Machine, moveHead, h2]

theorem r6_skipR (h1 : T.getD p false = true) :
    run rearm6Machine 2 ⟨(2, s), p, T⟩ = ⟨(2, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rearm6Machine ⟨(2, s), p, T⟩ = ⟨(3, T.getD p false), p + 1, T⟩ := by
    simp only [step, rearm6Machine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, rearm6Machine, moveHead]; rfl

theorem r6_crossR (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run rearm6Machine 2 ⟨(2, s), p, T⟩ = ⟨(4, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rearm6Machine ⟨(2, s), p, T⟩ = ⟨(3, T.getD p false), p + 1, T⟩ := by
    simp only [step, rearm6Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, rearm6Machine, moveHead, h2]

theorem r6_walkB (h1 : T.getD p false = true) :
    run rearm6Machine 2 ⟨(4, s), p, T⟩ = ⟨(4, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rearm6Machine ⟨(4, s), p, T⟩ = ⟨(5, true), p + 1, T⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, rearm6Machine, moveHead, h1']
  rw [e0]
  simp only [step, rearm6Machine, moveHead]; rfl

theorem r6_hopB (h1 : T.getD p false = false) :
    run rearm6Machine 2 ⟨(4, s), p, T⟩ = ⟨(7, s), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rearm6Machine ⟨(4, s), p, T⟩ = ⟨(6, s), p + 1, T⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, rearm6Machine, moveHead, h1']
  rw [e0]
  simp only [step, rearm6Machine, moveHead]; rfl

theorem r6_padB (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = false) :
    run rearm6Machine 2 ⟨(7, s), p, T⟩ = ⟨(7, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rearm6Machine ⟨(7, s), p, T⟩ = ⟨(8, T.getD p false), p + 1, T⟩ := by
    simp only [step, rearm6Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, rearm6Machine, moveHead, h2]

theorem r6_padB_boundT (h1 : T.getD p false = true) :
    run rearm6Machine 2 ⟨(7, s), p, T⟩ = ⟨(9, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rearm6Machine ⟨(7, s), p, T⟩ = ⟨(8, T.getD p false), p + 1, T⟩ := by
    simp only [step, rearm6Machine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, rearm6Machine, moveHead]; rfl

theorem r6_padB_boundM (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run rearm6Machine 2 ⟨(7, s), p, T⟩ = ⟨(9, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rearm6Machine ⟨(7, s), p, T⟩ = ⟨(8, T.getD p false), p + 1, T⟩ := by
    simp only [step, rearm6Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, rearm6Machine, moveHead, h2]

theorem r6_padB_bound
    (h : T.getD p false = true ∨ (T.getD p false = false ∧ T.getD (p + 1) false = true)) :
    run rearm6Machine 2 ⟨(7, s), p, T⟩ = ⟨(9, false), p, T⟩ := by
  rcases h with h1 | ⟨h1, h2⟩
  · exact r6_padB_boundT h1
  · exact r6_padB_boundM h1 h2

theorem r6_walkT (h1 : T.getD p false = true) :
    run rearm6Machine 2 ⟨(9, s), p, T⟩ = ⟨(9, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rearm6Machine ⟨(9, s), p, T⟩ = ⟨(10, true), p + 1, T⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, rearm6Machine, moveHead, h1']
  rw [e0]
  simp only [step, rearm6Machine, moveHead]; rfl

theorem r6_hopT (h1 : T.getD p false = false) :
    run rearm6Machine 2 ⟨(9, s), p, T⟩ = ⟨(12, s), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rearm6Machine ⟨(9, s), p, T⟩ = ⟨(11, s), p + 1, T⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, rearm6Machine, moveHead, h1']
  rw [e0]
  simp only [step, rearm6Machine, moveHead]; rfl

theorem r6_padT (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = false) :
    run rearm6Machine 2 ⟨(12, s), p, T⟩ = ⟨(12, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rearm6Machine ⟨(12, s), p, T⟩ = ⟨(13, T.getD p false), p + 1, T⟩ := by
    simp only [step, rearm6Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, rearm6Machine, moveHead, h2]

theorem r6_padT_boundT (h1 : T.getD p false = true) :
    run rearm6Machine 2 ⟨(12, s), p, T⟩ = ⟨(14, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rearm6Machine ⟨(12, s), p, T⟩ = ⟨(13, T.getD p false), p + 1, T⟩ := by
    simp only [step, rearm6Machine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, rearm6Machine, moveHead]; rfl

theorem r6_padT_boundM (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run rearm6Machine 2 ⟨(12, s), p, T⟩ = ⟨(14, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rearm6Machine ⟨(12, s), p, T⟩ = ⟨(13, T.getD p false), p + 1, T⟩ := by
    simp only [step, rearm6Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, rearm6Machine, moveHead, h2]

theorem r6_padT_bound
    (h : T.getD p false = true ∨ (T.getD p false = false ∧ T.getD (p + 1) false = true)) :
    run rearm6Machine 2 ⟨(12, s), p, T⟩ = ⟨(14, false), p, T⟩ := by
  rcases h with h1 | ⟨h1, h2⟩
  · exact r6_padT_boundT h1
  · exact r6_padT_boundM h1 h2

theorem r6_walkJ (h1 : T.getD p false = true) :
    run rearm6Machine 2 ⟨(14, s), p, T⟩ = ⟨(14, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rearm6Machine ⟨(14, s), p, T⟩ = ⟨(15, true), p + 1, T⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, rearm6Machine, moveHead, h1']
  rw [e0]
  simp only [step, rearm6Machine, moveHead]; rfl

theorem r6_hopJ (h1 : T.getD p false = false) :
    run rearm6Machine 2 ⟨(14, s), p, T⟩ = ⟨(17, s), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rearm6Machine ⟨(14, s), p, T⟩ = ⟨(16, s), p + 1, T⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, rearm6Machine, moveHead, h1']
  rw [e0]
  simp only [step, rearm6Machine, moveHead]; rfl

theorem r6_padJ (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = false) :
    run rearm6Machine 2 ⟨(17, s), p, T⟩ = ⟨(17, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rearm6Machine ⟨(17, s), p, T⟩ = ⟨(18, T.getD p false), p + 1, T⟩ := by
    simp only [step, rearm6Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, rearm6Machine, moveHead, h2]

theorem r6_padJ_boundT (h1 : T.getD p false = true) :
    run rearm6Machine 2 ⟨(17, s), p, T⟩ = ⟨(19, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step rearm6Machine ⟨(17, s), p, T⟩ = ⟨(18, T.getD p false), p + 1, T⟩ := by
    simp only [step, rearm6Machine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, rearm6Machine, moveHead]; rfl

theorem r6_two_head {s' : Bool} :
    run rearm6Machine 2 ⟨(19, s'), p, T⟩
      = ⟨(21, s'), p + 2, writeAt (writeAt T p false) (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e4 : step rearm6Machine ⟨(19, s'), p, T⟩
      = ⟨(20, s'), p + 1, writeAt T p false⟩ := by
    simp only [step, rearm6Machine, moveHead]; rfl
  have e5 : ∀ p' T', step rearm6Machine ⟨(20, s'), p', T'⟩
      = ⟨(21, s'), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, rearm6Machine, moveHead]; rfl
  rw [e4, e5]

theorem r6_zero_step (h : T.getD p false = true) :
    run rearm6Machine 2 ⟨(21, s), p, T⟩
      = ⟨(21, true), p + 2, writeAt (writeAt T p false) (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e6 : step rearm6Machine ⟨(21, s), p, T⟩
      = ⟨(22, true), p + 1, writeAt T p false⟩ := by
    have h' := h
    rw [List.getD_eq_getElem?_getD] at h'
    simp [step, rearm6Machine, moveHead, h']
  rw [e6]
  simp only [step, rearm6Machine, moveHead]; rfl

theorem r6_zero_last (h : T.getD p false = false) :
    run rearm6Machine 2 ⟨(21, s), p, T⟩
      = ⟨(24, false), p + 1, writeAt (writeAt T p false) (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e6 : step rearm6Machine ⟨(21, s), p, T⟩
      = ⟨(23, false), p + 1, writeAt T p false⟩ := by
    have h' := h
    rw [List.getD_eq_getElem?_getD] at h'
    simp [step, rearm6Machine, moveHead, h']
  rw [e6]
  simp only [step, rearm6Machine, moveHead]; rfl

end StepsR6

theorem r6_skipWs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run rearm6Machine (2 * k) ⟨(0, s), q, T⟩
      = ⟨(0, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), r6_skipW (h k (by omega))]
    rfl

theorem r6_skipRs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run rearm6Machine (2 * k) ⟨(2, s), q, T⟩
      = ⟨(2, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), r6_skipR (h k (by omega))]
    rfl

theorem r6_walkBs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run rearm6Machine (2 * k) ⟨(4, s), q, T⟩
      = ⟨(4, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), r6_walkB (h k (by omega))]
    rfl

theorem r6_padBs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = false
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run rearm6Machine (2 * k) ⟨(7, s), q, T⟩
      = ⟨(7, if k = 0 then s else false), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), r6_padB hk.1 hk.2]
    rfl

theorem r6_walkTs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run rearm6Machine (2 * k) ⟨(9, s), q, T⟩
      = ⟨(9, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), r6_walkT (h k (by omega))]
    rfl

theorem r6_padTs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = false
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run rearm6Machine (2 * k) ⟨(12, s), q, T⟩
      = ⟨(12, if k = 0 then s else false), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), r6_padT hk.1 hk.2]
    rfl

theorem r6_walkJs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run rearm6Machine (2 * k) ⟨(14, s), q, T⟩
      = ⟨(14, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), r6_walkJ (h k (by omega))]
    rfl

theorem r6_padJs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = false
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run rearm6Machine (2 * k) ⟨(17, s), q, T⟩
      = ⟨(17, if k = 0 then s else false), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), r6_padJ hk.1 hk.2]
    rfl

/-- The zeroing walk (evolving `zeroT`, five prefixes). -/
theorem r6_zeros (W Q R S U : List Bool) (G P2 CB C1 C2 P : ℕ) (E : List Bool)
    (hW : W.length = 2 * G + 2) (hQ : Q.length = 2 * P2 + 2) (hR : R.length = 2 * CB + 2)
    (hS : S.length = 2 * C1 + 2) (hU : U.length = 2 * C2 + 2) (hP : 0 < P) (s : Bool)
    (m : ℕ) (hm : m ≤ P - 1) :
    run rearm6Machine (2 * m)
      ⟨(21, s), 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2,
        W ++ (Q ++ (R ++ (S ++ (U ++ (zeroT P 0 ++ E)))))⟩
      = ⟨(21, if m = 0 then s else true),
          2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 + 2 * m,
          W ++ (Q ++ (R ++ (S ++ (U ++ (zeroT P m ++ E)))))⟩ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hlo : (W ++ (Q ++ (R ++ (S ++ (U ++ (zeroT P m ++ E)))))).getD
        (2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 + 2 * m) false
        = true := by
      rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 + 2 * m
          = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2
              + 2 * (m + 1))))) from by omega]
      exact liftJ5 _ _ _ _ _ _ hW hQ hR hS hU (zeroE_data_lo P m E (by omega))
    have hw : writeAt (writeAt (W ++ (Q ++ (R ++ (S ++ (U ++ (zeroT P m ++ E))))))
        (2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 + 2 * m) false)
        (2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 + 2 * m + 1)
        false
        = W ++ (Q ++ (R ++ (S ++ (U ++ (zeroT P (m + 1) ++ E))))) := by
      rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 + 2 * m
          = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2
              + 2 * (m + 1))))) from by omega,
        W2_append_right5 W Q R S U _ (2 * G + 2) (2 * P2 + 2) (2 * CB + 2) (2 * C1 + 2)
          (2 * C2 + 2) (2 * (m + 1)) false false hW hQ hR hS hU
          (by rw [List.length_append, zeroT_length P m (by omega) hP]; omega),
        zeroT_step P m E (by omega)]
    rw [show 2 * (m + 1) = 2 * m + 2 from by ring, run_add, ih (by omega),
      r6_zero_step hlo, hw]
    rfl

/-! ## THE LIVE-ONLY RE-ARMER RUN -/

/-- **The live-only re-armer**: one pass, `jT NV w ↦ jT NV 0`, every other region verbatim. -/
theorem rearm6_run (G g : ℕ) (hg : g ≤ G) (P2 r : ℕ) (hr : r ≤ P2)
    (CB C1 C2 NV v1 t v2 w : ℕ) (hv1 : v1 ≤ CB) (ht : t ≤ C1) (hv2 : v2 ≤ C2)
    (hw0 : 0 < w) (hw : w ≤ NV) (E : List Bool) :
    run rearm6Machine (2 * G + 2 * P2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * w + 18)
      (init rearm6Machine (cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t
        ++ (jT C2 v2 ++ (jT NV w ++ E)))))))
      = ⟨(24, false), 2 * G + 2 * P2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * w + 11,
          cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t
            ++ (jT C2 v2 ++ (jT NV 0 ++ E)))))⟩ := by
  have hW : (cntT G g).length = 2 * G + 2 := cntT_length G g hg
  have hQ : (cntT P2 r).length = 2 * P2 + 2 := cntT_length P2 r hr
  have hR : (jT CB v1).length = 2 * CB + 2 := jT_length CB v1 hv1
  have hS : (jT C1 t).length = 2 * C1 + 2 := jT_length C1 t ht
  have hU : (jT C2 v2).length = 2 * C2 + 2 := jT_length C2 v2 hv2
  have f0 := r6_skipWs (cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t
      ++ (jT C2 v2 ++ (jT NV w ++ E)))))) 0 G false
    (fun i hi => by simpa using cntE_lo G g _ i hg hi)
  simp only [Nat.zero_add] at f0
  have f0' := r6_crossW (s := if G = 0 then false else true) (p := 2 * G)
    (T := cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t
      ++ (jT C2 v2 ++ (jT NV w ++ E))))))
    (cntE_cm_lo G g _ hg) (cntE_cm_hi G g _ hg)
  have f1 := r6_skipRs (cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t
      ++ (jT C2 v2 ++ (jT NV w ++ E)))))) (2 * G + 2) P2 false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * i = 2 * G + 2 + (2 * i) from rfl]
      exact liftJ _ _ hW (cntE_lo P2 r _ i hr hi))
  have f1' := r6_crossR (s := if P2 = 0 then false else true) (p := 2 * G + 2 + 2 * P2)
    (T := cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t
      ++ (jT C2 v2 ++ (jT NV w ++ E))))))
    (by rw [show 2 * G + 2 + 2 * P2 = 2 * G + 2 + (2 * P2) from rfl]
        exact liftJ _ _ hW (cntE_cm_lo P2 r _ hr))
    (by rw [show 2 * G + 2 + 2 * P2 + 1 = 2 * G + 2 + (2 * P2 + 1) from by omega]
        exact liftJ _ _ hW (cntE_cm_hi P2 r _ hr))
  have f2 := r6_walkBs (cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t
      ++ (jT C2 v2 ++ (jT NV w ++ E)))))) (2 * G + 2 + 2 * P2 + 2) v1 false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * i = 2 * G + 2 + (2 * P2 + 2 + 2 * i)
          from by omega, ← jsT_zero CB v1]
      exact liftJ2 _ _ _ hW hQ
        (jsE_data CB v1 0 _ (2 * i) (by omega) (by omega) (by omega)))
  have f2' := r6_hopB (s := if v1 = 0 then false else true)
    (p := 2 * G + 2 + 2 * P2 + 2 + 2 * v1)
    (T := cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t
      ++ (jT C2 v2 ++ (jT NV w ++ E))))))
    (by rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * v1 = 2 * G + 2 + (2 * P2 + 2 + 2 * v1)
          from by omega, ← jsT_zero CB v1]
        exact liftJ2 _ _ _ hW hQ (jsE_m_lo CB v1 0 _ (by omega)))
  have f3 := r6_padBs (cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t
      ++ (jT C2 v2 ++ (jT NV w ++ E)))))) (2 * G + 2 + 2 * P2 + 2 + 2 * v1 + 2)
    (CB - v1) (if v1 = 0 then false else true)
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
  have f3' := r6_padB_bound
    (s := if CB - v1 = 0 then (if v1 = 0 then false else true) else false)
    (p := 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2)
    (T := cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t
      ++ (jT C2 v2 ++ (jT NV w ++ E))))))
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
  have f4 := r6_walkTs (cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t
      ++ (jT C2 v2 ++ (jT NV w ++ E)))))) (2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2) t false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * i
          = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + 2 * i)) from by omega,
        ← jsT_zero C1 t]
      exact liftJ3 _ _ _ _ hW hQ hR
        (jsE_data C1 t 0 _ (2 * i) (by omega) (by omega) (by omega)))
  have f4' := r6_hopT (s := if t = 0 then false else true)
    (p := 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * t)
    (T := cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t
      ++ (jT C2 v2 ++ (jT NV w ++ E))))))
    (by rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * t
          = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + 2 * t)) from by omega,
        ← jsT_zero C1 t]
        exact liftJ3 _ _ _ _ hW hQ hR (jsE_m_lo C1 t 0 _ (by omega)))
  have f5 := r6_padTs (cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t
      ++ (jT C2 v2 ++ (jT NV w ++ E)))))) (2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * t + 2)
    (C1 - t) (if t = 0 then false else true)
    (fun i hi => ⟨by
      rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * t + 2 + 2 * i
          = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * t + 2 + 2 * i))) from by omega,
        ← jsT_zero C1 t]
      exact liftJ3 _ _ _ _ hW hQ hR (jsE_pad C1 t 0 _ (2 * t + 2 + 2 * i)
        (by omega) ht (by omega) (by omega)), by
      rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * t + 2 + 2 * i + 1
          = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * t + 2 + 2 * i + 1)))
          from by omega, ← jsT_zero C1 t]
      exact liftJ3 _ _ _ _ hW hQ hR (jsE_pad C1 t 0 _ (2 * t + 2 + 2 * i + 1)
        (by omega) ht (by omega) (by omega))⟩)
  rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * t + 2 + 2 * (C1 - t)
      = 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 from by omega] at f5
  have f5' := r6_padT_bound
    (s := if C1 - t = 0 then (if t = 0 then false else true) else false)
    (p := 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2)
    (T := cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t
      ++ (jT C2 v2 ++ (jT NV w ++ E))))))
    (by rcases Nat.eq_zero_or_pos v2 with h0 | h0
        · right
          constructor
          · rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2
                = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + 2 * v2)))
                from by omega, ← jsT_zero C2 v2]
            exact liftJ4 _ _ _ _ _ hW hQ hR hS (jsE_m_lo C2 v2 0 _ (by omega))
          · rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 1
                = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * v2 + 1))))
                from by omega, ← jsT_zero C2 v2]
            exact liftJ4 _ _ _ _ _ hW hQ hR hS (jsE_m_hi C2 v2 0 _ (by omega))
        · left
          rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2
              = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * C1 + 2))) from by omega,
            ← jsT_zero C2 v2]
          exact liftJ4 _ _ _ _ _ hW hQ hR hS
            (jsE_data C2 v2 0 _ 0 (by omega) (by omega) (by omega)))
  have f6 := r6_walkJs (cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t
      ++ (jT C2 v2 ++ (jT NV w ++ E))))))
    (2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2) v2 false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * i
          = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + 2 * i)))
          from by omega, ← jsT_zero C2 v2]
      exact liftJ4 _ _ _ _ _ hW hQ hR hS
        (jsE_data C2 v2 0 _ (2 * i) (by omega) (by omega) (by omega)))
  have f6' := r6_hopJ (s := if v2 = 0 then false else true)
    (p := 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * v2)
    (T := cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t
      ++ (jT C2 v2 ++ (jT NV w ++ E))))))
    (by rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * v2
          = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + 2 * v2)))
          from by omega, ← jsT_zero C2 v2]
        exact liftJ4 _ _ _ _ _ hW hQ hR hS (jsE_m_lo C2 v2 0 _ (by omega)))
  have f7 := r6_padJs (cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t
      ++ (jT C2 v2 ++ (jT NV w ++ E))))))
    (2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * v2 + 2) (C2 - v2)
    (if v2 = 0 then false else true)
    (fun i hi => ⟨by
      rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * v2 + 2 + 2 * i
          = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * C1 + 2
              + (2 * v2 + 2 + 2 * i)))) from by omega, ← jsT_zero C2 v2]
      exact liftJ4 _ _ _ _ _ hW hQ hR hS (jsE_pad C2 v2 0 _ (2 * v2 + 2 + 2 * i)
        (by omega) hv2 (by omega) (by omega)), by
      rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * v2 + 2 + 2 * i + 1
          = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * C1 + 2
              + (2 * v2 + 2 + 2 * i + 1)))) from by omega, ← jsT_zero C2 v2]
      exact liftJ4 _ _ _ _ _ hW hQ hR hS (jsE_pad C2 v2 0 _ (2 * v2 + 2 + 2 * i + 1)
        (by omega) hv2 (by omega) (by omega))⟩)
  rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * v2 + 2
        + 2 * (C2 - v2)
      = 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2
      from by omega] at f7
  have f7' := r6_padJ_boundT
    (s := if C2 - v2 = 0 then (if v2 = 0 then false else true) else false)
    (p := 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2)
    (T := cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t
      ++ (jT C2 v2 ++ (jT NV w ++ E))))))
    (by rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2
          = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2 + 0))))
          from by omega, ← jsT_zero NV w]
        exact liftJ5 _ _ _ _ _ _ hW hQ hR hS hU
          (jsE_data NV w 0 _ 0 (by omega) (by omega) (by omega)))
  have f8 := r6_two_head (s' := false)
    (p := 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2)
    (T := cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t
      ++ (jT C2 v2 ++ (jT NV w ++ E))))))
  have hw8 : writeAt (writeAt (cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t
      ++ (jT C2 v2 ++ (jT NV w ++ E))))))
      (2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2) false)
      (2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 1) true
      = cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t ++ (jT C2 v2
          ++ (zeroT w 0 ++ (List.replicate (2 * (NV - w)) false ++ E)))))) := by
    rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2
        = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2 + 0))))
        from by omega,
      W2_append_right5 (cntT G g) (cntT P2 r) (jT CB v1) (jT C1 t) (jT C2 v2) _
        (2 * G + 2) (2 * P2 + 2) (2 * CB + 2) (2 * C1 + 2) (2 * C2 + 2) 0 false true hW hQ
        hR hS hU (by rw [List.length_append, jT_length NV w hw]; omega),
      jT_split_pad NV w E, show (0 : ℕ) + 1 = 1 from rfl, zeroT_head w _ hw0]
  rw [hw8] at f8
  have f9 := r6_zeros (cntT G g) (cntT P2 r) (jT CB v1) (jT C1 t) (jT C2 v2) G P2 CB C1
    C2 w (List.replicate (2 * (NV - w)) false ++ E) hW hQ hR hS hU hw0 false (w - 1)
    (le_refl _)
  have hlo10 : (cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t ++ (jT C2 v2
      ++ (zeroT w (w - 1) ++ (List.replicate (2 * (NV - w)) false ++ E))))))).getD
      (2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 + 2 * (w - 1))
      false = false := by
    rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2
          + 2 * (w - 1)
        = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2 + 2 * w))))
        from by omega]
    exact liftJ5 _ _ _ _ _ _ hW hQ hR hS hU (zeroE_m_lo w _ hw0)
  have f10 := r6_zero_last (s := if w - 1 = 0 then false else true)
    (p := 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 + 2 * (w - 1))
    (T := cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t ++ (jT C2 v2
      ++ (zeroT w (w - 1) ++ (List.replicate (2 * (NV - w)) false ++ E))))))) hlo10
  have hw10 : writeAt (writeAt (cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t
      ++ (jT C2 v2 ++ (zeroT w (w - 1)
        ++ (List.replicate (2 * (NV - w)) false ++ E)))))))
      (2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 + 2 * (w - 1))
      false)
      (2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 + 2 * (w - 1)
        + 1) false
      = cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t ++ (jT C2 v2
          ++ (jT NV 0 ++ E))))) := by
    rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2
          + 2 * (w - 1)
        = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2 + 2 * w))))
        from by omega,
      W2_append_right5 (cntT G g) (cntT P2 r) (jT CB v1) (jT C1 t) (jT C2 v2) _
        (2 * G + 2) (2 * P2 + 2) (2 * CB + 2) (2 * C1 + 2) (2 * C2 + 2) (2 * w) false
        false hW hQ hR hS hU
        (by rw [List.length_append, zeroT_length w (w - 1) (le_refl _) hw0]; omega),
      zeroT_last w _ hw0, jT_join_pad NV w hw E]
  rw [hw10] at f10
  rw [init_r6,
    show 2 * G + 2 * P2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * w + 18
      = 2 * G + (2 + (2 * P2 + (2 + (2 * v1 + (2 + (2 * (CB - v1) + (2 + (2 * t + (2
          + (2 * (C1 - t) + (2 + (2 * v2 + (2 + (2 * (C2 - v2) + (2 + (2
          + (2 * (w - 1) + 2))))))))))))))))) from by omega,
    run_add, f0, run_add, f0', run_add, f1, run_add, f1', run_add, f2, run_add, f2',
    show 2 * G + 2 + 2 * P2 + 2 + 2 * v1 + 2 = 2 * G + 2 + 2 * P2 + 2 + 2 * v1 + 2
      from rfl,
    run_add, f3, run_add, f3', run_add, f4, run_add, f4', run_add, f5, run_add, f5',
    run_add, f6, run_add, f6', run_add, f7, run_add, f7', run_add, f8, run_add, f9, f10,
    show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 + 2 * (w - 1)
        + 1
      = 2 * G + 2 * P2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * w + 11 from by omega]

theorem rearm6_halt : rearm6Machine.halt ((24 : Fin 25), false) = true := rfl

/-! ## The appender's step layer -/

section StepsS6
variable {bv : Bool} {s : Bool} {p : ℕ} {T : List Bool}

theorem s6_skipW (h1 : T.getD p false = true) :
    run (snoc6Machine bv) 2 ⟨(0, s), p, T⟩ = ⟨(0, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (snoc6Machine bv) ⟨(0, s), p, T⟩ = ⟨(1, T.getD p false), p + 1, T⟩ := by
    simp only [step, snoc6Machine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, snoc6Machine, moveHead]; rfl

theorem s6_crossW (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (snoc6Machine bv) 2 ⟨(0, s), p, T⟩ = ⟨(2, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (snoc6Machine bv) ⟨(0, s), p, T⟩ = ⟨(1, T.getD p false), p + 1, T⟩ := by
    simp only [step, snoc6Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, snoc6Machine, moveHead, h2]

theorem s6_skipR (h1 : T.getD p false = true) :
    run (snoc6Machine bv) 2 ⟨(2, s), p, T⟩ = ⟨(2, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (snoc6Machine bv) ⟨(2, s), p, T⟩ = ⟨(3, T.getD p false), p + 1, T⟩ := by
    simp only [step, snoc6Machine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, snoc6Machine, moveHead]; rfl

theorem s6_crossR (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (snoc6Machine bv) 2 ⟨(2, s), p, T⟩ = ⟨(4, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (snoc6Machine bv) ⟨(2, s), p, T⟩ = ⟨(3, T.getD p false), p + 1, T⟩ := by
    simp only [step, snoc6Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, snoc6Machine, moveHead, h2]

theorem s6_walkB (h1 : T.getD p false = true) :
    run (snoc6Machine bv) 2 ⟨(4, s), p, T⟩ = ⟨(4, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (snoc6Machine bv) ⟨(4, s), p, T⟩ = ⟨(5, true), p + 1, T⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, snoc6Machine, moveHead, h1']
  rw [e0]
  simp only [step, snoc6Machine, moveHead]; rfl

theorem s6_hopB (h1 : T.getD p false = false) :
    run (snoc6Machine bv) 2 ⟨(4, s), p, T⟩ = ⟨(7, s), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (snoc6Machine bv) ⟨(4, s), p, T⟩ = ⟨(6, s), p + 1, T⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, snoc6Machine, moveHead, h1']
  rw [e0]
  simp only [step, snoc6Machine, moveHead]; rfl

theorem s6_padB (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = false) :
    run (snoc6Machine bv) 2 ⟨(7, s), p, T⟩ = ⟨(7, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (snoc6Machine bv) ⟨(7, s), p, T⟩ = ⟨(8, T.getD p false), p + 1, T⟩ := by
    simp only [step, snoc6Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, snoc6Machine, moveHead, h2]

theorem s6_padB_boundT (h1 : T.getD p false = true) :
    run (snoc6Machine bv) 2 ⟨(7, s), p, T⟩ = ⟨(9, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (snoc6Machine bv) ⟨(7, s), p, T⟩ = ⟨(8, T.getD p false), p + 1, T⟩ := by
    simp only [step, snoc6Machine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, snoc6Machine, moveHead]; rfl

theorem s6_padB_boundM (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (snoc6Machine bv) 2 ⟨(7, s), p, T⟩ = ⟨(9, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (snoc6Machine bv) ⟨(7, s), p, T⟩ = ⟨(8, T.getD p false), p + 1, T⟩ := by
    simp only [step, snoc6Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, snoc6Machine, moveHead, h2]

theorem s6_padB_bound
    (h : T.getD p false = true ∨ (T.getD p false = false ∧ T.getD (p + 1) false = true)) :
    run (snoc6Machine bv) 2 ⟨(7, s), p, T⟩ = ⟨(9, false), p, T⟩ := by
  rcases h with h1 | ⟨h1, h2⟩
  · exact s6_padB_boundT h1
  · exact s6_padB_boundM h1 h2

theorem s6_walkT (h1 : T.getD p false = true) :
    run (snoc6Machine bv) 2 ⟨(9, s), p, T⟩ = ⟨(9, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (snoc6Machine bv) ⟨(9, s), p, T⟩ = ⟨(10, true), p + 1, T⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, snoc6Machine, moveHead, h1']
  rw [e0]
  simp only [step, snoc6Machine, moveHead]; rfl

theorem s6_hopT (h1 : T.getD p false = false) :
    run (snoc6Machine bv) 2 ⟨(9, s), p, T⟩ = ⟨(12, s), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (snoc6Machine bv) ⟨(9, s), p, T⟩ = ⟨(11, s), p + 1, T⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, snoc6Machine, moveHead, h1']
  rw [e0]
  simp only [step, snoc6Machine, moveHead]; rfl

theorem s6_padT (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = false) :
    run (snoc6Machine bv) 2 ⟨(12, s), p, T⟩ = ⟨(12, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (snoc6Machine bv) ⟨(12, s), p, T⟩ = ⟨(13, T.getD p false), p + 1, T⟩ := by
    simp only [step, snoc6Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, snoc6Machine, moveHead, h2]

theorem s6_padT_boundT (h1 : T.getD p false = true) :
    run (snoc6Machine bv) 2 ⟨(12, s), p, T⟩ = ⟨(14, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (snoc6Machine bv) ⟨(12, s), p, T⟩ = ⟨(13, T.getD p false), p + 1, T⟩ := by
    simp only [step, snoc6Machine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, snoc6Machine, moveHead]; rfl

theorem s6_padT_boundM (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (snoc6Machine bv) 2 ⟨(12, s), p, T⟩ = ⟨(14, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (snoc6Machine bv) ⟨(12, s), p, T⟩ = ⟨(13, T.getD p false), p + 1, T⟩ := by
    simp only [step, snoc6Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, snoc6Machine, moveHead, h2]

theorem s6_padT_bound
    (h : T.getD p false = true ∨ (T.getD p false = false ∧ T.getD (p + 1) false = true)) :
    run (snoc6Machine bv) 2 ⟨(12, s), p, T⟩ = ⟨(14, false), p, T⟩ := by
  rcases h with h1 | ⟨h1, h2⟩
  · exact s6_padT_boundT h1
  · exact s6_padT_boundM h1 h2

theorem s6_walkJ (h1 : T.getD p false = true) :
    run (snoc6Machine bv) 2 ⟨(14, s), p, T⟩ = ⟨(14, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (snoc6Machine bv) ⟨(14, s), p, T⟩ = ⟨(15, true), p + 1, T⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, snoc6Machine, moveHead, h1']
  rw [e0]
  simp only [step, snoc6Machine, moveHead]; rfl

theorem s6_hopJ (h1 : T.getD p false = false) :
    run (snoc6Machine bv) 2 ⟨(14, s), p, T⟩ = ⟨(17, s), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (snoc6Machine bv) ⟨(14, s), p, T⟩ = ⟨(16, s), p + 1, T⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, snoc6Machine, moveHead, h1']
  rw [e0]
  simp only [step, snoc6Machine, moveHead]; rfl

theorem s6_padJ (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = false) :
    run (snoc6Machine bv) 2 ⟨(17, s), p, T⟩ = ⟨(17, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (snoc6Machine bv) ⟨(17, s), p, T⟩ = ⟨(18, T.getD p false), p + 1, T⟩ := by
    simp only [step, snoc6Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, snoc6Machine, moveHead, h2]

theorem s6_padJ_boundT (h1 : T.getD p false = true) :
    run (snoc6Machine bv) 2 ⟨(17, s), p, T⟩ = ⟨(19, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (snoc6Machine bv) ⟨(17, s), p, T⟩ = ⟨(18, T.getD p false), p + 1, T⟩ := by
    simp only [step, snoc6Machine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, snoc6Machine, moveHead]; rfl

theorem s6_padJ_boundM (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (snoc6Machine bv) 2 ⟨(17, s), p, T⟩ = ⟨(19, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (snoc6Machine bv) ⟨(17, s), p, T⟩ = ⟨(18, T.getD p false), p + 1, T⟩ := by
    simp only [step, snoc6Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, snoc6Machine, moveHead, h2]

theorem s6_padJ_bound
    (h : T.getD p false = true ∨ (T.getD p false = false ∧ T.getD (p + 1) false = true)) :
    run (snoc6Machine bv) 2 ⟨(17, s), p, T⟩ = ⟨(19, false), p, T⟩ := by
  rcases h with h1 | ⟨h1, h2⟩
  · exact s6_padJ_boundT h1
  · exact s6_padJ_boundM h1 h2

theorem s6_walkV (h1 : T.getD p false = true) :
    run (snoc6Machine bv) 2 ⟨(19, s), p, T⟩ = ⟨(19, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (snoc6Machine bv) ⟨(19, s), p, T⟩ = ⟨(20, true), p + 1, T⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, snoc6Machine, moveHead, h1']
  rw [e0]
  simp only [step, snoc6Machine, moveHead]; rfl

theorem s6_hopV (h1 : T.getD p false = false) :
    run (snoc6Machine bv) 2 ⟨(19, s), p, T⟩ = ⟨(22, s), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (snoc6Machine bv) ⟨(19, s), p, T⟩ = ⟨(21, s), p + 1, T⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, snoc6Machine, moveHead, h1']
  rw [e0]
  simp only [step, snoc6Machine, moveHead]; rfl

theorem s6_scan (h : T.getD p false = T.getD (p + 1) false) :
    run (snoc6Machine bv) 2 ⟨(22, s), p, T⟩ = ⟨(22, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (snoc6Machine bv) ⟨(22, s), p, T⟩ = ⟨(23, T.getD p false), p + 1, T⟩ := by
    simp only [step, snoc6Machine, moveHead]; rfl
  rw [e0]
  have h' : T.getD (p + 1) false = T.getD p false := h.symm
  rw [List.getD_eq_getElem?_getD] at h'
  simp [step, snoc6Machine, moveHead, h']

theorem s6_detect (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (snoc6Machine bv) 2 ⟨(22, s), p, T⟩ = ⟨(24, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (snoc6Machine bv) ⟨(22, s), p, T⟩ = ⟨(23, T.getD p false), p + 1, T⟩ := by
    simp only [step, snoc6Machine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, snoc6Machine, moveHead, h2', show p + 1 - 1 = p from by omega]

theorem s6_four :
    run (snoc6Machine bv) 4 ⟨(24, s), p, T⟩
      = ⟨(28, s), p + 3, writeAt (writeAt (writeAt (writeAt T p bv)
          (p + 1) bv) (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e0 : step (snoc6Machine bv) ⟨(24, s), p, T⟩
      = ⟨(25, s), p + 1, writeAt T p bv⟩ := by
    simp only [step, snoc6Machine, moveHead]; rfl
  have e1 : ∀ p' T', step (snoc6Machine bv) ⟨(25, s), p', T'⟩
      = ⟨(26, s), p' + 1, writeAt T' p' bv⟩ := by
    intro p' T'; simp only [step, snoc6Machine, moveHead]; rfl
  have e2 : ∀ p' T', step (snoc6Machine bv) ⟨(26, s), p', T'⟩
      = ⟨(27, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, snoc6Machine, moveHead]; rfl
  have e3 : ∀ p' T', step (snoc6Machine bv) ⟨(27, s), p', T'⟩
      = ⟨(28, s), p', writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, snoc6Machine, moveHead]; rfl
  rw [e0, e1, e2, e3]

end StepsS6

/-! ## The appender's scan invariants -/

theorem s6_skipWs (bv : Bool) (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (snoc6Machine bv) (2 * k) ⟨(0, s), q, T⟩
      = ⟨(0, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), s6_skipW (h k (by omega))]
    rfl

theorem s6_skipRs (bv : Bool) (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (snoc6Machine bv) (2 * k) ⟨(2, s), q, T⟩
      = ⟨(2, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), s6_skipR (h k (by omega))]
    rfl

theorem s6_walkBs (bv : Bool) (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (snoc6Machine bv) (2 * k) ⟨(4, s), q, T⟩
      = ⟨(4, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), s6_walkB (h k (by omega))]
    rfl

theorem s6_padBs (bv : Bool) (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = false
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run (snoc6Machine bv) (2 * k) ⟨(7, s), q, T⟩
      = ⟨(7, if k = 0 then s else false), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), s6_padB hk.1 hk.2]
    rfl

theorem s6_walkTs (bv : Bool) (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (snoc6Machine bv) (2 * k) ⟨(9, s), q, T⟩
      = ⟨(9, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), s6_walkT (h k (by omega))]
    rfl

theorem s6_padTs (bv : Bool) (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = false
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run (snoc6Machine bv) (2 * k) ⟨(12, s), q, T⟩
      = ⟨(12, if k = 0 then s else false), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), s6_padT hk.1 hk.2]
    rfl

theorem s6_walkJs (bv : Bool) (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (snoc6Machine bv) (2 * k) ⟨(14, s), q, T⟩
      = ⟨(14, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), s6_walkJ (h k (by omega))]
    rfl

theorem s6_padJs (bv : Bool) (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = false
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run (snoc6Machine bv) (2 * k) ⟨(17, s), q, T⟩
      = ⟨(17, if k = 0 then s else false), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), s6_padJ hk.1 hk.2]
    rfl

theorem s6_walkVs (bv : Bool) (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (snoc6Machine bv) (2 * k) ⟨(19, s), q, T⟩
      = ⟨(19, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), s6_walkV (h k (by omega))]
    rfl

theorem s6_scans (bv : Bool) (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (snoc6Machine bv) (2 * k) ⟨(22, s), q, T⟩
      = ⟨(22, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), s6_scan (h k (by omega))]
    rfl

/-! ## THE ONE-BIT APPEND RUN -/

/-- **The one-bit output appender**: one pass, `encodeD out ↦ encodeD (out ++ [bv])`, every
region verbatim. -/
theorem snoc6_run (bv : Bool) (G g : ℕ) (hg : g ≤ G) (P2 r : ℕ) (hr : r ≤ P2)
    (CB C1 C2 NV v1 t v2 w : ℕ) (hv1 : v1 ≤ CB) (ht : t ≤ C1) (hv2 : v2 ≤ C2)
    (hw : w ≤ NV) (out : List Bool) :
    run (snoc6Machine bv)
      (2 * G + 2 * P2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 2 * out.length + 24)
      (init (snoc6Machine bv) (cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t
        ++ (jT C2 v2 ++ (jT NV w ++ encodeD out)))))))
      = ⟨(28, false),
          2 * G + 2 * P2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 2 * out.length + 15,
          cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t
            ++ (jT C2 v2 ++ (jT NV w ++ encodeD (out ++ [bv]))))))⟩ := by
  have hW : (cntT G g).length = 2 * G + 2 := cntT_length G g hg
  have hQ : (cntT P2 r).length = 2 * P2 + 2 := cntT_length P2 r hr
  have hR : (jT CB v1).length = 2 * CB + 2 := jT_length CB v1 hv1
  have hS : (jT C1 t).length = 2 * C1 + 2 := jT_length C1 t ht
  have hU : (jT C2 v2).length = 2 * C2 + 2 := jT_length C2 v2 hv2
  have hq6 : (cntT G g).length + (cntT P2 r).length + (jT CB v1).length
      + (jT C1 t).length + (jT C2 v2).length + (jT NV w).length
      = 2 * G + 2 * P2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 12 := by
    rw [hW, hQ, hR, hS, hU, jT_length NV w hw]; omega
  have f0 := s6_skipWs bv (cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t
      ++ (jT C2 v2 ++ (jT NV w ++ encodeD out)))))) 0 G false
    (fun i hi => by simpa using cntE_lo G g _ i hg hi)
  simp only [Nat.zero_add] at f0
  have f0' := s6_crossW (bv := bv) (s := if G = 0 then false else true) (p := 2 * G)
    (T := cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t
      ++ (jT C2 v2 ++ (jT NV w ++ encodeD out))))))
    (cntE_cm_lo G g _ hg) (cntE_cm_hi G g _ hg)
  have f1 := s6_skipRs bv (cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t
      ++ (jT C2 v2 ++ (jT NV w ++ encodeD out)))))) (2 * G + 2) P2 false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * i = 2 * G + 2 + (2 * i) from rfl]
      exact liftJ _ _ hW (cntE_lo P2 r _ i hr hi))
  have f1' := s6_crossR (bv := bv) (s := if P2 = 0 then false else true) (p := 2 * G + 2 + 2 * P2)
    (T := cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t
      ++ (jT C2 v2 ++ (jT NV w ++ encodeD out))))))
    (by rw [show 2 * G + 2 + 2 * P2 = 2 * G + 2 + (2 * P2) from rfl]
        exact liftJ _ _ hW (cntE_cm_lo P2 r _ hr))
    (by rw [show 2 * G + 2 + 2 * P2 + 1 = 2 * G + 2 + (2 * P2 + 1) from by omega]
        exact liftJ _ _ hW (cntE_cm_hi P2 r _ hr))
  have f2 := s6_walkBs bv (cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t
      ++ (jT C2 v2 ++ (jT NV w ++ encodeD out)))))) (2 * G + 2 + 2 * P2 + 2) v1 false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * i = 2 * G + 2 + (2 * P2 + 2 + 2 * i)
          from by omega, ← jsT_zero CB v1]
      exact liftJ2 _ _ _ hW hQ
        (jsE_data CB v1 0 _ (2 * i) (by omega) (by omega) (by omega)))
  have f2' := s6_hopB (bv := bv) (s := if v1 = 0 then false else true)
    (p := 2 * G + 2 + 2 * P2 + 2 + 2 * v1)
    (T := cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t
      ++ (jT C2 v2 ++ (jT NV w ++ encodeD out))))))
    (by rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * v1 = 2 * G + 2 + (2 * P2 + 2 + 2 * v1)
          from by omega, ← jsT_zero CB v1]
        exact liftJ2 _ _ _ hW hQ (jsE_m_lo CB v1 0 _ (by omega)))
  have f3 := s6_padBs bv (cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t
      ++ (jT C2 v2 ++ (jT NV w ++ encodeD out)))))) (2 * G + 2 + 2 * P2 + 2 + 2 * v1 + 2)
    (CB - v1) (if v1 = 0 then false else true)
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
  have f3' := s6_padB_bound (bv := bv)
    (s := if CB - v1 = 0 then (if v1 = 0 then false else true) else false)
    (p := 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2)
    (T := cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t
      ++ (jT C2 v2 ++ (jT NV w ++ encodeD out))))))
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
  have f4 := s6_walkTs bv (cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t
      ++ (jT C2 v2 ++ (jT NV w ++ encodeD out))))))
    (2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2) t false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * i
          = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + 2 * i)) from by omega,
        ← jsT_zero C1 t]
      exact liftJ3 _ _ _ _ hW hQ hR
        (jsE_data C1 t 0 _ (2 * i) (by omega) (by omega) (by omega)))
  have f4' := s6_hopT (bv := bv) (s := if t = 0 then false else true)
    (p := 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * t)
    (T := cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t
      ++ (jT C2 v2 ++ (jT NV w ++ encodeD out))))))
    (by rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * t
          = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + 2 * t)) from by omega,
        ← jsT_zero C1 t]
        exact liftJ3 _ _ _ _ hW hQ hR (jsE_m_lo C1 t 0 _ (by omega)))
  have f5 := s6_padTs bv (cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t
      ++ (jT C2 v2 ++ (jT NV w ++ encodeD out))))))
    (2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * t + 2) (C1 - t)
    (if t = 0 then false else true)
    (fun i hi => ⟨by
      rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * t + 2 + 2 * i
          = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * t + 2 + 2 * i))) from by omega,
        ← jsT_zero C1 t]
      exact liftJ3 _ _ _ _ hW hQ hR (jsE_pad C1 t 0 _ (2 * t + 2 + 2 * i)
        (by omega) ht (by omega) (by omega)), by
      rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * t + 2 + 2 * i + 1
          = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * t + 2 + 2 * i + 1)))
          from by omega, ← jsT_zero C1 t]
      exact liftJ3 _ _ _ _ hW hQ hR (jsE_pad C1 t 0 _ (2 * t + 2 + 2 * i + 1)
        (by omega) ht (by omega) (by omega))⟩)
  rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * t + 2 + 2 * (C1 - t)
      = 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 from by omega] at f5
  have f5' := s6_padT_bound (bv := bv)
    (s := if C1 - t = 0 then (if t = 0 then false else true) else false)
    (p := 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2)
    (T := cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t
      ++ (jT C2 v2 ++ (jT NV w ++ encodeD out))))))
    (by rcases Nat.eq_zero_or_pos v2 with h0 | h0
        · right
          constructor
          · rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2
                = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + 2 * v2)))
                from by omega, ← jsT_zero C2 v2]
            exact liftJ4 _ _ _ _ _ hW hQ hR hS (jsE_m_lo C2 v2 0 _ (by omega))
          · rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 1
                = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * v2 + 1))))
                from by omega, ← jsT_zero C2 v2]
            exact liftJ4 _ _ _ _ _ hW hQ hR hS (jsE_m_hi C2 v2 0 _ (by omega))
        · left
          rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2
              = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * C1 + 2))) from by omega,
            ← jsT_zero C2 v2]
          exact liftJ4 _ _ _ _ _ hW hQ hR hS
            (jsE_data C2 v2 0 _ 0 (by omega) (by omega) (by omega)))
  have f6 := s6_walkJs bv (cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t
      ++ (jT C2 v2 ++ (jT NV w ++ encodeD out))))))
    (2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2) v2 false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * i
          = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + 2 * i)))
          from by omega, ← jsT_zero C2 v2]
      exact liftJ4 _ _ _ _ _ hW hQ hR hS
        (jsE_data C2 v2 0 _ (2 * i) (by omega) (by omega) (by omega)))
  have f6' := s6_hopJ (bv := bv) (s := if v2 = 0 then false else true)
    (p := 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * v2)
    (T := cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t
      ++ (jT C2 v2 ++ (jT NV w ++ encodeD out))))))
    (by rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * v2
          = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + 2 * v2)))
          from by omega, ← jsT_zero C2 v2]
        exact liftJ4 _ _ _ _ _ hW hQ hR hS (jsE_m_lo C2 v2 0 _ (by omega)))
  have f7 := s6_padJs bv (cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t
      ++ (jT C2 v2 ++ (jT NV w ++ encodeD out))))))
    (2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * v2 + 2) (C2 - v2)
    (if v2 = 0 then false else true)
    (fun i hi => ⟨by
      rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * v2 + 2 + 2 * i
          = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * C1 + 2
              + (2 * v2 + 2 + 2 * i)))) from by omega, ← jsT_zero C2 v2]
      exact liftJ4 _ _ _ _ _ hW hQ hR hS (jsE_pad C2 v2 0 _ (2 * v2 + 2 + 2 * i)
        (by omega) hv2 (by omega) (by omega)), by
      rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * v2 + 2 + 2 * i + 1
          = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * C1 + 2
              + (2 * v2 + 2 + 2 * i + 1)))) from by omega, ← jsT_zero C2 v2]
      exact liftJ4 _ _ _ _ _ hW hQ hR hS (jsE_pad C2 v2 0 _ (2 * v2 + 2 + 2 * i + 1)
        (by omega) hv2 (by omega) (by omega))⟩)
  rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * v2 + 2 + 2 * (C2 - v2)
      = 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 from by omega] at f7
  have f7' := s6_padJ_bound (bv := bv)
    (s := if C2 - v2 = 0 then (if v2 = 0 then false else true) else false)
    (p := 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2)
    (T := cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t
      ++ (jT C2 v2 ++ (jT NV w ++ encodeD out))))))
    (by rcases Nat.eq_zero_or_pos w with h0 | h0
        · right
          constructor
          · rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2
                = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2
                    + 2 * w)))) from by omega, ← jsT_zero NV w]
            exact liftJ5 _ _ _ _ _ _ hW hQ hR hS hU (jsE_m_lo NV w 0 _ (by omega))
          · rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 1
                = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2
                    + (2 * w + 1))))) from by omega, ← jsT_zero NV w]
            exact liftJ5 _ _ _ _ _ _ hW hQ hR hS hU (jsE_m_hi NV w 0 _ (by omega))
        · left
          rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2
              = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2))))
              from by omega, ← jsT_zero NV w]
          exact liftJ5 _ _ _ _ _ _ hW hQ hR hS hU
            (jsE_data NV w 0 _ 0 (by omega) (by omega) (by omega)))
  have f8 := s6_walkVs bv (cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t
      ++ (jT C2 v2 ++ (jT NV w ++ encodeD out))))))
    (2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2) w false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * i
          = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2
              + 2 * i)))) from by omega, ← jsT_zero NV w]
      exact liftJ5 _ _ _ _ _ _ hW hQ hR hS hU
        (jsE_data NV w 0 _ (2 * i) (by omega) (by omega) (by omega)))
  have f8' := s6_hopV (bv := bv) (s := if w = 0 then false else true)
    (p := 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * w)
    (T := cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t
      ++ (jT C2 v2 ++ (jT NV w ++ encodeD out))))))
    (by rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * w
          = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2 + 2 * w))))
          from by omega, ← jsT_zero NV w]
        exact liftJ5 _ _ _ _ _ _ hW hQ hR hS hU (jsE_m_lo NV w 0 _ (by omega)))
  have f9 := s6_scans bv (cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t
      ++ (jT C2 v2 ++ (jT NV w ++ encodeD out))))))
    (2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * w + 2)
    ((NV - w) + out.length) (if w = 0 then false else true)
    (fun i hi => by
      rcases Nat.lt_or_ge i (NV - w) with hilt | hige
      · have e1 : (cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t ++ (jT C2 v2
            ++ (jT NV w ++ encodeD out)))))).getD
            (2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * w + 2
              + 2 * i) false = false := by
          rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2
                + 2 * w + 2 + 2 * i
              = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2
                  + (2 * w + 2 + 2 * i))))) from by omega, ← jsT_zero NV w]
          exact liftJ5 _ _ _ _ _ _ hW hQ hR hS hU
            (jsE_pad NV w 0 _ (2 * w + 2 + 2 * i) (by omega) hw (by omega) (by omega))
        have e2 : (cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t ++ (jT C2 v2
            ++ (jT NV w ++ encodeD out)))))).getD
            (2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * w + 2
              + 2 * i + 1) false = false := by
          rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2
                + 2 * w + 2 + 2 * i + 1
              = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2
                  + (2 * w + 2 + 2 * i + 1))))) from by omega, ← jsT_zero NV w]
          exact liftJ5 _ _ _ _ _ _ hW hQ hR hS hU
            (jsE_pad NV w 0 _ (2 * w + 2 + 2 * i + 1) (by omega) hw (by omega)
              (by omega))
        rw [e1, e2]
      · rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * w
              + 2 + 2 * i
            = 2 * G + 2 * P2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 12
                + 2 * (i - (NV - w)) from by omega]
        exact preD6_data_eq (cntT G g) (cntT P2 r) (jT CB v1) (jT C1 t) (jT C2 v2)
          (jT NV w) out (2 * G + 2 * P2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 12)
          (i - (NV - w)) hq6 (by omega))
  rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * w + 2
        + 2 * ((NV - w) + out.length)
      = 2 * G + 2 * P2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 12 + 2 * out.length
      from by omega] at f9
  have f10 := s6_detect (bv := bv)
    (s := storedD (cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t ++ (jT C2 v2
      ++ (jT NV w ++ encodeD out))))))
      (2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * w + 2)
      (if w = 0 then false else true) ((NV - w) + out.length))
    (p := 2 * G + 2 * P2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 12 + 2 * out.length)
    (preD6_mark_lo (cntT G g) (cntT P2 r) (jT CB v1) (jT C1 t) (jT C2 v2) (jT NV w) out
      (2 * G + 2 * P2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 12) hq6)
    (preD6_mark_hi (cntT G g) (cntT P2 r) (jT CB v1) (jT C1 t) (jT C2 v2) (jT NV w) out
      (2 * G + 2 * P2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 12) hq6)
  have f11 := s6_four (bv := bv) (s := false)
    (p := 2 * G + 2 * P2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 12 + 2 * out.length)
    (T := cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t
      ++ (jT C2 v2 ++ (jT NV w ++ encodeD out))))))
  rw [writes_snoc6 (cntT G g) (cntT P2 r) (jT CB v1) (jT C1 t) (jT C2 v2) (jT NV w) out
    (2 * G + 2 * P2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 12) hq6 bv] at f11
  rw [init_s6,
    show 2 * G + 2 * P2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 2 * out.length + 24
      = 2 * G + (2 + (2 * P2 + (2 + (2 * v1 + (2 + (2 * (CB - v1) + (2 + (2 * t + (2
          + (2 * (C1 - t) + (2 + (2 * v2 + (2 + (2 * (C2 - v2) + (2 + (2 * w + (2
          + (2 * ((NV - w) + out.length) + (2 + 4))))))))))))))))))) from by omega,
    run_add, f0, run_add, f0', run_add, f1, run_add, f1', run_add, f2, run_add, f2',
    run_add, f3, run_add, f3', run_add, f4, run_add, f4', run_add, f5, run_add, f5',
    run_add, f6, run_add, f6', run_add, f7, run_add, f7', run_add, f8, run_add, f8',
    run_add, f9, run_add, f10, f11,
    show 2 * G + 2 * P2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 12 + 2 * out.length + 3
      = 2 * G + 2 * P2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 2 * out.length + 15
      from by omega]

theorem snoc6_halt (bv : Bool) : (snoc6Machine bv).halt ((28 : Fin 29), false) = true := rfl

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitSnoc6
