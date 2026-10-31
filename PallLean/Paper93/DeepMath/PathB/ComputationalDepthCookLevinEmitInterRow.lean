import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitPairT
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitSeq
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitRepP

/-!
# Cook–Levin M2 emitter — the row interstitial and THE TRIANGLE ROW LOOP

Two deliverables close the triangle's row level (TRIANGLE_PLAN.md):

* **`interRowMachine`** — the row interstitial: on the post-engine six-region layout
  `cntT G g ++ (cntT P2 r ++ (jT CB j ++ (jT C1 t ++ (jT C2 j ++ (jT NV j ++ E)))))` it makes
  ONE left-to-right pass — skip the grand and row counters, `jT_incr` the bound mirror
  (`jT CB j ↦ jT CB (j+1)`), cross its pad, skip the `t`-mirror whole (data, marker, pad),
  `jT_incr` the `j`-source mirror (`jT C2 j ↦ jT C2 (j+1)`), cross its pad, and zero the live
  variable (`jT NV j ↦ jT NV 0` — the `zeroT` walk applies to the unsaturated variable by
  splitting the padding off: `jT NV j ++ E = jT j j ++ (pad ++ E)`) — then halts.  One machine
  (`Fin 29`) re-arms the row for the next round: the `interT` pattern with two increments.

* **`repP_pairRow_run`** — THE TRIANGLE ROW LOOP: `repPMachine` over
  `seqMachine (pairTMachine body) interRowMachine` runs `P` row rounds under the grand prefix;
  round `r` runs the engine at row `j = r+1` (bound mirror `j`, second source `j`, live
  `i = 0..j-1`) and the interstitial advances both mirrors and re-arms the live variable; the
  final tape carries `⋃_{1 ≤ j ≤ P} loop3Out body t j j` — the row-`j` slices of the triangle
  at grand time `t`.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitInterRow

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinCNFEncode
open PallLean.Paper93.DeepMath.PathB.CookLevinVarIndex
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSplice
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRange
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitNestVar
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg2 (W4_append_right2)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg3
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg3P (liftJ4 W4_append_right4)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitFamilyBodies
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRearm (W2_append_right3)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSeq
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRepP
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitPairT

/-! ## The padding split for the unsaturated zeroing

The live variable ends a row at `jT NV j` with `j ≤ NV` — NOT saturated.  Splitting the
padding off exposes a saturated `jT j j`, so the whole proven `zeroT` walk applies verbatim
with the padding absorbed into the suffix. -/

theorem jT_split_pad (NV j : ℕ) (E : List Bool) :
    jT NV j ++ E = jT j j ++ (List.replicate (2 * (NV - j)) false ++ E) := by
  simp [jT, List.append_assoc]

theorem jT_join_pad (NV j : ℕ) (hj : j ≤ NV) (E : List Bool) :
    jT j 0 ++ (List.replicate (2 * (NV - j)) false ++ E) = jT NV 0 ++ E := by
  simp only [jT, Nat.sub_zero, Nat.mul_zero, List.replicate_zero, List.nil_append,
    List.cons_append]
  rw [← List.append_assoc (List.replicate (2 * j) false), ← List.replicate_add,
    show 2 * j + 2 * (NV - j) = 2 * NV from by omega]

/-- The two-write pair under five prefixes (the zeroing writes on the live region). -/
theorem W2_append_right5 (A B C D E X : List Bool) (qa qb qc qd qe p : ℕ) (b1 b2 : Bool)
    (ha : A.length = qa) (hb : B.length = qb) (hc : C.length = qc) (hd : D.length = qd)
    (he : E.length = qe) (hp : p + 1 < X.length) :
    writeAt (writeAt (A ++ (B ++ (C ++ (D ++ (E ++ X)))))
        (qa + (qb + (qc + (qd + (qe + p))))) b1)
        (qa + (qb + (qc + (qd + (qe + p)))) + 1) b2
      = A ++ (B ++ (C ++ (D ++ (E ++ writeAt (writeAt X p b1) (p + 1) b2)))) := by
  have hl1 : (writeAt X p b1).length = X.length := by
    rw [writeAt_of_lt b1 (by omega), List.length_set]
  rw [writeAt_append_right5 A B C D E X qa qb qc qd qe p b1 ha hb hc hd he (by omega),
    show qa + (qb + (qc + (qd + (qe + p)))) + 1
      = qa + (qb + (qc + (qd + (qe + (p + 1))))) from by omega,
    writeAt_append_right5 A B C D E _ qa qb qc qd qe (p + 1) b2 ha hb hc hd he
      (by rw [hl1]; omega)]

/-! ## The machine

`Fin 29 × Bool`: `0/1` skip the grand counter, `2/3` skip the row counter, `4/5` walk the
bound mirror's filled pairs, `6,7,8` its four-write increment, `9/10` cross its pad, `11/12`
walk the `t`-mirror's filled pairs, `13` hop its marker, `14/15` cross its pad, `16/17` walk
the `j`-source's filled pairs, `18,19,20` its four-write increment, `21/22` cross its pad,
`23,24` the zeroing head pair, `25/26/27` the zeroing loop, `28` halt.  Every pad exit resets
the carried bit (the pairT pad-crossing convention). -/

def interRowMachine : Machine where
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
      (if b then ((5, b), none, 1) else ((6, s.2), some true, 1))
    else if s.1 = 5 then ((4, s.2), none, 1)
    else if s.1 = 6 then ((7, s.2), some true, 1)
    else if s.1 = 7 then ((8, s.2), some false, 1)
    else if s.1 = 8 then ((9, s.2), some true, 1)
    else if s.1 = 9 then ((10, b), none, 1)
    else if s.1 = 10 then
      (if s.2 then ((11, false), none, 0)
       else (if b then ((11, false), none, 0) else ((9, s.2), none, 1)))
    else if s.1 = 11 then
      (if b then ((12, b), none, 1) else ((13, s.2), none, 1))
    else if s.1 = 12 then ((11, s.2), none, 1)
    else if s.1 = 13 then ((14, s.2), none, 1)
    else if s.1 = 14 then ((15, b), none, 1)
    else if s.1 = 15 then
      (if s.2 then ((16, false), none, 0)
       else (if b then ((16, false), none, 0) else ((14, s.2), none, 1)))
    else if s.1 = 16 then
      (if b then ((17, b), none, 1) else ((18, s.2), some true, 1))
    else if s.1 = 17 then ((16, s.2), none, 1)
    else if s.1 = 18 then ((19, s.2), some true, 1)
    else if s.1 = 19 then ((20, s.2), some false, 1)
    else if s.1 = 20 then ((21, s.2), some true, 1)
    else if s.1 = 21 then ((22, b), none, 1)
    else if s.1 = 22 then
      (if s.2 then ((23, false), none, 0)
       else (if b then ((23, false), none, 0) else ((21, s.2), none, 1)))
    else if s.1 = 23 then ((24, s.2), some false, 1)
    else if s.1 = 24 then ((25, s.2), some true, 1)
    else if s.1 = 25 then
      (if b then ((26, b), some false, 1) else ((27, b), some false, 1))
    else if s.1 = 26 then ((25, s.2), some false, 1)
    else if s.1 = 27 then ((28, s.2), some false, 2)
    else ((s.1, s.2), none, 2)
  accept := fun _ => false

theorem init_ir (t : List Bool) : init interRowMachine t = ⟨(0, false), 0, t⟩ := rfl

/-! ## The step layer -/

section StepsIR
variable {s : Bool} {p : ℕ} {T : List Bool}

theorem ir_skipW (h1 : T.getD p false = true) :
    run interRowMachine 2 ⟨(0, s), p, T⟩ = ⟨(0, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step interRowMachine ⟨(0, s), p, T⟩ = ⟨(1, T.getD p false), p + 1, T⟩ := by
    simp only [step, interRowMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, interRowMachine, moveHead]; rfl

theorem ir_crossW (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run interRowMachine 2 ⟨(0, s), p, T⟩ = ⟨(2, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step interRowMachine ⟨(0, s), p, T⟩ = ⟨(1, T.getD p false), p + 1, T⟩ := by
    simp only [step, interRowMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, interRowMachine, moveHead, h2]

theorem ir_skipR (h1 : T.getD p false = true) :
    run interRowMachine 2 ⟨(2, s), p, T⟩ = ⟨(2, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step interRowMachine ⟨(2, s), p, T⟩ = ⟨(3, T.getD p false), p + 1, T⟩ := by
    simp only [step, interRowMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, interRowMachine, moveHead]; rfl

theorem ir_crossR (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run interRowMachine 2 ⟨(2, s), p, T⟩ = ⟨(4, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step interRowMachine ⟨(2, s), p, T⟩ = ⟨(3, T.getD p false), p + 1, T⟩ := by
    simp only [step, interRowMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, interRowMachine, moveHead, h2]

theorem ir_walkB (h1 : T.getD p false = true) :
    run interRowMachine 2 ⟨(4, s), p, T⟩ = ⟨(4, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step interRowMachine ⟨(4, s), p, T⟩ = ⟨(5, true), p + 1, T⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, interRowMachine, moveHead, h1']
  rw [e0]
  simp only [step, interRowMachine, moveHead]; rfl

/-- The four-write increment at the bound mirror's marker. -/
theorem ir_four_incrB (h1 : T.getD p false = false) :
    run interRowMachine 4 ⟨(4, s), p, T⟩
      = ⟨(9, s), p + 4, writeAt (writeAt (writeAt (writeAt T p true)
          (p + 1) true) (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e0 : step interRowMachine ⟨(4, s), p, T⟩ = ⟨(6, s), p + 1, writeAt T p true⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, interRowMachine, moveHead, h1']
  have e1 : ∀ p' T', step interRowMachine ⟨(6, s), p', T'⟩
      = ⟨(7, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, interRowMachine, moveHead]; rfl
  have e2 : ∀ p' T', step interRowMachine ⟨(7, s), p', T'⟩
      = ⟨(8, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, interRowMachine, moveHead]; rfl
  have e3 : ∀ p' T', step interRowMachine ⟨(8, s), p', T'⟩
      = ⟨(9, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, interRowMachine, moveHead]; rfl
  rw [e0, e1, e2, e3]

theorem ir_padB (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = false) :
    run interRowMachine 2 ⟨(9, s), p, T⟩ = ⟨(9, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step interRowMachine ⟨(9, s), p, T⟩ = ⟨(10, T.getD p false), p + 1, T⟩ := by
    simp only [step, interRowMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, interRowMachine, moveHead, h2]

theorem ir_padB_boundT (h1 : T.getD p false = true) :
    run interRowMachine 2 ⟨(9, s), p, T⟩ = ⟨(11, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step interRowMachine ⟨(9, s), p, T⟩ = ⟨(10, T.getD p false), p + 1, T⟩ := by
    simp only [step, interRowMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, interRowMachine, moveHead]; rfl

theorem ir_padB_boundM (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run interRowMachine 2 ⟨(9, s), p, T⟩ = ⟨(11, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step interRowMachine ⟨(9, s), p, T⟩ = ⟨(10, T.getD p false), p + 1, T⟩ := by
    simp only [step, interRowMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, interRowMachine, moveHead, h2]

theorem ir_padB_bound
    (h : T.getD p false = true ∨ (T.getD p false = false ∧ T.getD (p + 1) false = true)) :
    run interRowMachine 2 ⟨(9, s), p, T⟩ = ⟨(11, false), p, T⟩ := by
  rcases h with h1 | ⟨h1, h2⟩
  · exact ir_padB_boundT h1
  · exact ir_padB_boundM h1 h2

theorem ir_walkT (h1 : T.getD p false = true) :
    run interRowMachine 2 ⟨(11, s), p, T⟩ = ⟨(11, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step interRowMachine ⟨(11, s), p, T⟩ = ⟨(12, true), p + 1, T⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, interRowMachine, moveHead, h1']
  rw [e0]
  simp only [step, interRowMachine, moveHead]; rfl

/-- The `t`-mirror's marker hop: two blind cells into its padding. -/
theorem ir_hopT (h1 : T.getD p false = false) :
    run interRowMachine 2 ⟨(11, s), p, T⟩ = ⟨(14, s), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step interRowMachine ⟨(11, s), p, T⟩ = ⟨(13, s), p + 1, T⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, interRowMachine, moveHead, h1']
  rw [e0]
  simp only [step, interRowMachine, moveHead]; rfl

theorem ir_padT (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = false) :
    run interRowMachine 2 ⟨(14, s), p, T⟩ = ⟨(14, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step interRowMachine ⟨(14, s), p, T⟩ = ⟨(15, T.getD p false), p + 1, T⟩ := by
    simp only [step, interRowMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, interRowMachine, moveHead, h2]

theorem ir_padT_boundT (h1 : T.getD p false = true) :
    run interRowMachine 2 ⟨(14, s), p, T⟩ = ⟨(16, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step interRowMachine ⟨(14, s), p, T⟩ = ⟨(15, T.getD p false), p + 1, T⟩ := by
    simp only [step, interRowMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, interRowMachine, moveHead]; rfl

theorem ir_walkJ (h1 : T.getD p false = true) :
    run interRowMachine 2 ⟨(16, s), p, T⟩ = ⟨(16, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step interRowMachine ⟨(16, s), p, T⟩ = ⟨(17, true), p + 1, T⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, interRowMachine, moveHead, h1']
  rw [e0]
  simp only [step, interRowMachine, moveHead]; rfl

/-- The four-write increment at the `j`-source mirror's marker. -/
theorem ir_four_incrJ (h1 : T.getD p false = false) :
    run interRowMachine 4 ⟨(16, s), p, T⟩
      = ⟨(21, s), p + 4, writeAt (writeAt (writeAt (writeAt T p true)
          (p + 1) true) (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e0 : step interRowMachine ⟨(16, s), p, T⟩ = ⟨(18, s), p + 1, writeAt T p true⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, interRowMachine, moveHead, h1']
  have e1 : ∀ p' T', step interRowMachine ⟨(18, s), p', T'⟩
      = ⟨(19, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, interRowMachine, moveHead]; rfl
  have e2 : ∀ p' T', step interRowMachine ⟨(19, s), p', T'⟩
      = ⟨(20, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, interRowMachine, moveHead]; rfl
  have e3 : ∀ p' T', step interRowMachine ⟨(20, s), p', T'⟩
      = ⟨(21, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, interRowMachine, moveHead]; rfl
  rw [e0, e1, e2, e3]

theorem ir_padJ (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = false) :
    run interRowMachine 2 ⟨(21, s), p, T⟩ = ⟨(21, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step interRowMachine ⟨(21, s), p, T⟩ = ⟨(22, T.getD p false), p + 1, T⟩ := by
    simp only [step, interRowMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, interRowMachine, moveHead, h2]

theorem ir_padJ_boundT (h1 : T.getD p false = true) :
    run interRowMachine 2 ⟨(21, s), p, T⟩ = ⟨(23, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step interRowMachine ⟨(21, s), p, T⟩ = ⟨(22, T.getD p false), p + 1, T⟩ := by
    simp only [step, interRowMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, interRowMachine, moveHead]; rfl

/-- The zeroing head-pair: `false, true` blind writes. -/
theorem ir_two_head {s' : Bool} :
    run interRowMachine 2 ⟨(23, s'), p, T⟩
      = ⟨(25, s'), p + 2, writeAt (writeAt T p false) (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e4 : step interRowMachine ⟨(23, s'), p, T⟩
      = ⟨(24, s'), p + 1, writeAt T p false⟩ := by
    simp only [step, interRowMachine, moveHead]; rfl
  have e5 : ∀ p' T', step interRowMachine ⟨(24, s'), p', T'⟩
      = ⟨(25, s'), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, interRowMachine, moveHead]; rfl
  rw [e4, e5]

theorem ir_zero_step (h : T.getD p false = true) :
    run interRowMachine 2 ⟨(25, s), p, T⟩
      = ⟨(25, true), p + 2, writeAt (writeAt T p false) (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e6 : step interRowMachine ⟨(25, s), p, T⟩
      = ⟨(26, true), p + 1, writeAt T p false⟩ := by
    have h' := h
    rw [List.getD_eq_getElem?_getD] at h'
    simp [step, interRowMachine, moveHead, h']
  rw [e6]
  simp only [step, interRowMachine, moveHead]; rfl

theorem ir_zero_last (h : T.getD p false = false) :
    run interRowMachine 2 ⟨(25, s), p, T⟩
      = ⟨(28, false), p + 1, writeAt (writeAt T p false) (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e6 : step interRowMachine ⟨(25, s), p, T⟩
      = ⟨(27, false), p + 1, writeAt T p false⟩ := by
    have h' := h
    rw [List.getD_eq_getElem?_getD] at h'
    simp [step, interRowMachine, moveHead, h']
  rw [e6]
  simp only [step, interRowMachine, moveHead]; rfl

end StepsIR

/-! ## Scan invariants -/

theorem ir_skipWs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run interRowMachine (2 * k) ⟨(0, s), q, T⟩
      = ⟨(0, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), ir_skipW (h k (by omega))]
    rfl

theorem ir_skipRs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run interRowMachine (2 * k) ⟨(2, s), q, T⟩
      = ⟨(2, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), ir_skipR (h k (by omega))]
    rfl

theorem ir_walkBs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run interRowMachine (2 * k) ⟨(4, s), q, T⟩
      = ⟨(4, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), ir_walkB (h k (by omega))]
    rfl

theorem ir_padBs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = false
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run interRowMachine (2 * k) ⟨(9, s), q, T⟩
      = ⟨(9, if k = 0 then s else false), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), ir_padB hk.1 hk.2]
    rfl

theorem ir_walkTs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run interRowMachine (2 * k) ⟨(11, s), q, T⟩
      = ⟨(11, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), ir_walkT (h k (by omega))]
    rfl

theorem ir_padTs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = false
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run interRowMachine (2 * k) ⟨(14, s), q, T⟩
      = ⟨(14, if k = 0 then s else false), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), ir_padT hk.1 hk.2]
    rfl

theorem ir_walkJs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run interRowMachine (2 * k) ⟨(16, s), q, T⟩
      = ⟨(16, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), ir_walkJ (h k (by omega))]
    rfl

theorem ir_padJs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = false
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run interRowMachine (2 * k) ⟨(21, s), q, T⟩
      = ⟨(21, if k = 0 then s else false), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), ir_padJ hk.1 hk.2]
    rfl

/-- The zeroing walk (evolving `zeroT`, five prefixes). -/
theorem ir_zeros (W Q R S U : List Bool) (G P2 CB C1 C2 P : ℕ) (E : List Bool)
    (hW : W.length = 2 * G + 2) (hQ : Q.length = 2 * P2 + 2) (hR : R.length = 2 * CB + 2)
    (hS : S.length = 2 * C1 + 2) (hU : U.length = 2 * C2 + 2) (hP : 0 < P) (s : Bool)
    (m : ℕ) (hm : m ≤ P - 1) :
    run interRowMachine (2 * m)
      ⟨(25, s), 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2,
        W ++ (Q ++ (R ++ (S ++ (U ++ (zeroT P 0 ++ E)))))⟩
      = ⟨(25, if m = 0 then s else true),
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
      ir_zero_step hlo, hw]
    rfl

/-! ## THE ROW INTERSTITIAL RUN -/

/-- **The row interstitial**: one pass increments the bound mirror and the `j`-source mirror
in place (`jT CB j ↦ jT CB (j+1)`, `jT C2 j ↦ jT C2 (j+1)`), skips the `t`-mirror whole, and
re-arms the live variable (`jT NV j ↦ jT NV 0`) — the grand and row counters untouched. -/
theorem interRow_run (G g : ℕ) (hg : g ≤ G) (P2 r : ℕ) (hr : r ≤ P2) (CB C1 C2 NV j t : ℕ)
    (hj0 : 0 < j) (hjB : j < CB) (htC : t ≤ C1) (hjC : j < C2) (hjV : j ≤ NV)
    (E : List Bool) :
    run interRowMachine (2 * G + 2 * P2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * j + 18)
      (init interRowMachine (cntT G g ++ (cntT P2 r ++ (jT CB j ++ (jT C1 t
        ++ (jT C2 j ++ (jT NV j ++ E)))))))
      = ⟨(28, false), 2 * G + 2 * P2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * j + 11,
          cntT G g ++ (cntT P2 r ++ (jT CB (j + 1) ++ (jT C1 t
            ++ (jT C2 (j + 1) ++ (jT NV 0 ++ E)))))⟩ := by
  have hW : (cntT G g).length = 2 * G + 2 := cntT_length G g hg
  have hQ : (cntT P2 r).length = 2 * P2 + 2 := cntT_length P2 r hr
  have hR : (jT CB (j + 1)).length = 2 * CB + 2 := jT_length CB (j + 1) (by omega)
  have hS : (jT C1 t).length = 2 * C1 + 2 := jT_length C1 t htC
  have hU : (jT C2 (j + 1)).length = 2 * C2 + 2 := jT_length C2 (j + 1) (by omega)
  have f0 := ir_skipWs (cntT G g ++ (cntT P2 r ++ (jT CB j ++ (jT C1 t
      ++ (jT C2 j ++ (jT NV j ++ E)))))) 0 G false
    (fun i hi => by simpa using cntE_lo G g _ i hg hi)
  simp only [Nat.zero_add] at f0
  have f0' := ir_crossW (s := if G = 0 then false else true) (p := 2 * G)
    (T := cntT G g ++ (cntT P2 r ++ (jT CB j ++ (jT C1 t ++ (jT C2 j ++ (jT NV j ++ E))))))
    (cntE_cm_lo G g _ hg) (cntE_cm_hi G g _ hg)
  have f1 := ir_skipRs (cntT G g ++ (cntT P2 r ++ (jT CB j ++ (jT C1 t
      ++ (jT C2 j ++ (jT NV j ++ E)))))) (2 * G + 2) P2 false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * i = 2 * G + 2 + (2 * i) from rfl]
      exact liftJ _ _ hW (cntE_lo P2 r _ i hr hi))
  have f1' := ir_crossR (s := if P2 = 0 then false else true) (p := 2 * G + 2 + 2 * P2)
    (T := cntT G g ++ (cntT P2 r ++ (jT CB j ++ (jT C1 t ++ (jT C2 j ++ (jT NV j ++ E))))))
    (by rw [show 2 * G + 2 + 2 * P2 = 2 * G + 2 + (2 * P2) from rfl]
        exact liftJ _ _ hW (cntE_cm_lo P2 r _ hr))
    (by rw [show 2 * G + 2 + 2 * P2 + 1 = 2 * G + 2 + (2 * P2 + 1) from by omega]
        exact liftJ _ _ hW (cntE_cm_hi P2 r _ hr))
  have f2 := ir_walkBs (cntT G g ++ (cntT P2 r ++ (jT CB j ++ (jT C1 t
      ++ (jT C2 j ++ (jT NV j ++ E)))))) (2 * G + 2 + 2 * P2 + 2) j false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * i = 2 * G + 2 + (2 * P2 + 2 + 2 * i)
          from by omega, ← jsT_zero CB j]
      exact liftJ2 _ _ _ hW hQ
        (jsE_data CB j 0 _ (2 * i) (by omega) (by omega) (by omega)))
  have f3 := ir_four_incrB (s := if j = 0 then false else true)
    (p := 2 * G + 2 + 2 * P2 + 2 + 2 * j)
    (T := cntT G g ++ (cntT P2 r ++ (jT CB j ++ (jT C1 t ++ (jT C2 j ++ (jT NV j ++ E))))))
    (by rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * j = 2 * G + 2 + (2 * P2 + 2 + 2 * j)
          from by omega, ← jsT_zero CB j]
        exact liftJ2 _ _ _ hW hQ (jsE_m_lo CB j 0 _ (by omega)))
  rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * j = 2 * G + 2 + (2 * P2 + 2 + 2 * j) from by omega,
    W4_append_right2 (cntT G g) (cntT P2 r)
      (jT CB j ++ (jT C1 t ++ (jT C2 j ++ (jT NV j ++ E)))) (2 * G + 2) (2 * P2 + 2)
      (2 * j) true true false true hW hQ
      (by rw [List.length_append, jT_length CB j (by omega)]; omega),
    jT_incr CB j _ hjB] at f3
  have f4 := ir_padBs (cntT G g ++ (cntT P2 r ++ (jT CB (j + 1) ++ (jT C1 t
      ++ (jT C2 j ++ (jT NV j ++ E)))))) (2 * G + 2 + 2 * P2 + 2 + 2 * j + 4)
    (CB - j - 1) (if j = 0 then false else true)
    (fun i hi => ⟨by
      rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * j + 4 + 2 * i
          = 2 * G + 2 + (2 * P2 + 2 + (2 * (j + 1) + 2 + 2 * i)) from by omega,
        ← jsT_zero CB (j + 1)]
      exact liftJ2 _ _ _ hW hQ (jsE_pad CB (j + 1) 0 _ (2 * (j + 1) + 2 + 2 * i)
        (by omega) (by omega) (by omega) (by omega)), by
      rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * j + 4 + 2 * i + 1
          = 2 * G + 2 + (2 * P2 + 2 + (2 * (j + 1) + 2 + 2 * i + 1)) from by omega,
        ← jsT_zero CB (j + 1)]
      exact liftJ2 _ _ _ hW hQ (jsE_pad CB (j + 1) 0 _ (2 * (j + 1) + 2 + 2 * i + 1)
        (by omega) (by omega) (by omega) (by omega))⟩)
  rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * j + 4 + 2 * (CB - j - 1)
      = 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 from by omega] at f4
  have f5 := ir_padB_bound
    (s := if CB - j - 1 = 0 then (if j = 0 then false else true) else false)
    (p := 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2)
    (T := cntT G g ++ (cntT P2 r ++ (jT CB (j + 1) ++ (jT C1 t
      ++ (jT C2 j ++ (jT NV j ++ E))))))
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
  have f6 := ir_walkTs (cntT G g ++ (cntT P2 r ++ (jT CB (j + 1) ++ (jT C1 t
      ++ (jT C2 j ++ (jT NV j ++ E)))))) (2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2) t false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * i
          = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + 2 * i)) from by omega,
        ← jsT_zero C1 t]
      exact liftJ3 _ _ _ _ hW hQ hR
        (jsE_data C1 t 0 _ (2 * i) (by omega) (by omega) (by omega)))
  have f7 := ir_hopT (s := if t = 0 then false else true)
    (p := 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * t)
    (T := cntT G g ++ (cntT P2 r ++ (jT CB (j + 1) ++ (jT C1 t
      ++ (jT C2 j ++ (jT NV j ++ E))))))
    (by rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * t
          = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + 2 * t)) from by omega,
        ← jsT_zero C1 t]
        exact liftJ3 _ _ _ _ hW hQ hR (jsE_m_lo C1 t 0 _ (by omega)))
  have f8 := ir_padTs (cntT G g ++ (cntT P2 r ++ (jT CB (j + 1) ++ (jT C1 t
      ++ (jT C2 j ++ (jT NV j ++ E)))))) (2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * t + 2)
    (C1 - t) (if t = 0 then false else true)
    (fun i hi => ⟨by
      rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * t + 2 + 2 * i
          = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * t + 2 + 2 * i))) from by omega,
        ← jsT_zero C1 t]
      exact liftJ3 _ _ _ _ hW hQ hR (jsE_pad C1 t 0 _ (2 * t + 2 + 2 * i)
        (by omega) htC (by omega) (by omega)), by
      rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * t + 2 + 2 * i + 1
          = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * t + 2 + 2 * i + 1)))
          from by omega, ← jsT_zero C1 t]
      exact liftJ3 _ _ _ _ hW hQ hR (jsE_pad C1 t 0 _ (2 * t + 2 + 2 * i + 1)
        (by omega) htC (by omega) (by omega))⟩)
  rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * t + 2 + 2 * (C1 - t)
      = 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 from by omega] at f8
  have f9 := ir_padT_boundT
    (s := if C1 - t = 0 then (if t = 0 then false else true) else false)
    (p := 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2)
    (T := cntT G g ++ (cntT P2 r ++ (jT CB (j + 1) ++ (jT C1 t
      ++ (jT C2 j ++ (jT NV j ++ E))))))
    (by rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2
          = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + 0))) from by omega,
        ← jsT_zero C2 j]
        exact liftJ4 _ _ _ _ _ hW hQ hR hS
          (jsE_data C2 j 0 _ 0 (by omega) (by omega) (by omega)))
  have f10 := ir_walkJs (cntT G g ++ (cntT P2 r ++ (jT CB (j + 1) ++ (jT C1 t
      ++ (jT C2 j ++ (jT NV j ++ E)))))) (2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2)
    j false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * i
          = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + 2 * i))) from by omega,
        ← jsT_zero C2 j]
      exact liftJ4 _ _ _ _ _ hW hQ hR hS
        (jsE_data C2 j 0 _ (2 * i) (by omega) (by omega) (by omega)))
  have f11 := ir_four_incrJ (s := if j = 0 then false else true)
    (p := 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * j)
    (T := cntT G g ++ (cntT P2 r ++ (jT CB (j + 1) ++ (jT C1 t
      ++ (jT C2 j ++ (jT NV j ++ E))))))
    (by rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * j
          = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + 2 * j))) from by omega,
        ← jsT_zero C2 j]
        exact liftJ4 _ _ _ _ _ hW hQ hR hS (jsE_m_lo C2 j 0 _ (by omega)))
  rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * j
      = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + 2 * j))) from by omega,
    W4_append_right4 (cntT G g) (cntT P2 r) (jT CB (j + 1)) (jT C1 t)
      (jT C2 j ++ (jT NV j ++ E)) (2 * G + 2) (2 * P2 + 2) (2 * CB + 2) (2 * C1 + 2)
      (2 * j) true true false true hW hQ hR hS
      (by rw [List.length_append, jT_length C2 j (by omega)]; omega),
    jT_incr C2 j _ hjC] at f11
  have f12 := ir_padJs (cntT G g ++ (cntT P2 r ++ (jT CB (j + 1) ++ (jT C1 t
      ++ (jT C2 (j + 1) ++ (jT NV j ++ E))))))
    (2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * j + 4) (C2 - j - 1)
    (if j = 0 then false else true)
    (fun i hi => ⟨by
      rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * j + 4 + 2 * i
          = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * C1 + 2
              + (2 * (j + 1) + 2 + 2 * i)))) from by omega, ← jsT_zero C2 (j + 1)]
      exact liftJ4 _ _ _ _ _ hW hQ hR hS (jsE_pad C2 (j + 1) 0 _ (2 * (j + 1) + 2 + 2 * i)
        (by omega) (by omega) (by omega) (by omega)), by
      rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * j + 4 + 2 * i + 1
          = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * C1 + 2
              + (2 * (j + 1) + 2 + 2 * i + 1)))) from by omega, ← jsT_zero C2 (j + 1)]
      exact liftJ4 _ _ _ _ _ hW hQ hR hS
        (jsE_pad C2 (j + 1) 0 _ (2 * (j + 1) + 2 + 2 * i + 1) (by omega) (by omega)
          (by omega) (by omega))⟩)
  rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * j + 4 + 2 * (C2 - j - 1)
      = 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 from by omega] at f12
  have f13 := ir_padJ_boundT
    (s := if C2 - j - 1 = 0 then (if j = 0 then false else true) else false)
    (p := 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2)
    (T := cntT G g ++ (cntT P2 r ++ (jT CB (j + 1) ++ (jT C1 t
      ++ (jT C2 (j + 1) ++ (jT NV j ++ E))))))
    (by rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2
          = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2 + 0))))
          from by omega, ← jsT_zero NV j]
        exact liftJ5 _ _ _ _ _ _ hW hQ hR hS hU
          (jsE_data NV j 0 _ 0 (by omega) (by omega) (by omega)))
  have f14 := ir_two_head (s' := false)
    (p := 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2)
    (T := cntT G g ++ (cntT P2 r ++ (jT CB (j + 1) ++ (jT C1 t
      ++ (jT C2 (j + 1) ++ (jT NV j ++ E))))))
  have hw14 : writeAt (writeAt (cntT G g ++ (cntT P2 r ++ (jT CB (j + 1) ++ (jT C1 t
      ++ (jT C2 (j + 1) ++ (jT NV j ++ E))))))
      (2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2) false)
      (2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 1) true
      = cntT G g ++ (cntT P2 r ++ (jT CB (j + 1) ++ (jT C1 t ++ (jT C2 (j + 1)
          ++ (zeroT j 0 ++ (List.replicate (2 * (NV - j)) false ++ E)))))) := by
    rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2
        = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2 + 0))))
        from by omega,
      W2_append_right5 (cntT G g) (cntT P2 r) (jT CB (j + 1)) (jT C1 t) (jT C2 (j + 1)) _
        (2 * G + 2) (2 * P2 + 2) (2 * CB + 2) (2 * C1 + 2) (2 * C2 + 2) 0 false true hW hQ
        hR hS hU (by rw [List.length_append, jT_length NV j hjV]; omega),
      jT_split_pad NV j E, show (0 : ℕ) + 1 = 1 from rfl, zeroT_head j _ hj0]
  rw [hw14] at f14
  have f15 := ir_zeros (cntT G g) (cntT P2 r) (jT CB (j + 1)) (jT C1 t) (jT C2 (j + 1)) G
    P2 CB C1 C2 j (List.replicate (2 * (NV - j)) false ++ E) hW hQ hR hS hU hj0 false
    (j - 1) (le_refl _)
  have hlo16 : (cntT G g ++ (cntT P2 r ++ (jT CB (j + 1) ++ (jT C1 t ++ (jT C2 (j + 1)
      ++ (zeroT j (j - 1) ++ (List.replicate (2 * (NV - j)) false ++ E))))))).getD
      (2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 + 2 * (j - 1))
      false = false := by
    rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2
          + 2 * (j - 1)
        = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2 + 2 * j))))
        from by omega]
    exact liftJ5 _ _ _ _ _ _ hW hQ hR hS hU (zeroE_m_lo j _ hj0)
  have f16 := ir_zero_last (s := if j - 1 = 0 then false else true)
    (p := 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 + 2 * (j - 1))
    (T := cntT G g ++ (cntT P2 r ++ (jT CB (j + 1) ++ (jT C1 t ++ (jT C2 (j + 1)
      ++ (zeroT j (j - 1) ++ (List.replicate (2 * (NV - j)) false ++ E))))))) hlo16
  have hw16 : writeAt (writeAt (cntT G g ++ (cntT P2 r ++ (jT CB (j + 1) ++ (jT C1 t
      ++ (jT C2 (j + 1) ++ (zeroT j (j - 1)
        ++ (List.replicate (2 * (NV - j)) false ++ E)))))))
      (2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 + 2 * (j - 1))
      false)
      (2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 + 2 * (j - 1) + 1)
      false
      = cntT G g ++ (cntT P2 r ++ (jT CB (j + 1) ++ (jT C1 t ++ (jT C2 (j + 1)
          ++ (jT NV 0 ++ E))))) := by
    rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2
          + 2 * (j - 1)
        = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2 + 2 * j))))
        from by omega,
      W2_append_right5 (cntT G g) (cntT P2 r) (jT CB (j + 1)) (jT C1 t) (jT C2 (j + 1)) _
        (2 * G + 2) (2 * P2 + 2) (2 * CB + 2) (2 * C1 + 2) (2 * C2 + 2) (2 * j) false
        false hW hQ hR hS hU
        (by rw [List.length_append, zeroT_length j (j - 1) (le_refl _) hj0]; omega),
      zeroT_last j _ hj0, jT_join_pad NV j hjV E]
  rw [hw16] at f16
  rw [init_ir,
    show 2 * G + 2 * P2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * j + 18
      = 2 * G + (2 + (2 * P2 + (2 + (2 * j + (4 + (2 * (CB - j - 1) + (2 + (2 * t + (2
          + (2 * (C1 - t) + (2 + (2 * j + (4 + (2 * (C2 - j - 1) + (2 + (2
          + (2 * (j - 1) + 2))))))))))))))))) from by omega,
    run_add, f0, run_add, f0', run_add, f1, run_add, f1', run_add, f2,
    show 2 * G + 2 + 2 * P2 + 2 + 2 * j = 2 * G + 2 + (2 * P2 + 2 + 2 * j) from by omega,
    run_add, f3,
    show 2 * G + 2 + (2 * P2 + 2 + 2 * j) + 4 = 2 * G + 2 + 2 * P2 + 2 + 2 * j + 4
      from by omega,
    run_add, f4, run_add, f5, run_add, f6, run_add, f7, run_add, f8, run_add, f9,
    run_add, f10,
    show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * j
      = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + 2 * j))) from by omega,
    run_add, f11,
    show 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + 2 * j))) + 4
      = 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * j + 4 from by omega,
    run_add, f12, run_add, f13, run_add, f14, run_add, f15, f16,
    show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 + 2 * (j - 1)
        + 1
      = 2 * G + 2 * P2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * j + 11 from by omega]

theorem interRow_halt : interRowMachine.halt ((28 : Fin 29), false) = true := rfl

/-! ## THE TRIANGLE ROW LOOP -/

/-- The accumulated row slices at grand time `t`: `⋃_{1 ≤ j ≤ r} loop3Out body t j j`. -/
def triRowOut (body : List L3Instr) (t : ℕ) : ℕ → List Bool
  | 0 => []
  | r + 1 => triRowOut body t r ++ loop3Out body t (r + 1) (r + 1)

/-- **THE TRIANGLE ROW LOOP**: `repPMachine` over the engine sequenced with the row
interstitial runs `P` row rounds under the grand prefix — round `r` runs the padded engine at
row `j = r + 1` (the bound mirror and the `j`-source mirror both carry `j`; the live variable
sweeps `i = 0..j-1`) and the interstitial advances both mirrors in place and re-arms the live
variable.  One machine, self-halting, final output `⋃_{1 ≤ j ≤ P} loop3Out body t j j`. -/
theorem repP_pairRow_run (body : List L3Instr) (G g : ℕ) (hg : g ≤ G)
    (P t CB C1 C2 NV : ℕ) (htC : t ≤ C1) (hCB : P < CB) (hC2 : P < C2) (hNV : P ≤ NV)
    (out : List Bool) :
    run (repPMachine (seqMachine (pairTMachine body) interRowMachine))
      (repPRounds G (fun r =>
          pairTClock body G P CB C1 C2 NV t (r + 1) (r + 1)
              (out ++ triRowOut body t r).length + 1
            + (2 * G + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * (r + 1) + 18)) P
        + (4 * G + 4 * P + 8))
      (init (repPMachine (seqMachine (pairTMachine body) interRowMachine))
        (cntT G g ++ (cntT P 0 ++ (jT CB 1 ++ (jT C1 t ++ (jT C2 1 ++ (jT NV 0
          ++ encodeD out)))))))
      = ⟨Sum.inl (4, false), 2 * G + 2 + 2 * P + 1,
          cntT G g ++ (unaryD P ++ (jT CB (P + 1) ++ (jT C1 t ++ (jT C2 (P + 1)
            ++ (jT NV 0 ++ encodeD (out ++ triRowOut body t P))))))⟩ := by
  have h := repP_run (seqMachine (pairTMachine body) interRowMachine) G g hg P
    (fun r => jT CB (r + 1) ++ (jT C1 t ++ (jT C2 (r + 1) ++ (jT NV 0
      ++ encodeD (out ++ triRowOut body t r)))))
    (fun r => pairTClock body G P CB C1 C2 NV t (r + 1) (r + 1)
        (out ++ triRowOut body t r).length + 1
      + (2 * G + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * (r + 1) + 18))
    (fun _ => Sum.inr (28, false))
    (fun r => 2 * G + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * (r + 1) + 11)
    (fun r hr => by
      constructor
      · have heng := pairT_run body G g hg P (r + 1) (by omega) CB C1 C2 NV (r + 1) t
          (r + 1) (by omega) htC (by omega) (by omega) (out ++ triRowOut body t r)
        have hinter := interRow_run G g hg P (r + 1) (by omega) CB C1 C2 NV (r + 1) t
          (by omega) (by omega) htC (by omega) (by omega)
          (encodeD ((out ++ triRowOut body t r) ++ loop3Out body t (r + 1) (r + 1)))
        have hseq := seq_run (pairTMachine body) interRowMachine _ _ _ _ _ _ _ _ _
          heng rfl hinter rfl
        rw [List.append_assoc,
          show triRowOut body t r ++ loop3Out body t (r + 1) (r + 1)
            = triRowOut body t (r + 1) from rfl] at hseq
        exact hseq
      · rfl)
  simp only [show triRowOut body t 0 = [] from rfl, List.append_nil] at h
  exact h

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitInterRow
