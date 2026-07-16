import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitInterRow
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitRep

/-!
# Cook–Levin M2 emitter — the grand interstitial and THE TRIANGLE

Two deliverables close the triangle (TRIANGLE_PLAN.md):

* **`interGrandMachine`** — the grand interstitial, the reset-to-one design: on the
  post-row-loop layout
  `cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t ++ (jT C2 v2 ++ (jT NV w ++ E)))))` it makes
  ONE left-to-right pass — skip both counters, **reset the bound mirror to one**
  (`jT CB v1 ↦ jT CB 1`: a blind value-one head-quad `[T,T,F,T]` over the first two pairs, then
  the zeroing walk over the stale data, the old marker cleared in stride — the `oneT`
  descriptor mirrors `zeroT` with the four-cell head), cross its pad, **increment the
  `t`-mirror** (`jT C1 t ↦ jT C1 (t+1)`, the `interT` four-write), cross its pad, **reset the
  `j`-source mirror to one** likewise (`jT C2 v2 ↦ jT C2 1`), cross its pad, and halt at the
  live variable (already re-armed by the row loop).  Fixed clock
  `2G+2P2+2CB+2C1+2C2+16` — fully value-independent.

* **`rep_triangle_run`** — THE TRIANGLE, ONE MACHINE: `repMachine` over
  `seqMachine (repPMachine (seqMachine (pairTMachine body) interRowMachine)) interGrandMachine`
  runs `B` grand rounds; round `t` runs the FULL row loop (rows `j = 1..P`, row `j` emitting
  `loop3Out body t j j`) and the grand interstitial re-arms the mirrors and advances `t`; the
  final tape carries `⋃_{t<B} ⋃_{1≤j≤P} loop3Out body t j j` — the complete triangle stream.
  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitInterGrand

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinCNFEncode
open PallLean.Paper93.DeepMath.PathB.CookLevinVarIndex
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCompare
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSplice
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRange
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitNestVar
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg2 (W4_append_right2)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg3
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg3P (liftJ4 W4_append_right4)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitFamilyBodies
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRearmP (W2_append_right4)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSeq
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRep
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRepP
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitPairT
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitInterRow

/-! ## The `oneT` descriptor — the reset-to-one intermediate

`oneT v m`: the value-one head-quad written, `m` stale pairs zeroed, the rest and the old
marker still standing.  Mirrors `zeroT` with a four-cell head. -/

def oneT (v m : ℕ) : List Bool :=
  [true, true, false, true] ++ (List.replicate (2 * m) false
    ++ (List.replicate (2 * (v - 2 - m)) true ++ [false, true]))

theorem oneT_length (v m : ℕ) (hm : m ≤ v - 2) (hv : 2 ≤ v) :
    (oneT v m).length = 2 * v + 2 := by
  simp only [oneT, List.length_append, List.length_replicate, List.length_cons,
    List.length_nil]
  omega

/-- The blind value-one head-quad over the saturated variable's first two pairs. -/
theorem oneT_head (v : ℕ) (E : List Bool) (hv : 2 ≤ v) :
    writeAt (writeAt (writeAt (writeAt (jT v v ++ E) 0 true) 1 true) 2 false) 3 true
      = oneT v 0 ++ E := by
  have e : jT v v ++ E
      = true :: (true :: (true :: (true :: (List.replicate (2 * v - 4) true
          ++ ([false, true] ++ E))))) := by
    rw [jT, Nat.sub_self, show 2 * v = 4 + (2 * v - 4) from by omega, List.replicate_add]
    simp [List.append_assoc]
  have w0 : writeAt (true :: (true :: (true :: (true :: (List.replicate (2 * v - 4) true
        ++ ([false, true] ++ E)))))) 0 true
      = true :: (true :: (true :: (true :: (List.replicate (2 * v - 4) true
        ++ ([false, true] ++ E))))) := by
    rw [writeAt_of_lt true (by
      simp only [List.length_cons, List.length_append, List.length_replicate]; omega)]
    rfl
  have w1 : writeAt (true :: (true :: (true :: (true :: (List.replicate (2 * v - 4) true
        ++ ([false, true] ++ E)))))) 1 true
      = true :: (true :: (true :: (true :: (List.replicate (2 * v - 4) true
        ++ ([false, true] ++ E))))) := by
    rw [writeAt_of_lt true (by
      simp only [List.length_cons, List.length_append, List.length_replicate]; omega)]
    rfl
  have w2 : writeAt (true :: (true :: (true :: (true :: (List.replicate (2 * v - 4) true
        ++ ([false, true] ++ E)))))) 2 false
      = true :: (true :: (false :: (true :: (List.replicate (2 * v - 4) true
        ++ ([false, true] ++ E))))) := by
    rw [writeAt_of_lt false (by
      simp only [List.length_cons, List.length_append, List.length_replicate]; omega)]
    rfl
  have w3 : writeAt (true :: (true :: (false :: (true :: (List.replicate (2 * v - 4) true
        ++ ([false, true] ++ E)))))) 3 true
      = true :: (true :: (false :: (true :: (List.replicate (2 * v - 4) true
        ++ ([false, true] ++ E))))) := by
    rw [writeAt_of_lt true (by
      simp only [List.length_cons, List.length_append, List.length_replicate]; omega)]
    rfl
  rw [e, w0, w1, w2, w3, oneT, show 2 * (v - 2 - 0) = 2 * v - 4 from by omega]
  simp [List.append_assoc]

/-- Stage-`m` stale pair `m+1` (low cell), while unzeroed pairs remain. -/
theorem oneE_data_lo (v m : ℕ) (E : List Bool) (h : m + 1 ≤ v - 2) :
    (oneT v m ++ E).getD (4 + 2 * m) false = true := by
  rw [oneT]
  simp only [List.append_assoc]
  rw [show 4 + 2 * m = 4 + (2 * m + 0) from by omega,
    getD_append_left_length' _ _
      (show ([true, true, false, true] : List Bool).length = 4 from rfl),
    getD_append_left_length' _ _ List.length_replicate,
    List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem oneT_step (v m : ℕ) (E : List Bool) (h : m + 1 ≤ v - 2) :
    writeAt (writeAt (oneT v m ++ E) (4 + 2 * m) false) (4 + 2 * m + 1) false
      = oneT v (m + 1) ++ E := by
  have hv : 2 ≤ v := by omega
  have hl : (oneT v m).length = 2 * v + 2 := oneT_length v m (by omega) hv
  have e1 : writeAt (oneT v m ++ E) (4 + 2 * m) false
      = ([true, true, false, true] ++ (List.replicate (2 * m) false
          ++ (false :: (List.replicate (2 * (v - 2 - m) - 1) true ++ [false, true])))) ++ E := by
    rw [writeAt_of_lt false (by rw [List.length_append]; omega),
      List.set_append_left _ _ (by omega), oneT]
    simp only [List.append_assoc]
    rw [show 4 + 2 * m = 4 + (2 * m + 0) from by omega,
      set_append_left_length' _ _
        (show ([true, true, false, true] : List Bool).length = 4 from rfl),
      set_append_left_length' _ _ List.length_replicate,
      replicate_split_one (2 * (v - 2 - m)) (by omega)]
    simp only [List.cons_append, List.set_cons_zero]
    simp only [List.cons_append, List.append_assoc]
  rw [e1, writeAt_of_lt false (by
      simp only [List.length_append, List.length_cons, List.length_replicate]
      omega),
    List.set_append_left _ _ (by
      simp only [List.length_append, List.length_cons, List.length_replicate]
      omega)]
  rw [show 4 + 2 * m + 1 = 4 + (2 * m + 1) from by omega,
    set_append_left_length' _ _
      (show ([true, true, false, true] : List Bool).length = 4 from rfl),
    set_append_left_length' _ _ List.length_replicate, List.set_cons_succ,
    replicate_split_one (2 * (v - 2 - m) - 1) (by omega)]
  simp only [List.cons_append, List.set_cons_zero]
  rw [cons_cons_append false false, ← List.append_assoc (List.replicate (2 * m) false),
    show ([false, false] : List Bool) = List.replicate 2 false from rfl,
    ← List.replicate_add, show 2 * m + 2 = 2 * (m + 1) from by ring, oneT,
    show 2 * (v - 2 - (m + 1)) = 2 * (v - 2 - m) - 1 - 1 from by omega]
  simp

/-- Stage-`(v-2)` old-marker pair (low cell). -/
theorem oneE_m_lo (v : ℕ) (E : List Bool) (hv : 2 ≤ v) :
    (oneT v (v - 2) ++ E).getD (2 * v) false = false := by
  rw [oneT]
  simp only [List.append_assoc]
  rw [show 2 * v = 4 + (2 * (v - 2) + (2 * (v - 2 - (v - 2)) + 0)) from by omega,
    getD_append_left_length' _ _
      (show ([true, true, false, true] : List Bool).length = 4 from rfl),
    getD_append_left_length' _ _ List.length_replicate,
    getD_append_left_length' _ _ List.length_replicate]
  rfl

/-- The last walk step: zero the old marker — the variable is exactly `jT v 1`. -/
theorem oneT_last (v : ℕ) (E : List Bool) (hv : 2 ≤ v) :
    writeAt (writeAt (oneT v (v - 2) ++ E) (2 * v) false) (2 * v + 1) false
      = jT v 1 ++ E := by
  have e0 : oneT v (v - 2)
      = [true, true, false, true] ++ (List.replicate (2 * (v - 2)) false
          ++ [false, true]) := by
    rw [oneT, show v - 2 - (v - 2) = 0 from by omega]
    simp
  have hl : (oneT v (v - 2)).length = 2 * v + 2 := oneT_length v (v - 2) (le_refl _) hv
  rw [e0] at hl
  have e1 : writeAt (([true, true, false, true] ++ (List.replicate (2 * (v - 2)) false
        ++ [false, true])) ++ E) (2 * v) false
      = ([true, true, false, true] ++ (List.replicate (2 * (v - 2)) false
          ++ [false, true])) ++ E := by
    rw [writeAt_of_lt false (by rw [List.length_append]; omega),
      List.set_append_left _ _ (by omega)]
    simp only [List.append_assoc]
    rw [show 2 * v = 4 + (2 * (v - 2) + 0) from by omega,
      set_append_left_length' _ _
        (show ([true, true, false, true] : List Bool).length = 4 from rfl),
      set_append_left_length' _ _ List.length_replicate]
    simp [List.append_assoc]
  rw [e0, e1, writeAt_of_lt false (by rw [List.length_append]; omega),
    List.set_append_left _ _ (by omega)]
  rw [show 2 * v + 1 = 4 + (2 * (v - 2) + 1) from by omega,
    set_append_left_length' _ _
      (show ([true, true, false, true] : List Bool).length = 4 from rfl),
    set_append_left_length' _ _ List.length_replicate, List.set_cons_succ,
    List.set_cons_zero]
  rw [jT, show (2 : ℕ) * 1 = 2 from rfl,
    show ([true, true, false, true] : List Bool)
      = List.replicate 2 true ++ [false, true] from rfl,
    cons_cons_append false false,
    ← List.append_assoc (List.replicate (2 * (v - 2)) false),
    show ([false, false] : List Bool) = List.replicate 2 false from rfl,
    ← List.replicate_add, show 2 * (v - 2) + 2 = 2 * (v - 1) from by omega]
  simp

/-- Re-attaching the padding at value one. -/
theorem jT_join_pad1 (C v : ℕ) (h1 : 1 ≤ v) (hv : v ≤ C) (E : List Bool) :
    jT v 1 ++ (List.replicate (2 * (C - v)) false ++ E) = jT C 1 ++ E := by
  simp only [jT, List.cons_append, List.append_assoc]
  rw [← List.append_assoc (List.replicate (2 * (v - 1)) false), ← List.replicate_add,
    show 2 * (v - 1) + 2 * (C - v) = 2 * (C - 1) from by omega]

/-! ## The machine

`Fin 30 × Bool`: `0/1` skip the grand counter, `2/3` skip the row counter, `4,5,6,7` the
bound's value-one head-quad, `8/9/10` its zeroing walk (the last step flows into the pad),
`11/12` cross the bound's pad, `13/14` walk the `t`-mirror, `15,16,17` its four-write
increment, `18/19` cross its pad, `20,21,22,23` the `j`-source's head-quad, `24/25/26` its
zeroing walk, `27/28` cross its pad, `29` halt at the live variable.  Every pad exit resets
the carried bit. -/

def interGrandMachine : Machine where
  State := Fin 30 × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, false)
  halt := fun s => decide (s.1 = 29)
  δ := fun s b =>
    if s.1 = 0 then ((1, b), none, 1)
    else if s.1 = 1 then
      (if s.2 then ((0, s.2), none, 1)
       else (if b then ((2, s.2), none, 1) else ((29, s.2), none, 2)))
    else if s.1 = 2 then ((3, b), none, 1)
    else if s.1 = 3 then
      (if s.2 then ((2, s.2), none, 1)
       else (if b then ((4, s.2), none, 1) else ((29, s.2), none, 2)))
    else if s.1 = 4 then ((5, s.2), some true, 1)
    else if s.1 = 5 then ((6, s.2), some true, 1)
    else if s.1 = 6 then ((7, s.2), some false, 1)
    else if s.1 = 7 then ((8, s.2), some true, 1)
    else if s.1 = 8 then
      (if b then ((9, b), some false, 1) else ((10, b), some false, 1))
    else if s.1 = 9 then ((8, s.2), some false, 1)
    else if s.1 = 10 then ((11, s.2), some false, 1)
    else if s.1 = 11 then ((12, b), none, 1)
    else if s.1 = 12 then
      (if s.2 then ((13, false), none, 0)
       else (if b then ((13, false), none, 0) else ((11, s.2), none, 1)))
    else if s.1 = 13 then
      (if b then ((14, b), none, 1) else ((15, s.2), some true, 1))
    else if s.1 = 14 then ((13, s.2), none, 1)
    else if s.1 = 15 then ((16, s.2), some true, 1)
    else if s.1 = 16 then ((17, s.2), some false, 1)
    else if s.1 = 17 then ((18, s.2), some true, 1)
    else if s.1 = 18 then ((19, b), none, 1)
    else if s.1 = 19 then
      (if s.2 then ((20, false), none, 0)
       else (if b then ((20, false), none, 0) else ((18, s.2), none, 1)))
    else if s.1 = 20 then ((21, s.2), some true, 1)
    else if s.1 = 21 then ((22, s.2), some true, 1)
    else if s.1 = 22 then ((23, s.2), some false, 1)
    else if s.1 = 23 then ((24, s.2), some true, 1)
    else if s.1 = 24 then
      (if b then ((25, b), some false, 1) else ((26, b), some false, 1))
    else if s.1 = 25 then ((24, s.2), some false, 1)
    else if s.1 = 26 then ((27, s.2), some false, 1)
    else if s.1 = 27 then ((28, b), none, 1)
    else if s.1 = 28 then
      (if s.2 then ((29, false), none, 0)
       else (if b then ((29, false), none, 0) else ((27, s.2), none, 1)))
    else ((s.1, s.2), none, 2)
  accept := fun _ => false

theorem init_ig (t : List Bool) : init interGrandMachine t = ⟨(0, false), 0, t⟩ := rfl

/-! ## The step layer -/

section StepsIG
variable {s : Bool} {p : ℕ} {T : List Bool}

theorem ig_skipW (h1 : T.getD p false = true) :
    run interGrandMachine 2 ⟨(0, s), p, T⟩ = ⟨(0, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step interGrandMachine ⟨(0, s), p, T⟩ = ⟨(1, T.getD p false), p + 1, T⟩ := by
    simp only [step, interGrandMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, interGrandMachine, moveHead]; rfl

theorem ig_crossW (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run interGrandMachine 2 ⟨(0, s), p, T⟩ = ⟨(2, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step interGrandMachine ⟨(0, s), p, T⟩ = ⟨(1, T.getD p false), p + 1, T⟩ := by
    simp only [step, interGrandMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, interGrandMachine, moveHead, h2]

theorem ig_skipR (h1 : T.getD p false = true) :
    run interGrandMachine 2 ⟨(2, s), p, T⟩ = ⟨(2, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step interGrandMachine ⟨(2, s), p, T⟩ = ⟨(3, T.getD p false), p + 1, T⟩ := by
    simp only [step, interGrandMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, interGrandMachine, moveHead]; rfl

theorem ig_crossR (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run interGrandMachine 2 ⟨(2, s), p, T⟩ = ⟨(4, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step interGrandMachine ⟨(2, s), p, T⟩ = ⟨(3, T.getD p false), p + 1, T⟩ := by
    simp only [step, interGrandMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, interGrandMachine, moveHead, h2]

/-- The bound's blind value-one head-quad. -/
theorem ig_quadB :
    run interGrandMachine 4 ⟨(4, s), p, T⟩
      = ⟨(8, s), p + 4, writeAt (writeAt (writeAt (writeAt T p true)
          (p + 1) true) (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e0 : step interGrandMachine ⟨(4, s), p, T⟩ = ⟨(5, s), p + 1, writeAt T p true⟩ := by
    simp only [step, interGrandMachine, moveHead]; rfl
  have e1 : ∀ p' T', step interGrandMachine ⟨(5, s), p', T'⟩
      = ⟨(6, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, interGrandMachine, moveHead]; rfl
  have e2 : ∀ p' T', step interGrandMachine ⟨(6, s), p', T'⟩
      = ⟨(7, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, interGrandMachine, moveHead]; rfl
  have e3 : ∀ p' T', step interGrandMachine ⟨(7, s), p', T'⟩
      = ⟨(8, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, interGrandMachine, moveHead]; rfl
  rw [e0, e1, e2, e3]

theorem ig_zeroB_step (h : T.getD p false = true) :
    run interGrandMachine 2 ⟨(8, s), p, T⟩
      = ⟨(8, true), p + 2, writeAt (writeAt T p false) (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e6 : step interGrandMachine ⟨(8, s), p, T⟩
      = ⟨(9, true), p + 1, writeAt T p false⟩ := by
    have h' := h
    rw [List.getD_eq_getElem?_getD] at h'
    simp [step, interGrandMachine, moveHead, h']
  rw [e6]
  simp only [step, interGrandMachine, moveHead]; rfl

/-- The bound's last zeroing step flows into the pad crossing. -/
theorem ig_zeroB_last (h : T.getD p false = false) :
    run interGrandMachine 2 ⟨(8, s), p, T⟩
      = ⟨(11, false), p + 2, writeAt (writeAt T p false) (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e6 : step interGrandMachine ⟨(8, s), p, T⟩
      = ⟨(10, false), p + 1, writeAt T p false⟩ := by
    have h' := h
    rw [List.getD_eq_getElem?_getD] at h'
    simp [step, interGrandMachine, moveHead, h']
  rw [e6]
  simp only [step, interGrandMachine, moveHead]; rfl

theorem ig_padB (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = false) :
    run interGrandMachine 2 ⟨(11, s), p, T⟩ = ⟨(11, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step interGrandMachine ⟨(11, s), p, T⟩ = ⟨(12, T.getD p false), p + 1, T⟩ := by
    simp only [step, interGrandMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, interGrandMachine, moveHead, h2]

theorem ig_padB_boundT (h1 : T.getD p false = true) :
    run interGrandMachine 2 ⟨(11, s), p, T⟩ = ⟨(13, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step interGrandMachine ⟨(11, s), p, T⟩ = ⟨(12, T.getD p false), p + 1, T⟩ := by
    simp only [step, interGrandMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, interGrandMachine, moveHead]; rfl

theorem ig_padB_boundM (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run interGrandMachine 2 ⟨(11, s), p, T⟩ = ⟨(13, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step interGrandMachine ⟨(11, s), p, T⟩ = ⟨(12, T.getD p false), p + 1, T⟩ := by
    simp only [step, interGrandMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, interGrandMachine, moveHead, h2]

theorem ig_padB_bound
    (h : T.getD p false = true ∨ (T.getD p false = false ∧ T.getD (p + 1) false = true)) :
    run interGrandMachine 2 ⟨(11, s), p, T⟩ = ⟨(13, false), p, T⟩ := by
  rcases h with h1 | ⟨h1, h2⟩
  · exact ig_padB_boundT h1
  · exact ig_padB_boundM h1 h2

theorem ig_walkT (h1 : T.getD p false = true) :
    run interGrandMachine 2 ⟨(13, s), p, T⟩ = ⟨(13, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step interGrandMachine ⟨(13, s), p, T⟩ = ⟨(14, true), p + 1, T⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, interGrandMachine, moveHead, h1']
  rw [e0]
  simp only [step, interGrandMachine, moveHead]; rfl

/-- The four-write increment at the `t`-mirror's marker. -/
theorem ig_four_incrT (h1 : T.getD p false = false) :
    run interGrandMachine 4 ⟨(13, s), p, T⟩
      = ⟨(18, s), p + 4, writeAt (writeAt (writeAt (writeAt T p true)
          (p + 1) true) (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e0 : step interGrandMachine ⟨(13, s), p, T⟩
      = ⟨(15, s), p + 1, writeAt T p true⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, interGrandMachine, moveHead, h1']
  have e1 : ∀ p' T', step interGrandMachine ⟨(15, s), p', T'⟩
      = ⟨(16, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, interGrandMachine, moveHead]; rfl
  have e2 : ∀ p' T', step interGrandMachine ⟨(16, s), p', T'⟩
      = ⟨(17, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, interGrandMachine, moveHead]; rfl
  have e3 : ∀ p' T', step interGrandMachine ⟨(17, s), p', T'⟩
      = ⟨(18, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, interGrandMachine, moveHead]; rfl
  rw [e0, e1, e2, e3]

theorem ig_padT (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = false) :
    run interGrandMachine 2 ⟨(18, s), p, T⟩ = ⟨(18, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step interGrandMachine ⟨(18, s), p, T⟩ = ⟨(19, T.getD p false), p + 1, T⟩ := by
    simp only [step, interGrandMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, interGrandMachine, moveHead, h2]

theorem ig_padT_boundT (h1 : T.getD p false = true) :
    run interGrandMachine 2 ⟨(18, s), p, T⟩ = ⟨(20, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step interGrandMachine ⟨(18, s), p, T⟩ = ⟨(19, T.getD p false), p + 1, T⟩ := by
    simp only [step, interGrandMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, interGrandMachine, moveHead]; rfl

/-- The `j`-source's blind value-one head-quad. -/
theorem ig_quadJ :
    run interGrandMachine 4 ⟨(20, s), p, T⟩
      = ⟨(24, s), p + 4, writeAt (writeAt (writeAt (writeAt T p true)
          (p + 1) true) (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e0 : step interGrandMachine ⟨(20, s), p, T⟩
      = ⟨(21, s), p + 1, writeAt T p true⟩ := by
    simp only [step, interGrandMachine, moveHead]; rfl
  have e1 : ∀ p' T', step interGrandMachine ⟨(21, s), p', T'⟩
      = ⟨(22, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, interGrandMachine, moveHead]; rfl
  have e2 : ∀ p' T', step interGrandMachine ⟨(22, s), p', T'⟩
      = ⟨(23, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, interGrandMachine, moveHead]; rfl
  have e3 : ∀ p' T', step interGrandMachine ⟨(23, s), p', T'⟩
      = ⟨(24, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, interGrandMachine, moveHead]; rfl
  rw [e0, e1, e2, e3]

theorem ig_zeroJ_step (h : T.getD p false = true) :
    run interGrandMachine 2 ⟨(24, s), p, T⟩
      = ⟨(24, true), p + 2, writeAt (writeAt T p false) (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e6 : step interGrandMachine ⟨(24, s), p, T⟩
      = ⟨(25, true), p + 1, writeAt T p false⟩ := by
    have h' := h
    rw [List.getD_eq_getElem?_getD] at h'
    simp [step, interGrandMachine, moveHead, h']
  rw [e6]
  simp only [step, interGrandMachine, moveHead]; rfl

theorem ig_zeroJ_last (h : T.getD p false = false) :
    run interGrandMachine 2 ⟨(24, s), p, T⟩
      = ⟨(27, false), p + 2, writeAt (writeAt T p false) (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e6 : step interGrandMachine ⟨(24, s), p, T⟩
      = ⟨(26, false), p + 1, writeAt T p false⟩ := by
    have h' := h
    rw [List.getD_eq_getElem?_getD] at h'
    simp [step, interGrandMachine, moveHead, h']
  rw [e6]
  simp only [step, interGrandMachine, moveHead]; rfl

theorem ig_padJ (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = false) :
    run interGrandMachine 2 ⟨(27, s), p, T⟩ = ⟨(27, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step interGrandMachine ⟨(27, s), p, T⟩ = ⟨(28, T.getD p false), p + 1, T⟩ := by
    simp only [step, interGrandMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, interGrandMachine, moveHead, h2]

theorem ig_padJ_boundT (h1 : T.getD p false = true) :
    run interGrandMachine 2 ⟨(27, s), p, T⟩ = ⟨(29, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step interGrandMachine ⟨(27, s), p, T⟩ = ⟨(28, T.getD p false), p + 1, T⟩ := by
    simp only [step, interGrandMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, interGrandMachine, moveHead]; rfl

theorem ig_padJ_boundM (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run interGrandMachine 2 ⟨(27, s), p, T⟩ = ⟨(29, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step interGrandMachine ⟨(27, s), p, T⟩ = ⟨(28, T.getD p false), p + 1, T⟩ := by
    simp only [step, interGrandMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, interGrandMachine, moveHead, h2]

theorem ig_padJ_bound
    (h : T.getD p false = true ∨ (T.getD p false = false ∧ T.getD (p + 1) false = true)) :
    run interGrandMachine 2 ⟨(27, s), p, T⟩ = ⟨(29, false), p, T⟩ := by
  rcases h with h1 | ⟨h1, h2⟩
  · exact ig_padJ_boundT h1
  · exact ig_padJ_boundM h1 h2

end StepsIG

/-! ## Scan invariants -/

theorem ig_skipWs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run interGrandMachine (2 * k) ⟨(0, s), q, T⟩
      = ⟨(0, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), ig_skipW (h k (by omega))]
    rfl

theorem ig_skipRs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run interGrandMachine (2 * k) ⟨(2, s), q, T⟩
      = ⟨(2, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), ig_skipR (h k (by omega))]
    rfl

theorem ig_padBs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = false
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run interGrandMachine (2 * k) ⟨(11, s), q, T⟩
      = ⟨(11, if k = 0 then s else false), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), ig_padB hk.1 hk.2]
    rfl

theorem ig_walkTs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run interGrandMachine (2 * k) ⟨(13, s), q, T⟩
      = ⟨(13, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), ig_walkT (h k (by omega))]
    rfl

theorem ig_padTs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = false
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run interGrandMachine (2 * k) ⟨(18, s), q, T⟩
      = ⟨(18, if k = 0 then s else false), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), ig_padT hk.1 hk.2]
    rfl

theorem ig_padJs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = false
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run interGrandMachine (2 * k) ⟨(27, s), q, T⟩
      = ⟨(27, if k = 0 then s else false), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), ig_padJ hk.1 hk.2]
    rfl

/-- The bound's zeroing walk (evolving `oneT`, two prefixes). -/
theorem ig_zerosB (W Q : List Bool) (G P2 v : ℕ) (E : List Bool)
    (hW : W.length = 2 * G + 2) (hQ : Q.length = 2 * P2 + 2) (hv : 2 ≤ v) (s : Bool)
    (m : ℕ) (hm : m ≤ v - 2) :
    run interGrandMachine (2 * m)
      ⟨(8, s), 2 * G + 2 + 2 * P2 + 2 + 4, W ++ (Q ++ (oneT v 0 ++ E))⟩
      = ⟨(8, if m = 0 then s else true), 2 * G + 2 + 2 * P2 + 2 + 4 + 2 * m,
          W ++ (Q ++ (oneT v m ++ E))⟩ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hlo : (W ++ (Q ++ (oneT v m ++ E))).getD
        (2 * G + 2 + 2 * P2 + 2 + 4 + 2 * m) false = true := by
      rw [show 2 * G + 2 + 2 * P2 + 2 + 4 + 2 * m
          = 2 * G + 2 + (2 * P2 + 2 + (4 + 2 * m)) from by omega]
      exact liftJ2 _ _ _ hW hQ (oneE_data_lo v m E (by omega))
    have hw : writeAt (writeAt (W ++ (Q ++ (oneT v m ++ E)))
        (2 * G + 2 + 2 * P2 + 2 + 4 + 2 * m) false)
        (2 * G + 2 + 2 * P2 + 2 + 4 + 2 * m + 1) false
        = W ++ (Q ++ (oneT v (m + 1) ++ E)) := by
      rw [show 2 * G + 2 + 2 * P2 + 2 + 4 + 2 * m
          = 2 * G + 2 + (2 * P2 + 2 + (4 + 2 * m)) from by omega,
        W2_append_right2 W Q _ (2 * G + 2) (2 * P2 + 2) (4 + 2 * m) false false hW hQ
          (by rw [List.length_append, oneT_length v m (by omega) hv]; omega),
        oneT_step v m E (by omega)]
    rw [show 2 * (m + 1) = 2 * m + 2 from by ring, run_add, ih (by omega),
      ig_zeroB_step hlo, hw]
    rfl

/-- The `j`-source's zeroing walk (evolving `oneT`, four prefixes). -/
theorem ig_zerosJ (W Q R S : List Bool) (G P2 CB C1 v : ℕ) (E : List Bool)
    (hW : W.length = 2 * G + 2) (hQ : Q.length = 2 * P2 + 2) (hR : R.length = 2 * CB + 2)
    (hS : S.length = 2 * C1 + 2) (hv : 2 ≤ v) (s : Bool) (m : ℕ) (hm : m ≤ v - 2) :
    run interGrandMachine (2 * m)
      ⟨(24, s), 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 4,
        W ++ (Q ++ (R ++ (S ++ (oneT v 0 ++ E))))⟩
      = ⟨(24, if m = 0 then s else true),
          2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 4 + 2 * m,
          W ++ (Q ++ (R ++ (S ++ (oneT v m ++ E))))⟩ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hlo : (W ++ (Q ++ (R ++ (S ++ (oneT v m ++ E))))).getD
        (2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 4 + 2 * m) false = true := by
      rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 4 + 2 * m
          = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (4 + 2 * m))))
          from by omega]
      exact liftJ4 _ _ _ _ _ hW hQ hR hS (oneE_data_lo v m E (by omega))
    have hw : writeAt (writeAt (W ++ (Q ++ (R ++ (S ++ (oneT v m ++ E)))))
        (2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 4 + 2 * m) false)
        (2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 4 + 2 * m + 1) false
        = W ++ (Q ++ (R ++ (S ++ (oneT v (m + 1) ++ E)))) := by
      rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 4 + 2 * m
          = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (4 + 2 * m))))
          from by omega,
        W2_append_right4 W Q R S _ (2 * G + 2) (2 * P2 + 2) (2 * CB + 2) (2 * C1 + 2)
          (4 + 2 * m) false false hW hQ hR hS
          (by rw [List.length_append, oneT_length v m (by omega) hv]; omega),
        oneT_step v m E (by omega)]
    rw [show 2 * (m + 1) = 2 * m + 2 from by ring, run_add, ih (by omega),
      ig_zeroJ_step hlo, hw]
    rfl

/-! ## THE GRAND INTERSTITIAL RUN -/

/-- **The grand interstitial**: one pass resets the bound mirror and the `j`-source mirror to
one (`jT CB v1 ↦ jT CB 1`, `jT C2 v2 ↦ jT C2 1`), increments the `t`-mirror in place
(`jT C1 t ↦ jT C1 (t+1)`), and halts at the live variable — counters and live untouched,
fixed value-independent clock. -/
theorem interGrand_run (G g : ℕ) (hg : g ≤ G) (P2 r : ℕ) (hr : r ≤ P2)
    (CB C1 C2 NV v1 v2 t w : ℕ) (hv1 : 2 ≤ v1) (hv1C : v1 ≤ CB) (ht : t < C1)
    (hv2 : 2 ≤ v2) (hv2C : v2 ≤ C2) (_hw : w ≤ NV) (E : List Bool) :
    run interGrandMachine (2 * G + 2 * P2 + 2 * CB + 2 * C1 + 2 * C2 + 16)
      (init interGrandMachine (cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t
        ++ (jT C2 v2 ++ (jT NV w ++ E)))))))
      = ⟨(29, false), 2 * G + 2 * P2 + 2 * CB + 2 * C1 + 2 * C2 + 10,
          cntT G g ++ (cntT P2 r ++ (jT CB 1 ++ (jT C1 (t + 1)
            ++ (jT C2 1 ++ (jT NV w ++ E)))))⟩ := by
  have hW : (cntT G g).length = 2 * G + 2 := cntT_length G g hg
  have hQ : (cntT P2 r).length = 2 * P2 + 2 := cntT_length P2 r hr
  have hR : (jT CB 1).length = 2 * CB + 2 := jT_length CB 1 (by omega)
  have hS : (jT C1 (t + 1)).length = 2 * C1 + 2 := jT_length C1 (t + 1) (by omega)
  have hU : (jT C2 1).length = 2 * C2 + 2 := jT_length C2 1 (by omega)
  have f0 := ig_skipWs (cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t
      ++ (jT C2 v2 ++ (jT NV w ++ E)))))) 0 G false
    (fun i hi => by simpa using cntE_lo G g _ i hg hi)
  simp only [Nat.zero_add] at f0
  have f0' := ig_crossW (s := if G = 0 then false else true) (p := 2 * G)
    (T := cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t
      ++ (jT C2 v2 ++ (jT NV w ++ E))))))
    (cntE_cm_lo G g _ hg) (cntE_cm_hi G g _ hg)
  have f1 := ig_skipRs (cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t
      ++ (jT C2 v2 ++ (jT NV w ++ E)))))) (2 * G + 2) P2 false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * i = 2 * G + 2 + (2 * i) from rfl]
      exact liftJ _ _ hW (cntE_lo P2 r _ i hr hi))
  have f1' := ig_crossR (s := if P2 = 0 then false else true) (p := 2 * G + 2 + 2 * P2)
    (T := cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t
      ++ (jT C2 v2 ++ (jT NV w ++ E))))))
    (by rw [show 2 * G + 2 + 2 * P2 = 2 * G + 2 + (2 * P2) from rfl]
        exact liftJ _ _ hW (cntE_cm_lo P2 r _ hr))
    (by rw [show 2 * G + 2 + 2 * P2 + 1 = 2 * G + 2 + (2 * P2 + 1) from by omega]
        exact liftJ _ _ hW (cntE_cm_hi P2 r _ hr))
  have f2 := ig_quadB (s := false) (p := 2 * G + 2 + 2 * P2 + 2)
    (T := cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ (jT C1 t
      ++ (jT C2 v2 ++ (jT NV w ++ E))))))
  have hwB : writeAt (writeAt (writeAt (writeAt (cntT G g ++ (cntT P2 r ++ (jT CB v1
      ++ (jT C1 t ++ (jT C2 v2 ++ (jT NV w ++ E)))))) (2 * G + 2 + 2 * P2 + 2) true)
      (2 * G + 2 + 2 * P2 + 2 + 1) true) (2 * G + 2 + 2 * P2 + 2 + 2) false)
      (2 * G + 2 + 2 * P2 + 2 + 3) true
      = cntT G g ++ (cntT P2 r ++ (oneT v1 0 ++ (List.replicate (2 * (CB - v1)) false
          ++ (jT C1 t ++ (jT C2 v2 ++ (jT NV w ++ E)))))) := by
    rw [show 2 * G + 2 + 2 * P2 + 2 = 2 * G + 2 + (2 * P2 + 2 + 0) from by omega,
      W4_append_right2 (cntT G g) (cntT P2 r) _ (2 * G + 2) (2 * P2 + 2) 0 true true
        false true hW hQ
        (by rw [List.length_append, jT_length CB v1 hv1C]; omega)]
    simp only [Nat.zero_add]
    rw [jT_split_pad CB v1, oneT_head v1 _ hv1]
  rw [hwB] at f2
  have f3 := ig_zerosB (cntT G g) (cntT P2 r) G P2 v1
    (List.replicate (2 * (CB - v1)) false ++ (jT C1 t ++ (jT C2 v2 ++ (jT NV w ++ E))))
    hW hQ hv1 false (v1 - 2) (le_refl _)
  have hlo4 : (cntT G g ++ (cntT P2 r ++ (oneT v1 (v1 - 2)
      ++ (List.replicate (2 * (CB - v1)) false ++ (jT C1 t ++ (jT C2 v2
        ++ (jT NV w ++ E))))))).getD
      (2 * G + 2 + 2 * P2 + 2 + 4 + 2 * (v1 - 2)) false = false := by
    rw [show 2 * G + 2 + 2 * P2 + 2 + 4 + 2 * (v1 - 2)
        = 2 * G + 2 + (2 * P2 + 2 + 2 * v1) from by omega]
    exact liftJ2 _ _ _ hW hQ (oneE_m_lo v1 _ hv1)
  have f4 := ig_zeroB_last (s := if v1 - 2 = 0 then false else true)
    (p := 2 * G + 2 + 2 * P2 + 2 + 4 + 2 * (v1 - 2))
    (T := cntT G g ++ (cntT P2 r ++ (oneT v1 (v1 - 2)
      ++ (List.replicate (2 * (CB - v1)) false ++ (jT C1 t ++ (jT C2 v2
        ++ (jT NV w ++ E))))))) hlo4
  have hw4 : writeAt (writeAt (cntT G g ++ (cntT P2 r ++ (oneT v1 (v1 - 2)
      ++ (List.replicate (2 * (CB - v1)) false ++ (jT C1 t ++ (jT C2 v2
        ++ (jT NV w ++ E)))))))
      (2 * G + 2 + 2 * P2 + 2 + 4 + 2 * (v1 - 2)) false)
      (2 * G + 2 + 2 * P2 + 2 + 4 + 2 * (v1 - 2) + 1) false
      = cntT G g ++ (cntT P2 r ++ (jT CB 1 ++ (jT C1 t ++ (jT C2 v2
          ++ (jT NV w ++ E))))) := by
    rw [show 2 * G + 2 + 2 * P2 + 2 + 4 + 2 * (v1 - 2)
        = 2 * G + 2 + (2 * P2 + 2 + 2 * v1) from by omega,
      W2_append_right2 (cntT G g) (cntT P2 r) _ (2 * G + 2) (2 * P2 + 2) (2 * v1) false
        false hW hQ
        (by rw [List.length_append, oneT_length v1 (v1 - 2) (le_refl _) hv1]; omega),
      oneT_last v1 _ hv1, jT_join_pad1 CB v1 (by omega) hv1C]
  rw [hw4, show 2 * G + 2 + 2 * P2 + 2 + 4 + 2 * (v1 - 2) + 2
      = 2 * G + 2 + 2 * P2 + 2 + 2 * v1 + 2 from by omega] at f4
  have f5 := ig_padBs (cntT G g ++ (cntT P2 r ++ (jT CB 1 ++ (jT C1 t
      ++ (jT C2 v2 ++ (jT NV w ++ E)))))) (2 * G + 2 + 2 * P2 + 2 + 2 * v1 + 2)
    (CB - v1) false
    (fun i hi => ⟨by
      rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * v1 + 2 + 2 * i
          = 2 * G + 2 + (2 * P2 + 2 + (2 * v1 + 2 + 2 * i)) from by omega,
        ← jsT_zero CB 1]
      exact liftJ2 _ _ _ hW hQ (jsE_pad CB 1 0 _ (2 * v1 + 2 + 2 * i)
        (by omega) (by omega) (by omega) (by omega)), by
      rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * v1 + 2 + 2 * i + 1
          = 2 * G + 2 + (2 * P2 + 2 + (2 * v1 + 2 + 2 * i + 1)) from by omega,
        ← jsT_zero CB 1]
      exact liftJ2 _ _ _ hW hQ (jsE_pad CB 1 0 _ (2 * v1 + 2 + 2 * i + 1)
        (by omega) (by omega) (by omega) (by omega))⟩)
  rw [ite_self, show 2 * G + 2 + 2 * P2 + 2 + 2 * v1 + 2 + 2 * (CB - v1)
      = 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 from by omega] at f5
  have f6 := ig_padB_bound (s := false) (p := 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2)
    (T := cntT G g ++ (cntT P2 r ++ (jT CB 1 ++ (jT C1 t ++ (jT C2 v2
      ++ (jT NV w ++ E))))))
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
  have f7 := ig_walkTs (cntT G g ++ (cntT P2 r ++ (jT CB 1 ++ (jT C1 t
      ++ (jT C2 v2 ++ (jT NV w ++ E)))))) (2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2) t false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * i
          = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + 2 * i)) from by omega,
        ← jsT_zero C1 t]
      exact liftJ3 _ _ _ _ hW hQ hR
        (jsE_data C1 t 0 _ (2 * i) (by omega) (by omega) (by omega)))
  have f8 := ig_four_incrT (s := if t = 0 then false else true)
    (p := 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * t)
    (T := cntT G g ++ (cntT P2 r ++ (jT CB 1 ++ (jT C1 t ++ (jT C2 v2
      ++ (jT NV w ++ E))))))
    (by rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * t
          = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + 2 * t)) from by omega,
        ← jsT_zero C1 t]
        exact liftJ3 _ _ _ _ hW hQ hR (jsE_m_lo C1 t 0 _ (by omega)))
  rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * t
      = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + 2 * t)) from by omega,
    W4_append_right3 (cntT G g) (cntT P2 r) (jT CB 1)
      (jT C1 t ++ (jT C2 v2 ++ (jT NV w ++ E))) (2 * G + 2) (2 * P2 + 2) (2 * CB + 2)
      (2 * t) true true false true hW hQ hR
      (by rw [List.length_append, jT_length C1 t (by omega)]; omega),
    jT_incr C1 t _ ht] at f8
  have f9 := ig_padTs (cntT G g ++ (cntT P2 r ++ (jT CB 1 ++ (jT C1 (t + 1)
      ++ (jT C2 v2 ++ (jT NV w ++ E))))))
    (2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * t + 4) (C1 - t - 1)
    (if t = 0 then false else true)
    (fun i hi => ⟨by
      rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * t + 4 + 2 * i
          = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * (t + 1) + 2 + 2 * i)))
          from by omega, ← jsT_zero C1 (t + 1)]
      exact liftJ3 _ _ _ _ hW hQ hR (jsE_pad C1 (t + 1) 0 _ (2 * (t + 1) + 2 + 2 * i)
        (by omega) (by omega) (by omega) (by omega)), by
      rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * t + 4 + 2 * i + 1
          = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * (t + 1) + 2 + 2 * i + 1)))
          from by omega, ← jsT_zero C1 (t + 1)]
      exact liftJ3 _ _ _ _ hW hQ hR (jsE_pad C1 (t + 1) 0 _ (2 * (t + 1) + 2 + 2 * i + 1)
        (by omega) (by omega) (by omega) (by omega))⟩)
  rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * t + 4 + 2 * (C1 - t - 1)
      = 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 from by omega] at f9
  have f10 := ig_padT_boundT
    (s := if C1 - t - 1 = 0 then (if t = 0 then false else true) else false)
    (p := 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2)
    (T := cntT G g ++ (cntT P2 r ++ (jT CB 1 ++ (jT C1 (t + 1) ++ (jT C2 v2
      ++ (jT NV w ++ E))))))
    (by rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2
          = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + 0))) from by omega,
        ← jsT_zero C2 v2]
        exact liftJ4 _ _ _ _ _ hW hQ hR hS
          (jsE_data C2 v2 0 _ 0 (by omega) (by omega) (by omega)))
  have f11 := ig_quadJ (s := false)
    (p := 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2)
    (T := cntT G g ++ (cntT P2 r ++ (jT CB 1 ++ (jT C1 (t + 1) ++ (jT C2 v2
      ++ (jT NV w ++ E))))))
  have hwJ : writeAt (writeAt (writeAt (writeAt (cntT G g ++ (cntT P2 r ++ (jT CB 1
      ++ (jT C1 (t + 1) ++ (jT C2 v2 ++ (jT NV w ++ E))))))
      (2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2) true)
      (2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 1) true)
      (2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2) false)
      (2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 3) true
      = cntT G g ++ (cntT P2 r ++ (jT CB 1 ++ (jT C1 (t + 1) ++ (oneT v2 0
          ++ (List.replicate (2 * (C2 - v2)) false ++ (jT NV w ++ E)))))) := by
    rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2
        = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + 0))) from by omega,
      W4_append_right4 (cntT G g) (cntT P2 r) (jT CB 1) (jT C1 (t + 1)) _ (2 * G + 2)
        (2 * P2 + 2) (2 * CB + 2) (2 * C1 + 2) 0 true true false true hW hQ hR hS
        (by rw [List.length_append, jT_length C2 v2 hv2C]; omega)]
    simp only [Nat.zero_add]
    rw [jT_split_pad C2 v2, oneT_head v2 _ hv2]
  rw [hwJ] at f11
  have f12 := ig_zerosJ (cntT G g) (cntT P2 r) (jT CB 1) (jT C1 (t + 1)) G P2 CB C1 v2
    (List.replicate (2 * (C2 - v2)) false ++ (jT NV w ++ E)) hW hQ hR hS hv2 false
    (v2 - 2) (le_refl _)
  have hlo13 : (cntT G g ++ (cntT P2 r ++ (jT CB 1 ++ (jT C1 (t + 1) ++ (oneT v2 (v2 - 2)
      ++ (List.replicate (2 * (C2 - v2)) false ++ (jT NV w ++ E))))))).getD
      (2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 4 + 2 * (v2 - 2)) false
      = false := by
    rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 4 + 2 * (v2 - 2)
        = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + 2 * v2))) from by omega]
    exact liftJ4 _ _ _ _ _ hW hQ hR hS (oneE_m_lo v2 _ hv2)
  have f13 := ig_zeroJ_last (s := if v2 - 2 = 0 then false else true)
    (p := 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 4 + 2 * (v2 - 2))
    (T := cntT G g ++ (cntT P2 r ++ (jT CB 1 ++ (jT C1 (t + 1) ++ (oneT v2 (v2 - 2)
      ++ (List.replicate (2 * (C2 - v2)) false ++ (jT NV w ++ E))))))) hlo13
  have hw13 : writeAt (writeAt (cntT G g ++ (cntT P2 r ++ (jT CB 1 ++ (jT C1 (t + 1)
      ++ (oneT v2 (v2 - 2) ++ (List.replicate (2 * (C2 - v2)) false
        ++ (jT NV w ++ E)))))))
      (2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 4 + 2 * (v2 - 2)) false)
      (2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 4 + 2 * (v2 - 2) + 1) false
      = cntT G g ++ (cntT P2 r ++ (jT CB 1 ++ (jT C1 (t + 1) ++ (jT C2 1
          ++ (jT NV w ++ E))))) := by
    rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 4 + 2 * (v2 - 2)
        = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + 2 * v2))) from by omega,
      W2_append_right4 (cntT G g) (cntT P2 r) (jT CB 1) (jT C1 (t + 1)) _ (2 * G + 2)
        (2 * P2 + 2) (2 * CB + 2) (2 * C1 + 2) (2 * v2) false false hW hQ hR hS
        (by rw [List.length_append, oneT_length v2 (v2 - 2) (le_refl _) hv2]; omega),
      oneT_last v2 _ hv2, jT_join_pad1 C2 v2 (by omega) hv2C]
  rw [hw13, show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 4 + 2 * (v2 - 2) + 2
      = 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * v2 + 2
      from by omega] at f13
  have f14 := ig_padJs (cntT G g ++ (cntT P2 r ++ (jT CB 1 ++ (jT C1 (t + 1)
      ++ (jT C2 1 ++ (jT NV w ++ E))))))
    (2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * v2 + 2) (C2 - v2) false
    (fun i hi => ⟨by
      rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * v2 + 2 + 2 * i
          = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * C1 + 2
              + (2 * v2 + 2 + 2 * i)))) from by omega, ← jsT_zero C2 1]
      exact liftJ4 _ _ _ _ _ hW hQ hR hS (jsE_pad C2 1 0 _ (2 * v2 + 2 + 2 * i)
        (by omega) (by omega) (by omega) (by omega)), by
      rw [show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * v2 + 2 + 2 * i + 1
          = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + (2 * C1 + 2
              + (2 * v2 + 2 + 2 * i + 1)))) from by omega, ← jsT_zero C2 1]
      exact liftJ4 _ _ _ _ _ hW hQ hR hS (jsE_pad C2 1 0 _ (2 * v2 + 2 + 2 * i + 1)
        (by omega) (by omega) (by omega) (by omega))⟩)
  rw [ite_self, show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * v2 + 2
        + 2 * (C2 - v2)
      = 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2
      from by omega] at f14
  have f15 := ig_padJ_bound (s := false)
    (p := 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2)
    (T := cntT G g ++ (cntT P2 r ++ (jT CB 1 ++ (jT C1 (t + 1) ++ (jT C2 1
      ++ (jT NV w ++ E))))))
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
  rw [init_ig,
    show 2 * G + 2 * P2 + 2 * CB + 2 * C1 + 2 * C2 + 16
      = 2 * G + (2 + (2 * P2 + (2 + (4 + (2 * (v1 - 2) + (2 + (2 * (CB - v1) + (2
          + (2 * t + (4 + (2 * (C1 - t - 1) + (2 + (4 + (2 * (v2 - 2) + (2
          + (2 * (C2 - v2) + 2)))))))))))))))) from by omega,
    run_add, f0, run_add, f0', run_add, f1, run_add, f1', run_add, f2, run_add, f3,
    run_add, f4, run_add, f5, run_add, f6, run_add, f7,
    show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * t
      = 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + 2 * t)) from by omega,
    run_add, f8,
    show 2 * G + 2 + (2 * P2 + 2 + (2 * CB + 2 + 2 * t)) + 4
      = 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * t + 4 from by omega,
    run_add, f9, run_add, f10, run_add, f11, run_add, f12, run_add, f13, run_add, f14,
    f15,
    show 2 * G + 2 + 2 * P2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2
      = 2 * G + 2 * P2 + 2 * CB + 2 * C1 + 2 * C2 + 10 from by omega]

theorem interGrand_halt : interGrandMachine.halt ((29 : Fin 30), false) = true := rfl

/-! ## THE TRIANGLE, ONE MACHINE -/

/-- The accumulated triangle stream: `⋃_{t' < t} ⋃_{1 ≤ j ≤ P} loop3Out body t' j j`. -/
def triOut (body : List L3Instr) (P : ℕ) : ℕ → List Bool
  | 0 => []
  | t + 1 => triOut body P t ++ triRowOut body t P

/-- The prefixed grand-loop wrapper halts at its return phase for ANY body machine — stated
generically so the composite's instances never unfold. -/
theorem repP_halt_inl4 (M : Machine) :
    (repPMachine M).halt (Sum.inl (4, false)) = true := rfl

set_option maxHeartbeats 1600000 in
/-- **THE TRIANGLE, ONE MACHINE**: `repMachine` over the row loop sequenced with the grand
interstitial runs `B` grand rounds — round `t` runs the full row loop (rows `j = 1..P`, row
`j` emitting `loop3Out body t j j`) and the grand interstitial resets both mirrors to one and
advances the `t`-mirror.  One machine, self-halting at the explicit clock, final output
`⋃_{t<B} ⋃_{1≤j≤P} loop3Out body t j j`. -/
theorem rep_triangle_run (body : List L3Instr) (B P CB C1 C2 NV : ℕ) (hP : 0 < P)
    (hCB : P < CB) (hC2 : P < C2) (hNV : P ≤ NV) (hBC1 : B ≤ C1) (out : List Bool) :
    run (repMachine (seqMachine
        (repPMachine (seqMachine (pairTMachine body) interRowMachine))
        interGrandMachine))
      (repRounds (fun t =>
          (repPRounds B (fun r =>
              pairTClock body B P CB C1 C2 NV t (r + 1) (r + 1)
                  ((out ++ triOut body P t) ++ triRowOut body t r).length + 1
                + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * (r + 1) + 18)) P
            + (4 * B + 4 * P + 8)) + 1
          + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 16)) B + (4 * B + 4))
      (init (repMachine (seqMachine
          (repPMachine (seqMachine (pairTMachine body) interRowMachine))
          interGrandMachine))
        (cntT B 0 ++ (unaryD P ++ (jT CB 1 ++ (jT C1 0 ++ (jT C2 1 ++ (jT NV 0
          ++ encodeD out)))))))
      = ⟨Sum.inl (4, false), 2 * B + 1,
          unaryD B ++ (unaryD P ++ (jT CB 1 ++ (jT C1 B ++ (jT C2 1 ++ (jT NV 0
            ++ encodeD (out ++ triOut body P B))))))⟩ := by
  have h := rep_run (seqMachine
      (repPMachine (seqMachine (pairTMachine body) interRowMachine)) interGrandMachine) B
    (fun t => unaryD P ++ (jT CB 1 ++ (jT C1 t ++ (jT C2 1 ++ (jT NV 0
      ++ encodeD (out ++ triOut body P t))))))
    (fun t =>
      (repPRounds B (fun r =>
          pairTClock body B P CB C1 C2 NV t (r + 1) (r + 1)
              ((out ++ triOut body P t) ++ triRowOut body t r).length + 1
            + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * (r + 1) + 18)) P
        + (4 * B + 4 * P + 8)) + 1
      + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 16))
    (fun _ => Sum.inr (29, false))
    (fun _ => 2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 10)
    (fun t ht => by
      constructor
      · have heng := repP_pairRow_run body B (t + 1) (by omega) P t CB C1 C2 NV
          (by omega) hCB hC2 hNV (out ++ triOut body P t)
        rw [cntT_zero P] at heng
        have hinter := interGrand_run B (t + 1) (by omega) P 0 (by omega) CB C1 C2 NV
          (P + 1) (P + 1) t 0 (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega)
          (encodeD ((out ++ triOut body P t) ++ triRowOut body t P))
        rw [cntT_zero P] at hinter
        have hseq := seq_run
          (repPMachine (seqMachine (pairTMachine body) interRowMachine))
          interGrandMachine _ _ _ _ _ _ _ _ _ heng
          (repP_halt_inl4 (seqMachine (pairTMachine body) interRowMachine)) hinter
          interGrand_halt
        rw [List.append_assoc,
          show triOut body P t ++ triRowOut body t P = triOut body P (t + 1)
            from rfl] at hseq
        exact hseq
      · exact seq_halt_final _ interGrandMachine (29, false) interGrand_halt)
  simp only [show triOut body P 0 = [] from rfl, List.append_nil] at h
  exact h

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitInterGrand
