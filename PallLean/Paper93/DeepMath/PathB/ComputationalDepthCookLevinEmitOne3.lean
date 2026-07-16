import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitRst4

/-!
# Cook–Levin M2 emitter — E6 step 3: THE BOUND RESET-TO-ONE (`one3Machine`)

The single mode-switch interstitial of the master chain: between the `P`-bound family loops
and the `1`-bound loops, return the bound mirror from `P + 1` to `1`
(`jT CB v₁ ↦ jT CB 1`, `2 ≤ v₁`) with every other region verbatim.  The machine skips the two
counters, then runs interGrand's reset-to-one track on the THIRD region: write the new head
`[T,T,F,T]`, zero the old content pairwise (the `oneT` descriptor), close at the old fence.
`Fin 12 × Bool`; one pass, clock `2G + 2P2 + 2v₁ + 6`.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitOne3

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitAppendBlock
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCompare
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSplice
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRange
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitNestVar
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg2 (W4_append_right2)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg3
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitInterRow
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitInterGrand

/-! ## The machine -/

def one3Machine : Machine where
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
    else if s.1 = 4 then ((5, s.2), some true, 1)
    else if s.1 = 5 then ((6, s.2), some true, 1)
    else if s.1 = 6 then ((7, s.2), some false, 1)
    else if s.1 = 7 then ((8, s.2), some true, 1)
    else if s.1 = 8 then
      (if b then ((9, b), some false, 1) else ((10, b), some false, 1))
    else if s.1 = 9 then ((8, s.2), some false, 1)
    else if s.1 = 10 then ((11, s.2), some false, 2)
    else ((s.1, s.2), none, 2)
  accept := fun _ => false

theorem init_one3 (t : List Bool) : init one3Machine t = ⟨(0, false), 0, t⟩ := rfl

theorem one3_halt : one3Machine.halt ((11 : Fin 12), false) = true := rfl

/-! ## Step layer -/

section StepsOne3
variable {s : Bool} {p : ℕ} {T : List Bool}

theorem one3_skipW (h1 : T.getD p false = true) :
    run one3Machine 2 ⟨(0, s), p, T⟩ = ⟨(0, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step one3Machine ⟨(0, s), p, T⟩ = ⟨(1, T.getD p false), p + 1, T⟩ := by
    simp only [step, one3Machine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, one3Machine, moveHead]; rfl

theorem one3_crossW (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run one3Machine 2 ⟨(0, s), p, T⟩ = ⟨(2, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step one3Machine ⟨(0, s), p, T⟩ = ⟨(1, T.getD p false), p + 1, T⟩ := by
    simp only [step, one3Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, one3Machine, moveHead, h2]

theorem one3_skipR (h1 : T.getD p false = true) :
    run one3Machine 2 ⟨(2, s), p, T⟩ = ⟨(2, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step one3Machine ⟨(2, s), p, T⟩ = ⟨(3, T.getD p false), p + 1, T⟩ := by
    simp only [step, one3Machine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, one3Machine, moveHead]; rfl

theorem one3_crossR (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run one3Machine 2 ⟨(2, s), p, T⟩ = ⟨(4, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step one3Machine ⟨(2, s), p, T⟩ = ⟨(3, T.getD p false), p + 1, T⟩ := by
    simp only [step, one3Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, one3Machine, moveHead, h2]

theorem one3_head {s' : Bool} :
    run one3Machine 4 ⟨(4, s'), p, T⟩
      = ⟨(8, s'), p + 4,
          writeAt (writeAt (writeAt (writeAt T p true) (p + 1) true) (p + 2) false)
            (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e4 : step one3Machine ⟨(4, s'), p, T⟩ = ⟨(5, s'), p + 1, writeAt T p true⟩ := by
    simp only [step, one3Machine, moveHead]; rfl
  have e5 : ∀ p' T', step one3Machine ⟨(5, s'), p', T'⟩
      = ⟨(6, s'), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, one3Machine, moveHead]; rfl
  have e6 : ∀ p' T', step one3Machine ⟨(6, s'), p', T'⟩
      = ⟨(7, s'), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, one3Machine, moveHead]; rfl
  have e7 : ∀ p' T', step one3Machine ⟨(7, s'), p', T'⟩
      = ⟨(8, s'), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, one3Machine, moveHead]; rfl
  rw [e4, e5, e6, e7]

theorem one3_one_step (h : T.getD p false = true) :
    run one3Machine 2 ⟨(8, s), p, T⟩
      = ⟨(8, true), p + 2, writeAt (writeAt T p false) (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e6 : step one3Machine ⟨(8, s), p, T⟩
      = ⟨(9, true), p + 1, writeAt T p false⟩ := by
    have h' := h
    rw [List.getD_eq_getElem?_getD] at h'
    simp [step, one3Machine, moveHead, h']
  rw [e6]
  simp only [step, one3Machine, moveHead]; rfl

theorem one3_one_last (h : T.getD p false = false) :
    run one3Machine 2 ⟨(8, s), p, T⟩
      = ⟨(11, false), p + 1, writeAt (writeAt T p false) (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e6 : step one3Machine ⟨(8, s), p, T⟩
      = ⟨(10, false), p + 1, writeAt T p false⟩ := by
    have h' := h
    rw [List.getD_eq_getElem?_getD] at h'
    simp [step, one3Machine, moveHead, h']
  rw [e6]
  simp only [step, one3Machine, moveHead]; rfl

end StepsOne3

/-! ## The iterated walks -/

theorem one3_skipWs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run one3Machine (2 * k) ⟨(0, s), q, T⟩
      = ⟨(0, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), one3_skipW (h k (by omega))]
    rfl

theorem one3_skipRs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run one3Machine (2 * k) ⟨(2, s), q, T⟩
      = ⟨(2, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), one3_skipR (h k (by omega))]
    rfl

/-- The reset-to-one walk (evolving `oneT`, two prefixes). -/
theorem one3_ones (W Q : List Bool) (G P2 v : ℕ) (E : List Bool)
    (hW : W.length = 2 * G + 2) (hQ : Q.length = 2 * P2 + 2) (hv : 2 ≤ v) (s : Bool)
    (m : ℕ) (hm : m ≤ v - 2) :
    run one3Machine (2 * m)
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
          (by rw [List.length_append, oneT_length v m (by omega) (by omega)]; omega),
        oneT_step v m E (by omega)]
    rw [show 2 * (m + 1) = 2 * m + 2 from by ring, run_add, ih (by omega),
      one3_one_step hlo, hw]
    rfl

/-! ## THE BOUND RESET RUN -/

set_option maxHeartbeats 800000 in
/-- **The bound reset-to-one**: one pass, `jT CB v₁ ↦ jT CB 1` (`2 ≤ v₁`), every other region
verbatim — the single mode-switch interstitial of the E6 master chain. -/
theorem one3_run (G g : ℕ) (hg : g ≤ G) (P2 r : ℕ) (hr : r ≤ P2) (CB v1 : ℕ)
    (hv1 : 2 ≤ v1) (hv1C : v1 ≤ CB) (E : List Bool) :
    run one3Machine (2 * G + 2 * P2 + 2 * v1 + 6)
      (init one3Machine (cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ E))))
      = ⟨(11, false), 2 * G + 2 * P2 + 2 * v1 + 5,
          cntT G g ++ (cntT P2 r ++ (jT CB 1 ++ E))⟩ := by
  have hW : (cntT G g).length = 2 * G + 2 := cntT_length G g hg
  have hQ : (cntT P2 r).length = 2 * P2 + 2 := cntT_length P2 r hr
  have f0 := one3_skipWs (cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ E)))
    0 G false (fun i hi => by simpa using cntE_lo G g _ i hg hi)
  simp only [Nat.zero_add] at f0
  have f0' := one3_crossW (s := if G = 0 then false else true) (p := 2 * G)
    (T := cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ E)))
    (cntE_cm_lo G g _ hg) (cntE_cm_hi G g _ hg)
  have f1 := one3_skipRs (cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ E)))
    (2 * G + 2) P2 false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * i = 2 * G + 2 + (2 * i) from rfl]
      exact liftJ _ _ hW (cntE_lo P2 r _ i hr hi))
  have f1' := one3_crossR (s := if P2 = 0 then false else true) (p := 2 * G + 2 + 2 * P2)
    (T := cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ E)))
    (by rw [show 2 * G + 2 + 2 * P2 = 2 * G + 2 + (2 * P2) from rfl]
        exact liftJ _ _ hW (cntE_cm_lo P2 r _ hr))
    (by rw [show 2 * G + 2 + 2 * P2 + 1 = 2 * G + 2 + (2 * P2 + 1) from by omega]
        exact liftJ _ _ hW (cntE_cm_hi P2 r _ hr))
  have f8 := one3_head (s' := false) (p := 2 * G + 2 + 2 * P2 + 2)
    (T := cntT G g ++ (cntT P2 r ++ (jT CB v1 ++ E)))
  have hw8 : writeAt (writeAt (writeAt (writeAt (cntT G g ++ (cntT P2 r
      ++ (jT CB v1 ++ E))) (2 * G + 2 + 2 * P2 + 2) true)
      (2 * G + 2 + 2 * P2 + 2 + 1) true) (2 * G + 2 + 2 * P2 + 2 + 2) false)
      (2 * G + 2 + 2 * P2 + 2 + 3) true
      = cntT G g ++ (cntT P2 r ++ (oneT v1 0
          ++ (List.replicate (2 * (CB - v1)) false ++ E))) := by
    rw [show 2 * G + 2 + 2 * P2 + 2 = 2 * G + 2 + (2 * P2 + 2 + 0) from by omega,
      W4_append_right2 (cntT G g) (cntT P2 r) _ (2 * G + 2) (2 * P2 + 2) 0 true true
        false true hW hQ
        (by rw [List.length_append, jT_length CB v1 hv1C]; omega),
      jT_split_pad CB v1, oneT_head v1 _ hv1]
  rw [show 2 * G + 2 + 2 * P2 + 2 + 1 + 1 + 1 = 2 * G + 2 + 2 * P2 + 2 + 3 from by omega,
    show 2 * G + 2 + 2 * P2 + 2 + 1 + 1 = 2 * G + 2 + 2 * P2 + 2 + 2 from by omega]
    at f8
  rw [hw8] at f8
  have f9 := one3_ones (cntT G g) (cntT P2 r) G P2 v1
    (List.replicate (2 * (CB - v1)) false ++ E) hW hQ hv1 false (v1 - 2) (le_refl _)
  have hlo10 : (cntT G g ++ (cntT P2 r ++ (oneT v1 (v1 - 2)
      ++ (List.replicate (2 * (CB - v1)) false ++ E)))).getD
      (2 * G + 2 + 2 * P2 + 2 + 4 + 2 * (v1 - 2)) false = false := by
    rw [show 2 * G + 2 + 2 * P2 + 2 + 4 + 2 * (v1 - 2)
        = 2 * G + 2 + (2 * P2 + 2 + 2 * v1) from by omega]
    exact liftJ2 _ _ _ hW hQ (oneE_m_lo v1 _ hv1)
  have f10 := one3_one_last (s := if v1 - 2 = 0 then false else true)
    (p := 2 * G + 2 + 2 * P2 + 2 + 4 + 2 * (v1 - 2))
    (T := cntT G g ++ (cntT P2 r ++ (oneT v1 (v1 - 2)
      ++ (List.replicate (2 * (CB - v1)) false ++ E)))) hlo10
  have hw10 : writeAt (writeAt (cntT G g ++ (cntT P2 r ++ (oneT v1 (v1 - 2)
      ++ (List.replicate (2 * (CB - v1)) false ++ E))))
      (2 * G + 2 + 2 * P2 + 2 + 4 + 2 * (v1 - 2)) false)
      (2 * G + 2 + 2 * P2 + 2 + 4 + 2 * (v1 - 2) + 1) false
      = cntT G g ++ (cntT P2 r ++ (jT CB 1 ++ E)) := by
    rw [show 2 * G + 2 + 2 * P2 + 2 + 4 + 2 * (v1 - 2)
        = 2 * G + 2 + (2 * P2 + 2 + 2 * v1) from by omega,
      W2_append_right2 (cntT G g) (cntT P2 r) _ (2 * G + 2) (2 * P2 + 2) (2 * v1)
        false false hW hQ
        (by rw [List.length_append, oneT_length v1 (v1 - 2) (le_refl _) hv1]; omega),
      oneT_last v1 _ hv1, jT_join_pad1 CB v1 (by omega) hv1C]
  rw [hw10] at f10
  rw [init_one3,
    show 2 * G + 2 * P2 + 2 * v1 + 6
      = 2 * G + (2 + (2 * P2 + (2 + (4 + (2 * (v1 - 2) + 2))))) from by omega,
    run_add, f0, run_add, f0', run_add, f1, run_add, f1', run_add, f8, run_add, f9, f10,
    show 2 * G + 2 + 2 * P2 + 2 + 4 + 2 * (v1 - 2) + 1
      = 2 * G + 2 * P2 + 2 * v1 + 5 from by omega]

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitOne3
