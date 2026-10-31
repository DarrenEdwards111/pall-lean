import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitAddT
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitRearmT

/-!
# Cook–Levin M2 emitter — E2's multiplier: `rep` over the prefixed adder

`addTPMachine` is `addTMachine` under the grand prefix (the established `P`-lift: three appended
skip pairs, positions `+2G+2`), so it is a `rep_run`-shaped per-round body: on
`cntT G g ++ (unaryD A ++ (jT CAP v ++ E))` it adds `A` into the padded accumulator and restores
the addend.  **The multiplier is then free**: `rep_mul_run` drives it `M` times by `repMachine` —
the grand counter IS the multiplicand — computing `v + M·A` in the accumulator.  No new loop
machinery: multiplication = the grand-loop combinator over the adder, exactly as addition = the
adder's own loop over the increment.  The canonical majorant `p(n) = c·(n+1)^k` for fixed `c, k`
is `k` such multiplications chained; the remaining piece for the chain is the prefixed `rep`
(so a multiplier can itself be a per-round body) — the same lift, one level up.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitMulT

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSplice
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRange
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitNestVar
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitNestVar
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg2 (W4_append_right2)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitAddT
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRep

/-! ## The prefixed adder

`Fin 18 × Bool`: `addTMachine`'s phases `0–11` verbatim; `12/13 → 0` (the find; also the start and
the increment's reset), `14/15 → 2` (the re-skip), `16/17 → 9` (the heal). -/

def addTPMachine : Machine where
  State := Fin 18 × Bool
  fin := inferInstance
  dec := inferInstance
  start := (12, false)
  halt := fun s => decide (s.1 = 11)
  δ := fun s b =>
    if s.1 = 0 then ((1, b), none, 1)
    else if s.1 = 1 then
      (if s.2 then
        (if b then ((14, s.2), some false, 3) else ((0, s.2), none, 1))
       else (if b then ((16, s.2), none, 3) else ((11, s.2), none, 2)))
    else if s.1 = 2 then ((3, b), none, 1)
    else if s.1 = 3 then
      (if s.2 then ((2, s.2), none, 1)
       else (if b then ((4, s.2), none, 1) else ((11, s.2), none, 2)))
    else if s.1 = 4 then
      (if b then ((5, b), none, 1) else ((6, s.2), some true, 1))
    else if s.1 = 5 then ((4, s.2), none, 1)
    else if s.1 = 6 then ((7, s.2), some true, 1)
    else if s.1 = 7 then ((8, s.2), some false, 1)
    else if s.1 = 8 then ((12, false), some true, 3)
    else if s.1 = 9 then ((10, b), none, 1)
    else if s.1 = 10 then
      (if s.2 then ((9, true), some true, 1)
       else (if b then ((11, false), none, 2) else ((11, false), none, 2)))
    else if s.1 = 12 then ((13, b), none, 1)
    else if s.1 = 13 then
      (if s.2 then ((12, s.2), none, 1)
       else (if b then ((0, s.2), none, 1) else ((11, s.2), none, 2)))
    else if s.1 = 14 then ((15, b), none, 1)
    else if s.1 = 15 then
      (if s.2 then ((14, s.2), none, 1)
       else (if b then ((2, s.2), none, 1) else ((11, s.2), none, 2)))
    else if s.1 = 16 then ((17, b), none, 1)
    else if s.1 = 17 then
      (if s.2 then ((16, s.2), none, 1)
       else (if b then ((9, s.2), none, 1) else ((11, s.2), none, 2)))
    else ((s.1, s.2), none, 2)
  accept := fun _ => false

theorem init_ap (t : List Bool) : init addTPMachine t = ⟨(12, false), 0, t⟩ := rfl

/-! ## The step layer -/

section StepsAP
variable {s : Bool} {p : ℕ} {T : List Bool}

theorem ap_skipB (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run addTPMachine 2 ⟨(0, s), p, T⟩ = ⟨(0, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step addTPMachine ⟨(0, s), p, T⟩ = ⟨(1, T.getD p false), p + 1, T⟩ := by
    simp only [step, addTPMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, addTPMachine, moveHead, h2]

theorem ap_markB (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run addTPMachine 2 ⟨(0, s), p, T⟩ = ⟨(14, true), 0, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step addTPMachine ⟨(0, s), p, T⟩ = ⟨(1, T.getD p false), p + 1, T⟩ := by
    simp only [step, addTPMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, addTPMachine, moveHead, h2]

theorem ap_doneB (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run addTPMachine 2 ⟨(0, s), p, T⟩ = ⟨(16, false), 0, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step addTPMachine ⟨(0, s), p, T⟩ = ⟨(1, T.getD p false), p + 1, T⟩ := by
    simp only [step, addTPMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, addTPMachine, moveHead, h2]

theorem ap_skipR1 (h1 : T.getD p false = true) :
    run addTPMachine 2 ⟨(2, s), p, T⟩ = ⟨(2, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step addTPMachine ⟨(2, s), p, T⟩ = ⟨(3, T.getD p false), p + 1, T⟩ := by
    simp only [step, addTPMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, addTPMachine, moveHead]; rfl

theorem ap_crossR1 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run addTPMachine 2 ⟨(2, s), p, T⟩ = ⟨(4, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step addTPMachine ⟨(2, s), p, T⟩ = ⟨(3, T.getD p false), p + 1, T⟩ := by
    simp only [step, addTPMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, addTPMachine, moveHead, h2]

theorem ap_walk (h1 : T.getD p false = true) :
    run addTPMachine 2 ⟨(4, s), p, T⟩ = ⟨(4, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step addTPMachine ⟨(4, s), p, T⟩ = ⟨(5, true), p + 1, T⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, addTPMachine, moveHead, h1']
  rw [e0]
  simp only [step, addTPMachine, moveHead]; rfl

theorem ap_four_incr (h1 : T.getD p false = false) :
    run addTPMachine 4 ⟨(4, s), p, T⟩
      = ⟨(12, false), 0, writeAt (writeAt (writeAt (writeAt T p true)
          (p + 1) true) (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e0 : step addTPMachine ⟨(4, s), p, T⟩ = ⟨(6, s), p + 1, writeAt T p true⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, addTPMachine, moveHead, h1']
  have e1 : ∀ p' T', step addTPMachine ⟨(6, s), p', T'⟩
      = ⟨(7, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, addTPMachine, moveHead]; rfl
  have e2 : ∀ p' T', step addTPMachine ⟨(7, s), p', T'⟩
      = ⟨(8, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, addTPMachine, moveHead]; rfl
  have e3 : ∀ p' T', step addTPMachine ⟨(8, s), p', T'⟩
      = ⟨(12, false), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, addTPMachine, moveHead]; rfl
  rw [e0, e1, e2, e3]

theorem ap_healB (h1 : T.getD p false = true) :
    run addTPMachine 2 ⟨(9, s), p, T⟩ = ⟨(9, true), p + 2, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step addTPMachine ⟨(9, s), p, T⟩ = ⟨(10, T.getD p false), p + 1, T⟩ := by
    simp only [step, addTPMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, addTPMachine, moveHead]; rfl

theorem ap_doneFin (h1 : T.getD p false = false) :
    run addTPMachine 2 ⟨(9, s), p, T⟩ = ⟨(11, false), p + 1, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step addTPMachine ⟨(9, s), p, T⟩ = ⟨(10, T.getD p false), p + 1, T⟩ := by
    simp only [step, addTPMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, addTPMachine, moveHead]
  rcases T.getD (p + 1) false with _ | _ <;> rfl

theorem ap_skipWf (h1 : T.getD p false = true) :
    run addTPMachine 2 ⟨(12, s), p, T⟩ = ⟨(12, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step addTPMachine ⟨(12, s), p, T⟩ = ⟨(13, T.getD p false), p + 1, T⟩ := by
    simp only [step, addTPMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, addTPMachine, moveHead]; rfl

theorem ap_crossWf (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run addTPMachine 2 ⟨(12, s), p, T⟩ = ⟨(0, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step addTPMachine ⟨(12, s), p, T⟩ = ⟨(13, T.getD p false), p + 1, T⟩ := by
    simp only [step, addTPMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, addTPMachine, moveHead, h2]

theorem ap_skipWr (h1 : T.getD p false = true) :
    run addTPMachine 2 ⟨(14, s), p, T⟩ = ⟨(14, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step addTPMachine ⟨(14, s), p, T⟩ = ⟨(15, T.getD p false), p + 1, T⟩ := by
    simp only [step, addTPMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, addTPMachine, moveHead]; rfl

theorem ap_crossWr (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run addTPMachine 2 ⟨(14, s), p, T⟩ = ⟨(2, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step addTPMachine ⟨(14, s), p, T⟩ = ⟨(15, T.getD p false), p + 1, T⟩ := by
    simp only [step, addTPMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, addTPMachine, moveHead, h2]

theorem ap_skipWh (h1 : T.getD p false = true) :
    run addTPMachine 2 ⟨(16, s), p, T⟩ = ⟨(16, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step addTPMachine ⟨(16, s), p, T⟩ = ⟨(17, T.getD p false), p + 1, T⟩ := by
    simp only [step, addTPMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, addTPMachine, moveHead]; rfl

theorem ap_crossWh (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run addTPMachine 2 ⟨(16, s), p, T⟩ = ⟨(9, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step addTPMachine ⟨(16, s), p, T⟩ = ⟨(17, T.getD p false), p + 1, T⟩ := by
    simp only [step, addTPMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, addTPMachine, moveHead, h2]

end StepsAP

/-! ### Scan invariants -/

theorem ap_skipBs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run addTPMachine (2 * k) ⟨(0, s), q, T⟩
      = ⟨(0, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), ap_skipB hk.1 hk.2]
    rfl

theorem ap_skipR1s (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run addTPMachine (2 * k) ⟨(2, s), q, T⟩
      = ⟨(2, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), ap_skipR1 (h k (by omega))]
    rfl

theorem ap_walks (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run addTPMachine (2 * k) ⟨(4, s), q, T⟩
      = ⟨(4, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), ap_walk (h k (by omega))]
    rfl

theorem ap_skipWfs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run addTPMachine (2 * k) ⟨(12, s), q, T⟩
      = ⟨(12, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), ap_skipWf (h k (by omega))]
    rfl

theorem ap_skipWrs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run addTPMachine (2 * k) ⟨(14, s), q, T⟩
      = ⟨(14, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), ap_skipWr (h k (by omega))]
    rfl

theorem ap_skipWhs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run addTPMachine (2 * k) ⟨(16, s), q, T⟩
      = ⟨(16, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), ap_skipWh (h k (by omega))]
    rfl

theorem ap_healBs (P : List Bool) (G v : ℕ) (E : List Bool) (hP : P.length = 2 * G + 2)
    (s : Bool) (i : ℕ) (hi : i ≤ v) :
    run addTPMachine (2 * i) ⟨(9, s), 2 * G + 2, P ++ (hlT v 0 ++ E)⟩
      = ⟨(9, if i = 0 then s else true), 2 * G + 2 + 2 * i, P ++ (hlT v i ++ E)⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have h1 : (P ++ (hlT v i ++ E)).getD (2 * G + 2 + 2 * i) false = true := by
      rw [show 2 * G + 2 + 2 * i = 2 * G + 2 + (2 * i) from rfl]
      exact liftJ P _ hP (hlE_pair_lo v i E (by omega))
    have hw : writeAt (P ++ (hlT v i ++ E)) (2 * G + 2 + 2 * i + 1) true
        = P ++ (hlT v (i + 1) ++ E) := by
      rw [show 2 * G + 2 + 2 * i + 1 = 2 * G + 2 + (2 * i + 1) from by omega,
        writeAt_append_right P _ (2 * G + 2) (2 * i + 1) true hP
          (by rw [List.length_append, hlT_length v i (by omega)]; omega),
        hlT_heal v i E (by omega)]
    rw [show 2 * (i + 1) = 2 * i + 2 from by ring, run_add, ih (by omega),
      ap_healB h1, hw]
    rfl

/-! ## The round and the loop -/

/-- One prefixed addition round. -/
theorem ap_round (G g : ℕ) (hg : g ≤ G) (A CAP v i : ℕ) (hi : i < A)
    (hvA : v + A ≤ CAP) (E : List Bool) (s : Bool) :
    run addTPMachine (4 * G + 2 * A + 2 * v + 4 * i + 12)
      ⟨(12, s), 0, cntT G g ++ (cntT A i ++ (jT CAP (v + i) ++ E))⟩
      = ⟨(12, false), 0, cntT G g ++ (cntT A (i + 1) ++ (jT CAP (v + i + 1) ++ E))⟩ := by
  have hW : (cntT G g).length = 2 * G + 2 := cntT_length G g hg
  have hA1 : (cntT A (i + 1)).length = 2 * A + 2 := cntT_length A (i + 1) (by omega)
  have r0 := ap_skipWfs (cntT G g ++ (cntT A i ++ (jT CAP (v + i) ++ E))) 0 G s
    (fun i' hi' => by simpa using cntE_lo G g _ i' hg hi')
  simp only [Nat.zero_add] at r0
  have r0' := ap_crossWf (s := if G = 0 then s else true) (p := 2 * G)
    (T := cntT G g ++ (cntT A i ++ (jT CAP (v + i) ++ E)))
    (cntE_cm_lo G g _ hg) (cntE_cm_hi G g _ hg)
  have r1 := ap_skipBs (cntT G g ++ (cntT A i ++ (jT CAP (v + i) ++ E)))
    (2 * G + 2) i false
    (fun i' hi' => ⟨by
      rw [show 2 * G + 2 + 2 * i' = 2 * G + 2 + (2 * i') from rfl]
      exact liftJ _ _ hW (cntE_mark_lo A i _ i' hi'), by
      rw [show 2 * G + 2 + 2 * i' + 1 = 2 * G + 2 + (2 * i' + 1) from by omega]
      exact liftJ _ _ hW (cntE_mark_hi A i _ i' hi')⟩)
  have r2 := ap_markB (s := if i = 0 then false else true) (p := 2 * G + 2 + 2 * i)
    (T := cntT G g ++ (cntT A i ++ (jT CAP (v + i) ++ E)))
    (by rw [show 2 * G + 2 + 2 * i = 2 * G + 2 + (2 * i) from rfl]
        exact liftJ _ _ hW (cntE_data A i _ (2 * i) (by omega) (by omega) (by omega)))
    (by rw [show 2 * G + 2 + 2 * i + 1 = 2 * G + 2 + (2 * i + 1) from by omega]
        exact liftJ _ _ hW (cntE_data A i _ (2 * i + 1) (by omega) (by omega) (by omega)))
  have hwm : writeAt (cntT G g ++ (cntT A i ++ (jT CAP (v + i) ++ E)))
      (2 * G + 2 + 2 * i + 1) false
      = cntT G g ++ (cntT A (i + 1) ++ (jT CAP (v + i) ++ E)) := by
    rw [show 2 * G + 2 + 2 * i + 1 = 2 * G + 2 + (2 * i + 1) from by omega,
      writeAt_append_right _ _ (2 * G + 2) (2 * i + 1) false hW
        (by rw [List.length_append, cntT_length A i (by omega)]; omega),
      cntT_mark A i _ hi]
  rw [hwm] at r2
  have r3 := ap_skipWrs (cntT G g ++ (cntT A (i + 1) ++ (jT CAP (v + i) ++ E))) 0 G true
    (fun i' hi' => by simpa using cntE_lo G g _ i' hg hi')
  simp only [Nat.zero_add] at r3
  have r3' := ap_crossWr (s := if G = 0 then true else true) (p := 2 * G)
    (T := cntT G g ++ (cntT A (i + 1) ++ (jT CAP (v + i) ++ E)))
    (cntE_cm_lo G g _ hg) (cntE_cm_hi G g _ hg)
  have r4 := ap_skipR1s (cntT G g ++ (cntT A (i + 1) ++ (jT CAP (v + i) ++ E)))
    (2 * G + 2) A false
    (fun i' hi' => by
      rw [show 2 * G + 2 + 2 * i' = 2 * G + 2 + (2 * i') from rfl]
      exact liftJ _ _ hW (cntE_lo A (i + 1) _ i' (by omega) hi'))
  have r5 := ap_crossR1 (s := if A = 0 then false else true) (p := 2 * G + 2 + 2 * A)
    (T := cntT G g ++ (cntT A (i + 1) ++ (jT CAP (v + i) ++ E)))
    (by rw [show 2 * G + 2 + 2 * A = 2 * G + 2 + (2 * A) from rfl]
        exact liftJ _ _ hW (cntE_cm_lo A (i + 1) _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * A + 1 = 2 * G + 2 + (2 * A + 1) from by omega]
        exact liftJ _ _ hW (cntE_cm_hi A (i + 1) _ (by omega)))
  have r6 := ap_walks (cntT G g ++ (cntT A (i + 1) ++ (jT CAP (v + i) ++ E)))
    (2 * G + 2 + 2 * A + 2) (v + i) false
    (fun i' hi' => by
      rw [show 2 * G + 2 + 2 * A + 2 + 2 * i' = 2 * G + 2 + (2 * A + 2 + 2 * i')
          from by omega, ← jsT_zero CAP (v + i)]
      exact liftJ2 _ _ _ hW hA1
        (jsE_data CAP (v + i) 0 _ (2 * i') (by omega) (by omega) (by omega)))
  have r7 := ap_four_incr (s := if v + i = 0 then false else true)
    (p := 2 * G + 2 + (2 * A + 2 + 2 * (v + i)))
    (T := cntT G g ++ (cntT A (i + 1) ++ (jT CAP (v + i) ++ E)))
    (by rw [← jsT_zero CAP (v + i)]
        exact liftJ2 _ _ _ hW hA1 (jsE_m_lo CAP (v + i) 0 _ (by omega)))
  rw [W4_append_right2 (cntT G g) (cntT A (i + 1)) (jT CAP (v + i) ++ E) (2 * G + 2)
      (2 * A + 2) (2 * (v + i)) true true false true hW hA1
      (by rw [List.length_append, jT_length CAP (v + i) (by omega)]; omega),
    jT_incr CAP (v + i) _ (by omega)] at r7
  rw [show 4 * G + 2 * A + 2 * v + 4 * i + 12
      = 2 * G + (2 + (2 * i + (2 + (2 * G + (2 + (2 * A + (2 + (2 * (v + i) + 4))))))))
      from by omega,
    run_add, r0, run_add, r0', run_add, r1, run_add, r2, run_add, r3, run_add, r3',
    run_add, r4, run_add, r5, run_add, r6,
    show 2 * G + 2 + 2 * A + 2 + 2 * (v + i) = 2 * G + 2 + (2 * A + 2 + 2 * (v + i))
      from by omega,
    r7]

def apClockN (G A v : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => apClockN G A v i + (4 * G + 2 * A + 2 * v + 4 * i + 12)

theorem ap_run_rounds (G g : ℕ) (hg : g ≤ G) (A CAP v : ℕ) (hvA : v + A ≤ CAP)
    (E : List Bool) (i : ℕ) (hi : i ≤ A) (s : Bool) :
    run addTPMachine (apClockN G A v i) ⟨(12, s), 0, cntT G g ++ (cntT A 0
      ++ (jT CAP v ++ E))⟩
      = ⟨(12, if i = 0 then s else false), 0,
          cntT G g ++ (cntT A i ++ (jT CAP (v + i) ++ E))⟩ := by
  induction i with
  | zero => simp only [apClockN]; rw [run_zero]; simp
  | succ i ih =>
    rw [show apClockN G A v (i + 1)
        = apClockN G A v i + (4 * G + 2 * A + 2 * v + 4 * i + 12) from rfl,
      run_add, ih (by omega), ap_round G g hg A CAP v i (by omega) hvA E _,
      if_neg (by omega), show v + (i + 1) = v + i + 1 from by omega]

def apClock (G A v : ℕ) : ℕ :=
  apClockN G A v A + (2 * G + (2 + (2 * A + (2 + (2 * G + (2 + (2 * A + 2)))))))

/-- **The prefixed adder runs to completion** — `rep_run`'s hypothesis shape. -/
theorem addTP_run (G g : ℕ) (hg : g ≤ G) (A CAP v : ℕ) (hvA : v + A ≤ CAP)
    (E : List Bool) :
    run addTPMachine (apClock G A v)
      (init addTPMachine (cntT G g ++ (unaryD A ++ (jT CAP v ++ E))))
      = ⟨(11, false), 2 * G + 2 + 2 * A + 1,
          cntT G g ++ (unaryD A ++ (jT CAP (v + A) ++ E))⟩ := by
  have hW : (cntT G g).length = 2 * G + 2 := cntT_length G g hg
  rw [init_ap,
    show (cntT G g ++ (unaryD A ++ (jT CAP v ++ E)) : List Bool)
      = cntT G g ++ (cntT A 0 ++ (jT CAP v ++ E)) from by rw [cntT_zero]]
  simp only [apClock]
  have f0 := ap_skipWfs (cntT G g ++ (cntT A A ++ (jT CAP (v + A) ++ E))) 0 G false
    (fun i hi => by simpa using cntE_lo G g _ i hg hi)
  simp only [Nat.zero_add] at f0
  have f0' := ap_crossWf (s := if G = 0 then false else true) (p := 2 * G)
    (T := cntT G g ++ (cntT A A ++ (jT CAP (v + A) ++ E)))
    (cntE_cm_lo G g _ hg) (cntE_cm_hi G g _ hg)
  have f1 := ap_skipBs (cntT G g ++ (cntT A A ++ (jT CAP (v + A) ++ E))) (2 * G + 2) A
    false
    (fun i hi => ⟨by
      rw [show 2 * G + 2 + 2 * i = 2 * G + 2 + (2 * i) from rfl]
      exact liftJ _ _ hW (cntE_mark_lo A A _ i hi), by
      rw [show 2 * G + 2 + 2 * i + 1 = 2 * G + 2 + (2 * i + 1) from by omega]
      exact liftJ _ _ hW (cntE_mark_hi A A _ i hi)⟩)
  have f2 := ap_doneB (s := if A = 0 then false else true) (p := 2 * G + 2 + 2 * A)
    (T := cntT G g ++ (cntT A A ++ (jT CAP (v + A) ++ E)))
    (by rw [show 2 * G + 2 + 2 * A = 2 * G + 2 + (2 * A) from rfl]
        exact liftJ _ _ hW (cntE_cm_lo A A _ (le_refl A)))
    (by rw [show 2 * G + 2 + 2 * A + 1 = 2 * G + 2 + (2 * A + 1) from by omega]
        exact liftJ _ _ hW (cntE_cm_hi A A _ (le_refl A)))
  have f3 := ap_skipWhs (cntT G g ++ (hlT A 0 ++ (jT CAP (v + A) ++ E))) 0 G false
    (fun i hi => by simpa using cntE_lo G g _ i hg hi)
  simp only [Nat.zero_add] at f3
  have f3' := ap_crossWh (s := if G = 0 then false else true) (p := 2 * G)
    (T := cntT G g ++ (hlT A 0 ++ (jT CAP (v + A) ++ E)))
    (cntE_cm_lo G g _ hg) (cntE_cm_hi G g _ hg)
  have f4 := ap_healBs (cntT G g) G A (jT CAP (v + A) ++ E) hW false A (le_refl A)
  have f5 := ap_doneFin (s := if A = 0 then false else true) (p := 2 * G + 2 + 2 * A)
    (T := cntT G g ++ (hlT A A ++ (jT CAP (v + A) ++ E)))
    (by rw [show 2 * G + 2 + 2 * A = 2 * G + 2 + (2 * A) from rfl]
        exact liftJ _ _ hW (hlE_cm_lo A _))
  rw [run_add, ap_run_rounds G g hg A CAP v hvA E A (le_refl A) false, ite_self,
    run_add, f0, run_add, f0', run_add, f1, run_add, f2, ← hlT_zero, run_add, f3,
    run_add, f3', run_add, f4, f5, hlT_last]

theorem addTP_halt : addTPMachine.halt ((11 : Fin 18), false) = true := rfl

/-! ## THE MULTIPLIER -/

/-- **E2'S MULTIPLIER**: `repMachine` over the prefixed adder — the grand counter IS the
multiplicand.  `M` grand rounds each add `A` into the padded accumulator: `v + M·A`, at the
explicit clock, no new loop machinery. -/
theorem rep_mul_run (M A CAP v : ℕ) (hcap : v + M * A ≤ CAP) (E : List Bool) :
    run (repMachine addTPMachine)
      (repRounds (fun t => apClock M A (v + t * A)) M + (4 * M + 4))
      (init (repMachine addTPMachine) (cntT M 0 ++ (unaryD A ++ (jT CAP v ++ E))))
      = ⟨Sum.inl (4, false), 2 * M + 1,
          unaryD M ++ (unaryD A ++ (jT CAP (v + M * A) ++ E))⟩ := by
  have h := rep_run addTPMachine M
    (fun t => unaryD A ++ (jT CAP (v + t * A) ++ E))
    (fun t => apClock M A (v + t * A))
    (fun _ => (11, false)) (fun _ => 2 * M + 2 + 2 * A + 1)
    (fun t ht => by
      constructor
      · have hr := addTP_run M (t + 1) (by omega) A CAP (v + t * A)
          (by have : (t + 1) * A ≤ M * A := Nat.mul_le_mul_right _ (by omega)
              have : v + (t + 1) * A ≤ v + M * A := by omega
              calc v + t * A + A = v + (t + 1) * A := by ring
                _ ≤ v + M * A := this
                _ ≤ CAP := hcap) E
        rw [show v + t * A + A = v + (t + 1) * A from by ring] at hr
        exact hr
      · rfl)
  simpa using h

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitMulT