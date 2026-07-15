import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitNest

/-!
# Cook–Levin M2 emitter, E4 (iv) — the nested loop with a live variable (and the zeroing pass)

Fourth brick of E4: the nested harness of E4 (iii) upgraded with a **live inner loop variable**.
`nestVarMachine` runs `for t in range B: for p in range P: splice p` — each inner iteration emits
`encodeNat p` from a capacity-bounded counter that is **incremented in place** per inner round (E4 (ii))
and — the one mechanism new to this brick — **zeroed** between outer rounds: after the inner bound's heal,
a zeroing walk rewrites the full variable `11^P 01` back to `01 00^P` inside its fixed footprint, handing
the next outer round a pristine `jT P 0`.

Four static regions: outer bound `cntT B t`, inner bound `cntT P i`, the variable `jsT/jhT/jT` (capacity
`P`), the doubled output.  The splice sub-rounds' find crosses **two** bound regions; the emit seek runs
from inside the variable across its boundary and padding to the output terminator; the output sits under a
**three-part** work prefix (`preD3_*`, `writes_snoc3`).  Everything else is the practiced mirror — the
variable's descriptors and structural writes are E4 (ii)'s verbatim.

**Top theorem** (`nestVar_run`, promise `0 < P`): on
`unaryD B ++ (unaryD P ++ (jT P 0 ++ encodeD out))` the machine halts by itself at the explicit clock with
tape **exactly** `unaryD B ++ (unaryD P ++ (jT P 0 ++ encodeD (out ++ blkRep (rangeEnc P) B)))` — `B`
copies of the full range block, both bounds restored, **the variable zeroed**: every work region leaves in
its entry state, so the harness is composable.  With this, E4's mechanism inventory is complete; the family
emitters are instantiations (add the second live variable at its own static address, swap the body's splice
list for the template block streams).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitNestVar

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinEmit (encodeNat)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCompare
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCopy
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitAppendBlock
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSplice
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoop
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRange
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitNest

/-! ## Three-part prefix lifts -/

/-- Lifting a suffix-generic `getD` fact past two known-length prefixes. -/
theorem liftJ2 (A C X : List Bool) {qa qc c : ℕ} (ha : A.length = qa) (hc : C.length = qc)
    {b : Bool} (h : X.getD c false = b) :
    (A ++ (C ++ X)).getD (qa + (qc + c)) false = b := by
  rw [getD_append_left_length' A _ ha, getD_append_left_length' C _ hc]
  exact h

/-- `writeAt` past two known-length prefixes. -/
theorem writeAt_append_right2 (A C X : List Bool) (qa qc p : ℕ) (w : Bool)
    (ha : A.length = qa) (hc : C.length = qc) (hp : p < X.length) :
    writeAt (A ++ (C ++ X)) (qa + (qc + p)) w = A ++ (C ++ writeAt X p w) := by
  rw [writeAt_append_right A _ qa (qc + p) w ha
      (by rw [List.length_append]; omega),
    writeAt_append_right C X qc p w hc hp]

/-- Output data pairs read equal, under a three-part work prefix. -/
theorem preD3_data_eq (A C D out : List Bool) (q i : ℕ)
    (hq : A.length + C.length + D.length = q) (h : i < out.length) :
    (A ++ (C ++ (D ++ encodeD out))).getD (q + 2 * i) false
      = (A ++ (C ++ (D ++ encodeD out))).getD (q + 2 * i + 1) false := by
  have := preD_data_eq (A ++ (C ++ D)) out q i
    (by simp only [List.length_append]; omega) h
  simpa [List.append_assoc] using this

theorem preD3_mark_lo (A C D out : List Bool) (q : ℕ)
    (hq : A.length + C.length + D.length = q) :
    (A ++ (C ++ (D ++ encodeD out))).getD (q + 2 * out.length) false = false := by
  have := preD_mark_lo (A ++ (C ++ D)) out q (by simp only [List.length_append]; omega)
  simpa [List.append_assoc] using this

theorem preD3_mark_hi (A C D out : List Bool) (q : ℕ)
    (hq : A.length + C.length + D.length = q) :
    (A ++ (C ++ (D ++ encodeD out))).getD (q + 2 * out.length + 1) false = true := by
  have := preD_mark_hi (A ++ (C ++ D)) out q (by simp only [List.length_append]; omega)
  simpa [List.append_assoc] using this

/-- The four-write snoc under a three-part work prefix. -/
theorem writes_snoc3 (A C D out : List Bool) (q : ℕ)
    (hq : A.length + C.length + D.length = q) (b : Bool) :
    writeAt (writeAt (writeAt (writeAt (A ++ (C ++ (D ++ encodeD out)))
        (q + 2 * out.length) b) (q + 2 * out.length + 1) b) (q + 2 * out.length + 2) false)
        (q + 2 * out.length + 3) true
      = A ++ (C ++ (D ++ encodeD (out ++ [b]))) := by
  have h := writes_snoc (A ++ (C ++ D)) out q (by simp only [List.length_append]; omega) b
  simpa [List.append_assoc] using h

/-! ## The zeroing-walk descriptor

At walk stage `m` (`m ≤ P - 1`): pair `0` rewritten to the fresh `01` marker, pairs `1..m` zeroed, pairs
`m+1..P-1` still `11`, the old marker `01` at pair `P`. -/

def zeroT (P m : ℕ) : List Bool :=
  [false, true] ++ (List.replicate (2 * m) false
    ++ (List.replicate (2 * (P - 1 - m)) true ++ [false, true]))

theorem zeroT_length (P m : ℕ) (hm : m ≤ P - 1) (hP : 0 < P) :
    (zeroT P m).length = 2 * P + 2 := by
  simp only [zeroT, List.length_append, List.length_replicate, List.length_cons, List.length_nil]
  omega

/-- Stage-`m` data pair `m+1` (low cell), while unzeroed pairs remain. -/
theorem zeroE_data_lo (P m : ℕ) (E : List Bool) (h : m + 1 ≤ P - 1) :
    (zeroT P m ++ E).getD (2 * (m + 1)) false = true := by
  rw [zeroT]
  simp only [List.append_assoc]
  rw [show 2 * (m + 1) = 2 + (2 * m + 0) from by omega,
    getD_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl),
    getD_append_left_length' _ _ List.length_replicate,
    List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem zeroE_data_hi (P m : ℕ) (E : List Bool) (h : m + 1 ≤ P - 1) :
    (zeroT P m ++ E).getD (2 * (m + 1) + 1) false = true := by
  rw [zeroT]
  simp only [List.append_assoc]
  rw [show 2 * (m + 1) + 1 = 2 + (2 * m + 1) from by omega,
    getD_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl),
    getD_append_left_length' _ _ List.length_replicate,
    List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

/-- Stage-`(P-1)` old-marker pair `P` (low cell). -/
theorem zeroE_m_lo (P : ℕ) (E : List Bool) (hP : 0 < P) :
    (zeroT P (P - 1) ++ E).getD (2 * P) false = false := by
  rw [zeroT]
  simp only [List.append_assoc]
  rw [show 2 * P = 2 + (2 * (P - 1) + (2 * (P - 1 - (P - 1)) + 0)) from by omega,
    getD_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl),
    getD_append_left_length' _ _ List.length_replicate,
    getD_append_left_length' _ _ List.length_replicate]
  rfl

theorem zeroE_m_hi (P : ℕ) (E : List Bool) (hP : 0 < P) :
    (zeroT P (P - 1) ++ E).getD (2 * P + 1) false = true := by
  rw [zeroT]
  simp only [List.append_assoc]
  rw [show 2 * P + 1 = 2 + (2 * (P - 1) + (2 * (P - 1 - (P - 1)) + 1)) from by omega,
    getD_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl),
    getD_append_left_length' _ _ List.length_replicate,
    getD_append_left_length' _ _ List.length_replicate]
  rfl

/-! ### The three structural zeroing writes -/

/-- Peeling one element off a nonempty `replicate` without touching other occurrences of its length. -/
theorem replicate_split_one {α : Type} (n : ℕ) (hn : 0 < n) (a : α) :
    List.replicate n a = a :: List.replicate (n - 1) a := by
  conv_lhs => rw [show n = (n - 1) + 1 from by omega]
  rw [List.replicate_succ]

/-- The head rewrite: the full variable's first pair becomes the fresh `01` marker. -/
theorem zeroT_head (P : ℕ) (E : List Bool) (hP : 0 < P) :
    writeAt (writeAt (jT P P ++ E) 0 false) 1 true = zeroT P 0 ++ E := by
  have hl : (jT P P).length = 2 * P + 2 := jT_length P P (le_refl P)
  have e1 : writeAt (jT P P ++ E) 0 false
      = (false :: (List.replicate (2 * P - 1) true ++ [false, true])) ++ E := by
    rw [writeAt_of_lt false (by rw [List.length_append]; omega),
      List.set_append_left _ _ (by omega), jT, Nat.sub_self,
      replicate_split_one (2 * P) (by omega)]
    simp only [Nat.mul_zero, List.replicate_zero, List.append_nil, List.cons_append,
      List.set_cons_zero]
  rw [e1, writeAt_of_lt true (by
      simp only [List.length_append, List.length_cons, List.length_replicate]
      omega),
    List.set_append_left _ _ (by
      simp only [List.length_cons, List.length_append, List.length_replicate]
      omega),
    List.set_cons_succ, replicate_split_one (2 * P - 1) (by omega)]
  simp only [List.cons_append, List.set_cons_zero]
  rw [zeroT, show 2 * (P - 1 - 0) = 2 * P - 1 - 1 from by omega]
  simp [List.append_assoc]

/-- One walk step: zero the next `11` pair. -/
theorem zeroT_step (P m : ℕ) (E : List Bool) (h : m + 1 ≤ P - 1) :
    writeAt (writeAt (zeroT P m ++ E) (2 * (m + 1)) false) (2 * (m + 1) + 1) false
      = zeroT P (m + 1) ++ E := by
  have hP : 0 < P := by omega
  have hl : (zeroT P m).length = 2 * P + 2 := zeroT_length P m (by omega) hP
  have e1 : writeAt (zeroT P m ++ E) (2 * (m + 1)) false
      = ([false, true] ++ (List.replicate (2 * m) false
          ++ (false :: (List.replicate (2 * (P - 1 - m) - 1) true ++ [false, true])))) ++ E := by
    rw [writeAt_of_lt false (by rw [List.length_append]; omega),
      List.set_append_left _ _ (by omega), zeroT]
    simp only [List.append_assoc]
    rw [show 2 * (m + 1) = 2 + (2 * m + 0) from by omega,
      set_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl),
      set_append_left_length' _ _ List.length_replicate,
      replicate_split_one (2 * (P - 1 - m)) (by omega)]
    simp only [List.cons_append, List.set_cons_zero]
    simp only [List.cons_append, List.append_assoc]
  rw [e1, writeAt_of_lt false (by
      simp only [List.length_append, List.length_cons, List.length_replicate]
      omega),
    List.set_append_left _ _ (by
      simp only [List.length_append, List.length_cons, List.length_replicate]
      omega)]
  rw [show 2 * (m + 1) + 1 = 2 + (2 * m + 1) from by omega,
    set_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl),
    set_append_left_length' _ _ List.length_replicate, List.set_cons_succ,
    replicate_split_one (2 * (P - 1 - m) - 1) (by omega)]
  simp only [List.cons_append, List.set_cons_zero]
  rw [cons_cons_append false false, ← List.append_assoc (List.replicate (2 * m) false),
    show ([false, false] : List Bool) = List.replicate 2 false from rfl, ← List.replicate_add,
    show 2 * m + 2 = 2 * (m + 1) from by ring, zeroT,
    show 2 * (P - 1 - (m + 1)) = 2 * (P - 1 - m) - 1 - 1 from by omega]
  simp

/-- The last walk step: zero the old marker — the variable is exactly `jT P 0`. -/
theorem zeroT_last (P : ℕ) (E : List Bool) (hP : 0 < P) :
    writeAt (writeAt (zeroT P (P - 1) ++ E) (2 * P) false) (2 * P + 1) false
      = jT P 0 ++ E := by
  have e0 : zeroT P (P - 1)
      = [false, true] ++ (List.replicate (2 * (P - 1)) false ++ [false, true]) := by
    rw [zeroT, show P - 1 - (P - 1) = 0 from by omega]
    simp
  have hl : (zeroT P (P - 1)).length = 2 * P + 2 := zeroT_length P (P - 1) (le_refl _) hP
  rw [e0] at hl
  have e1 : writeAt (([false, true] ++ (List.replicate (2 * (P - 1)) false ++ [false, true]))
        ++ E) (2 * P) false
      = ([false, true] ++ (List.replicate (2 * (P - 1)) false ++ [false, true])) ++ E := by
    rw [writeAt_of_lt false (by rw [List.length_append]; omega),
      List.set_append_left _ _ (by omega)]
    simp only [List.append_assoc]
    rw [show 2 * P = 2 + (2 * (P - 1) + 0) from by omega,
      set_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl),
      set_append_left_length' _ _ List.length_replicate]
    simp only [List.cons_append, List.set_cons_zero]
    simp only [List.cons_append, List.append_assoc]
  rw [e0, e1, writeAt_of_lt false (by
      simp only [List.length_append, List.length_cons, List.length_replicate]
      omega),
    List.set_append_left _ _ (by
      simp only [List.length_append, List.length_cons, List.length_replicate]
      omega)]
  rw [show 2 * P + 1 = 2 + (2 * (P - 1) + 1) from by omega,
    set_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl),
    set_append_left_length' _ _ List.length_replicate]
  simp only [List.cons_append, List.set_cons_succ, List.set_cons_zero]
  rw [cons_cons_append false false, ← List.append_assoc (List.replicate (2 * (P - 1)) false),
    show ([false, false] : List Bool) = List.replicate 2 false from rfl, ← List.replicate_add,
    show 2 * (P - 1) + 2 = 2 * P from by omega, jT]
  simp

/-! ## The machine

Control: `Fin 51 × Bool` (stored low cell).  Phases: `0/1` find in the outer bound (mark + reset ⇒ inner
loop, boundary ⇒ outer restore), `2/3` find-path skip of the outer bound, `4/5` find in the inner bound
(mark + reset ⇒ splice, boundary + reset ⇒ inner finale), `6/7`+`8/9` the splice find's two bound skips,
`10/11` find in the variable (mark ⇒ seek, boundary ⇒ the closing `false`), `12/13` seek the variable's
rest, `14/15` seek the output, `16–19` the doubled-`true` snoc (reset ⇒ next splice sub-round), `20/21`
the final seek, `22–25` the doubled-`false` snoc (reset ⇒ heal path), `26/27`+`28/29` the heal path's two
bound skips, `30/31` heal the variable (boundary ⇒ increment), `32–35` the in-place increment (reset ⇒
next inner round), `36/37` the finale's bound skip, `38/39` heal the inner bound (boundary ⇒ the zeroing
walk), `40/41` the zero head-rewrite, `42/43` the walk's classify, `44/45` zero a data pair, `46/47` zero
the old marker (reset ⇒ next outer round), `48/49` restore the outer bound, `50` = halt. -/

def nestVarMachine : Machine where
  State := Fin 51 × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, false)
  halt := fun s => decide (s.1 = 50)
  δ := fun s b =>
    if s.1 = 0 then ((1, b), none, 1)
    else if s.1 = 1 then
      (if s.2 then (if b then ((2, s.2), some false, 3) else ((0, s.2), none, 1))
       else (if b then ((48, s.2), none, 3) else ((50, s.2), none, 2)))
    else if s.1 = 2 then ((3, b), none, 1)
    else if s.1 = 3 then
      (if s.2 then ((2, s.2), none, 1)
       else (if b then ((4, s.2), none, 1) else ((50, s.2), none, 2)))
    else if s.1 = 4 then ((5, b), none, 1)
    else if s.1 = 5 then
      (if s.2 then (if b then ((6, s.2), some false, 3) else ((4, s.2), none, 1))
       else (if b then ((36, s.2), none, 3) else ((50, s.2), none, 2)))
    else if s.1 = 6 then ((7, b), none, 1)
    else if s.1 = 7 then
      (if s.2 then ((6, s.2), none, 1)
       else (if b then ((8, s.2), none, 1) else ((50, s.2), none, 2)))
    else if s.1 = 8 then ((9, b), none, 1)
    else if s.1 = 9 then
      (if s.2 then ((8, s.2), none, 1)
       else (if b then ((10, s.2), none, 1) else ((50, s.2), none, 2)))
    else if s.1 = 10 then ((11, b), none, 1)
    else if s.1 = 11 then
      (if s.2 then (if b then ((12, s.2), some false, 1) else ((10, s.2), none, 1))
       else (if b then ((20, s.2), none, 1) else ((50, s.2), none, 2)))
    else if s.1 = 12 then ((13, b), none, 1)
    else if s.1 = 13 then
      (if b = s.2 then ((12, s.2), none, 1) else ((14, s.2), none, 1))
    else if s.1 = 14 then ((15, b), none, 1)
    else if s.1 = 15 then
      (if b = s.2 then ((14, s.2), none, 1) else ((16, s.2), none, 0))
    else if s.1 = 16 then ((17, s.2), some true, 1)
    else if s.1 = 17 then ((18, s.2), some true, 1)
    else if s.1 = 18 then ((19, s.2), some false, 1)
    else if s.1 = 19 then ((6, s.2), some true, 3)
    else if s.1 = 20 then ((21, b), none, 1)
    else if s.1 = 21 then
      (if b = s.2 then ((20, s.2), none, 1) else ((22, s.2), none, 0))
    else if s.1 = 22 then ((23, s.2), some false, 1)
    else if s.1 = 23 then ((24, s.2), some false, 1)
    else if s.1 = 24 then ((25, s.2), some false, 1)
    else if s.1 = 25 then ((26, s.2), some true, 3)
    else if s.1 = 26 then ((27, b), none, 1)
    else if s.1 = 27 then
      (if s.2 then ((26, s.2), none, 1)
       else (if b then ((28, s.2), none, 1) else ((50, s.2), none, 2)))
    else if s.1 = 28 then ((29, b), none, 1)
    else if s.1 = 29 then
      (if s.2 then ((28, s.2), none, 1)
       else (if b then ((30, s.2), none, 1) else ((50, s.2), none, 2)))
    else if s.1 = 30 then ((31, b), none, 1)
    else if s.1 = 31 then
      (if s.2 then (if b then ((50, s.2), none, 2) else ((30, true), some true, 1))
       else (if b then ((32, s.2), none, 0) else ((50, s.2), none, 2)))
    else if s.1 = 32 then ((33, s.2), some true, 1)
    else if s.1 = 33 then ((34, s.2), some true, 1)
    else if s.1 = 34 then ((35, s.2), some false, 1)
    else if s.1 = 35 then ((2, s.2), some true, 3)
    else if s.1 = 36 then ((37, b), none, 1)
    else if s.1 = 37 then
      (if s.2 then ((36, s.2), none, 1)
       else (if b then ((38, s.2), none, 1) else ((50, s.2), none, 2)))
    else if s.1 = 38 then ((39, b), none, 1)
    else if s.1 = 39 then
      (if s.2 then (if b then ((50, s.2), none, 2) else ((38, true), some true, 1))
       else (if b then ((40, s.2), none, 1) else ((50, s.2), none, 2)))
    else if s.1 = 40 then ((41, s.2), some false, 1)
    else if s.1 = 41 then ((42, s.2), some true, 1)
    else if s.1 = 42 then ((43, b), none, 1)
    else if s.1 = 43 then
      (if b = s.2 then ((44, s.2), none, 0) else ((46, s.2), none, 0))
    else if s.1 = 44 then ((45, s.2), some false, 1)
    else if s.1 = 45 then ((42, s.2), some false, 1)
    else if s.1 = 46 then ((47, s.2), some false, 1)
    else if s.1 = 47 then ((0, s.2), some false, 3)
    else if s.1 = 48 then ((49, b), none, 1)
    else if s.1 = 49 then
      (if s.2 then (if b then ((50, s.2), none, 2) else ((48, true), some true, 1))
       else ((50, s.2), none, 2))
    else ((s.1, s.2), none, 2)
  accept := fun _ => false

theorem init_nv (x : List Bool) : init nestVarMachine x = ⟨(0, false), 0, x⟩ := rfl

/-! ### Step and pair-step lemmas (the practiced mirror, kept to the pair level) -/

section Steps
variable {s : Bool} {p : ℕ} {T : List Bool}

theorem nv_step_lo {ph ph' : Fin 51} (hph : nestVarMachine.halt (ph, s) = false)
    (hδ : ∀ b, nestVarMachine.δ (ph, s) b = ((ph', b), none, 1)) :
    step nestVarMachine ⟨(ph, s), p, T⟩ = ⟨(ph', T.getD p false), p + 1, T⟩ := by
  simp only [step, hph, Bool.false_eq_true, if_false, hδ]
  rfl

theorem run_two_skipB' (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run nestVarMachine 2 ⟨(0, s), p, T⟩ = ⟨(0, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step nestVarMachine ⟨(0, s), p, T⟩ = ⟨(1, T.getD p false), p + 1, T⟩ := by
    simp only [step, nestVarMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, nestVarMachine, moveHead, h2]

theorem run_two_markB' (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run nestVarMachine 2 ⟨(0, s), p, T⟩ = ⟨(2, true), 0, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step nestVarMachine ⟨(0, s), p, T⟩ = ⟨(1, T.getD p false), p + 1, T⟩ := by
    simp only [step, nestVarMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, nestVarMachine, moveHead, h2]

theorem run_two_toRstB' (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run nestVarMachine 2 ⟨(0, s), p, T⟩ = ⟨(48, false), 0, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step nestVarMachine ⟨(0, s), p, T⟩ = ⟨(1, T.getD p false), p + 1, T⟩ := by
    simp only [step, nestVarMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, nestVarMachine, moveHead, h2]

theorem run_two_skipWI (h1 : T.getD p false = true) :
    run nestVarMachine 2 ⟨(2, s), p, T⟩ = ⟨(2, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step nestVarMachine ⟨(2, s), p, T⟩ = ⟨(3, T.getD p false), p + 1, T⟩ := by
    simp only [step, nestVarMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, nestVarMachine, moveHead]; rfl

theorem run_two_crossWI (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run nestVarMachine 2 ⟨(2, s), p, T⟩ = ⟨(4, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step nestVarMachine ⟨(2, s), p, T⟩ = ⟨(3, T.getD p false), p + 1, T⟩ := by
    simp only [step, nestVarMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, nestVarMachine, moveHead, h2]

theorem run_two_skipP' (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run nestVarMachine 2 ⟨(4, s), p, T⟩ = ⟨(4, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step nestVarMachine ⟨(4, s), p, T⟩ = ⟨(5, T.getD p false), p + 1, T⟩ := by
    simp only [step, nestVarMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, nestVarMachine, moveHead, h2]

theorem run_two_markP' (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run nestVarMachine 2 ⟨(4, s), p, T⟩ = ⟨(6, true), 0, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step nestVarMachine ⟨(4, s), p, T⟩ = ⟨(5, T.getD p false), p + 1, T⟩ := by
    simp only [step, nestVarMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, nestVarMachine, moveHead, h2]

theorem run_two_doneP' (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run nestVarMachine 2 ⟨(4, s), p, T⟩ = ⟨(36, false), 0, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step nestVarMachine ⟨(4, s), p, T⟩ = ⟨(5, T.getD p false), p + 1, T⟩ := by
    simp only [step, nestVarMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, nestVarMachine, moveHead, h2]

theorem run_two_skipWS (h1 : T.getD p false = true) :
    run nestVarMachine 2 ⟨(6, s), p, T⟩ = ⟨(6, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step nestVarMachine ⟨(6, s), p, T⟩ = ⟨(7, T.getD p false), p + 1, T⟩ := by
    simp only [step, nestVarMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, nestVarMachine, moveHead]; rfl

theorem run_two_crossWS (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run nestVarMachine 2 ⟨(6, s), p, T⟩ = ⟨(8, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step nestVarMachine ⟨(6, s), p, T⟩ = ⟨(7, T.getD p false), p + 1, T⟩ := by
    simp only [step, nestVarMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, nestVarMachine, moveHead, h2]

theorem run_two_skipPS (h1 : T.getD p false = true) :
    run nestVarMachine 2 ⟨(8, s), p, T⟩ = ⟨(8, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step nestVarMachine ⟨(8, s), p, T⟩ = ⟨(9, T.getD p false), p + 1, T⟩ := by
    simp only [step, nestVarMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, nestVarMachine, moveHead]; rfl

theorem run_two_crossPS (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run nestVarMachine 2 ⟨(8, s), p, T⟩ = ⟨(10, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step nestVarMachine ⟨(8, s), p, T⟩ = ⟨(9, T.getD p false), p + 1, T⟩ := by
    simp only [step, nestVarMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, nestVarMachine, moveHead, h2]

theorem run_two_skipJ' (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run nestVarMachine 2 ⟨(10, s), p, T⟩ = ⟨(10, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step nestVarMachine ⟨(10, s), p, T⟩ = ⟨(11, T.getD p false), p + 1, T⟩ := by
    simp only [step, nestVarMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, nestVarMachine, moveHead, h2]

theorem run_two_markJ' (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run nestVarMachine 2 ⟨(10, s), p, T⟩ = ⟨(12, true), p + 2, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step nestVarMachine ⟨(10, s), p, T⟩ = ⟨(11, T.getD p false), p + 1, T⟩ := by
    simp only [step, nestVarMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, nestVarMachine, moveHead, h2]

theorem run_two_doneJ' (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run nestVarMachine 2 ⟨(10, s), p, T⟩ = ⟨(20, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step nestVarMachine ⟨(10, s), p, T⟩ = ⟨(11, T.getD p false), p + 1, T⟩ := by
    simp only [step, nestVarMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, nestVarMachine, moveHead, h2]

theorem run_two_seekA' (h : T.getD p false = T.getD (p + 1) false) :
    run nestVarMachine 2 ⟨(12, s), p, T⟩ = ⟨(12, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step nestVarMachine ⟨(12, s), p, T⟩ = ⟨(13, T.getD p false), p + 1, T⟩ := by
    simp only [step, nestVarMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, nestVarMachine, moveHead, h2]

theorem run_two_crossA' (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run nestVarMachine 2 ⟨(12, s), p, T⟩ = ⟨(14, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step nestVarMachine ⟨(12, s), p, T⟩ = ⟨(13, T.getD p false), p + 1, T⟩ := by
    simp only [step, nestVarMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, nestVarMachine, moveHead, h2']

theorem run_two_seekB' (h : T.getD p false = T.getD (p + 1) false) :
    run nestVarMachine 2 ⟨(14, s), p, T⟩ = ⟨(14, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step nestVarMachine ⟨(14, s), p, T⟩ = ⟨(15, T.getD p false), p + 1, T⟩ := by
    simp only [step, nestVarMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, nestVarMachine, moveHead, h2]

theorem run_two_detectB' (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run nestVarMachine 2 ⟨(14, s), p, T⟩ = ⟨(16, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step nestVarMachine ⟨(14, s), p, T⟩ = ⟨(15, T.getD p false), p + 1, T⟩ := by
    simp only [step, nestVarMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, nestVarMachine, moveHead, h2', show p + 1 - 1 = p from by omega]

theorem run_four_true' :
    run nestVarMachine 4 ⟨(16, s), p, T⟩
      = ⟨(6, s), 0, writeAt (writeAt (writeAt (writeAt T p true) (p + 1) true)
          (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e16 : step nestVarMachine ⟨(16, s), p, T⟩ = ⟨(17, s), p + 1, writeAt T p true⟩ := by
    simp only [step, nestVarMachine, moveHead]; rfl
  have e17 : ∀ p' T', step nestVarMachine ⟨(17, s), p', T'⟩
      = ⟨(18, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, nestVarMachine, moveHead]; rfl
  have e18 : ∀ p' T', step nestVarMachine ⟨(18, s), p', T'⟩
      = ⟨(19, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, nestVarMachine, moveHead]; rfl
  have e19 : ∀ p' T', step nestVarMachine ⟨(19, s), p', T'⟩
      = ⟨(6, s), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, nestVarMachine, moveHead]; rfl
  rw [e16, e17, e18, e19]

theorem run_two_seekF' (h : T.getD p false = T.getD (p + 1) false) :
    run nestVarMachine 2 ⟨(20, s), p, T⟩ = ⟨(20, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step nestVarMachine ⟨(20, s), p, T⟩ = ⟨(21, T.getD p false), p + 1, T⟩ := by
    simp only [step, nestVarMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, nestVarMachine, moveHead, h2]

theorem run_two_detectF' (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run nestVarMachine 2 ⟨(20, s), p, T⟩ = ⟨(22, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step nestVarMachine ⟨(20, s), p, T⟩ = ⟨(21, T.getD p false), p + 1, T⟩ := by
    simp only [step, nestVarMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, nestVarMachine, moveHead, h2', show p + 1 - 1 = p from by omega]

theorem run_four_false' :
    run nestVarMachine 4 ⟨(22, s), p, T⟩
      = ⟨(26, s), 0, writeAt (writeAt (writeAt (writeAt T p false) (p + 1) false)
          (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e22 : step nestVarMachine ⟨(22, s), p, T⟩ = ⟨(23, s), p + 1, writeAt T p false⟩ := by
    simp only [step, nestVarMachine, moveHead]; rfl
  have e23 : ∀ p' T', step nestVarMachine ⟨(23, s), p', T'⟩
      = ⟨(24, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, nestVarMachine, moveHead]; rfl
  have e24 : ∀ p' T', step nestVarMachine ⟨(24, s), p', T'⟩
      = ⟨(25, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, nestVarMachine, moveHead]; rfl
  have e25 : ∀ p' T', step nestVarMachine ⟨(25, s), p', T'⟩
      = ⟨(26, s), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, nestVarMachine, moveHead]; rfl
  rw [e22, e23, e24, e25]

theorem run_two_skipWH (h1 : T.getD p false = true) :
    run nestVarMachine 2 ⟨(26, s), p, T⟩ = ⟨(26, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step nestVarMachine ⟨(26, s), p, T⟩ = ⟨(27, T.getD p false), p + 1, T⟩ := by
    simp only [step, nestVarMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, nestVarMachine, moveHead]; rfl

theorem run_two_crossWH (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run nestVarMachine 2 ⟨(26, s), p, T⟩ = ⟨(28, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step nestVarMachine ⟨(26, s), p, T⟩ = ⟨(27, T.getD p false), p + 1, T⟩ := by
    simp only [step, nestVarMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, nestVarMachine, moveHead, h2]

theorem run_two_skipPH (h1 : T.getD p false = true) :
    run nestVarMachine 2 ⟨(28, s), p, T⟩ = ⟨(28, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step nestVarMachine ⟨(28, s), p, T⟩ = ⟨(29, T.getD p false), p + 1, T⟩ := by
    simp only [step, nestVarMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, nestVarMachine, moveHead]; rfl

theorem run_two_crossPH (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run nestVarMachine 2 ⟨(28, s), p, T⟩ = ⟨(30, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step nestVarMachine ⟨(28, s), p, T⟩ = ⟨(29, T.getD p false), p + 1, T⟩ := by
    simp only [step, nestVarMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, nestVarMachine, moveHead, h2]

theorem run_two_healJ' (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run nestVarMachine 2 ⟨(30, s), p, T⟩ = ⟨(30, true), p + 2, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step nestVarMachine ⟨(30, s), p, T⟩ = ⟨(31, T.getD p false), p + 1, T⟩ := by
    simp only [step, nestVarMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, nestVarMachine, moveHead, h2]

theorem run_two_toIncr' (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run nestVarMachine 2 ⟨(30, s), p, T⟩ = ⟨(32, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step nestVarMachine ⟨(30, s), p, T⟩ = ⟨(31, T.getD p false), p + 1, T⟩ := by
    simp only [step, nestVarMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, nestVarMachine, moveHead, h2, show p + 1 - 1 = p from by omega]

theorem run_four_incr' :
    run nestVarMachine 4 ⟨(32, s), p, T⟩
      = ⟨(2, s), 0, writeAt (writeAt (writeAt (writeAt T p true) (p + 1) true)
          (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e32 : step nestVarMachine ⟨(32, s), p, T⟩ = ⟨(33, s), p + 1, writeAt T p true⟩ := by
    simp only [step, nestVarMachine, moveHead]; rfl
  have e33 : ∀ p' T', step nestVarMachine ⟨(33, s), p', T'⟩
      = ⟨(34, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, nestVarMachine, moveHead]; rfl
  have e34 : ∀ p' T', step nestVarMachine ⟨(34, s), p', T'⟩
      = ⟨(35, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, nestVarMachine, moveHead]; rfl
  have e35 : ∀ p' T', step nestVarMachine ⟨(35, s), p', T'⟩
      = ⟨(2, s), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, nestVarMachine, moveHead]; rfl
  rw [e32, e33, e34, e35]

theorem run_two_skipWN (h1 : T.getD p false = true) :
    run nestVarMachine 2 ⟨(36, s), p, T⟩ = ⟨(36, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step nestVarMachine ⟨(36, s), p, T⟩ = ⟨(37, T.getD p false), p + 1, T⟩ := by
    simp only [step, nestVarMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, nestVarMachine, moveHead]; rfl

theorem run_two_crossWN (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run nestVarMachine 2 ⟨(36, s), p, T⟩ = ⟨(38, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step nestVarMachine ⟨(36, s), p, T⟩ = ⟨(37, T.getD p false), p + 1, T⟩ := by
    simp only [step, nestVarMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, nestVarMachine, moveHead, h2]

theorem run_two_healP' (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run nestVarMachine 2 ⟨(38, s), p, T⟩ = ⟨(38, true), p + 2, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step nestVarMachine ⟨(38, s), p, T⟩ = ⟨(39, T.getD p false), p + 1, T⟩ := by
    simp only [step, nestVarMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, nestVarMachine, moveHead, h2]

theorem run_two_toZero' (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run nestVarMachine 2 ⟨(38, s), p, T⟩ = ⟨(40, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step nestVarMachine ⟨(38, s), p, T⟩ = ⟨(39, T.getD p false), p + 1, T⟩ := by
    simp only [step, nestVarMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, nestVarMachine, moveHead, h2]

theorem run_two_zeroHead' :
    run nestVarMachine 2 ⟨(40, s), p, T⟩
      = ⟨(42, s), p + 2, writeAt (writeAt T p false) (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e40 : step nestVarMachine ⟨(40, s), p, T⟩ = ⟨(41, s), p + 1, writeAt T p false⟩ := by
    simp only [step, nestVarMachine, moveHead]; rfl
  have e41 : ∀ p' T', step nestVarMachine ⟨(41, s), p', T'⟩
      = ⟨(42, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, nestVarMachine, moveHead]; rfl
  rw [e40, e41]

theorem run_four_zeroStep' (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run nestVarMachine 4 ⟨(42, s), p, T⟩
      = ⟨(42, true), p + 2, writeAt (writeAt T p false) (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e42 : step nestVarMachine ⟨(42, s), p, T⟩ = ⟨(43, T.getD p false), p + 1, T⟩ := by
    simp only [step, nestVarMachine, moveHead]; rfl
  rw [e42, h1]
  have h2' := h2
  rw [List.getD_eq_getElem?_getD] at h2'
  have e43 : step nestVarMachine ⟨(43, true), p + 1, T⟩ = ⟨(44, true), p, T⟩ := by
    simp [step, nestVarMachine, moveHead, h2', show p + 1 - 1 = p from by omega]
  rw [e43]
  have e44 : step nestVarMachine ⟨(44, true), p, T⟩
      = ⟨(45, true), p + 1, writeAt T p false⟩ := by
    simp only [step, nestVarMachine, moveHead]; rfl
  have e45 : ∀ T', step nestVarMachine ⟨(45, true), p + 1, T'⟩
      = ⟨(42, true), p + 2, writeAt T' (p + 1) false⟩ := by
    intro T'; simp only [step, nestVarMachine, moveHead]; rfl
  rw [e44, e45]

theorem run_four_zeroLast' (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run nestVarMachine 4 ⟨(42, s), p, T⟩
      = ⟨(0, false), 0, writeAt (writeAt T p false) (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e42 : step nestVarMachine ⟨(42, s), p, T⟩ = ⟨(43, T.getD p false), p + 1, T⟩ := by
    simp only [step, nestVarMachine, moveHead]; rfl
  rw [e42, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  have e43 : step nestVarMachine ⟨(43, false), p + 1, T⟩ = ⟨(46, false), p, T⟩ := by
    simp [step, nestVarMachine, moveHead, h2', show p + 1 - 1 = p from by omega]
  rw [e43]
  have e46 : step nestVarMachine ⟨(46, false), p, T⟩
      = ⟨(47, false), p + 1, writeAt T p false⟩ := by
    simp only [step, nestVarMachine, moveHead]; rfl
  have e47 : ∀ T', step nestVarMachine ⟨(47, false), p + 1, T'⟩
      = ⟨(0, false), 0, writeAt T' (p + 1) false⟩ := by
    intro T'; simp only [step, nestVarMachine, moveHead]; rfl
  rw [e46, e47]

theorem run_two_healB' (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run nestVarMachine 2 ⟨(48, s), p, T⟩ = ⟨(48, true), p + 2, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step nestVarMachine ⟨(48, s), p, T⟩ = ⟨(49, T.getD p false), p + 1, T⟩ := by
    simp only [step, nestVarMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, nestVarMachine, moveHead, h2]

theorem run_two_doneB' (h1 : T.getD p false = false) :
    run nestVarMachine 2 ⟨(48, s), p, T⟩ = ⟨(50, false), p + 1, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step nestVarMachine ⟨(48, s), p, T⟩ = ⟨(49, T.getD p false), p + 1, T⟩ := by
    simp only [step, nestVarMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, nestVarMachine, moveHead]; rfl

end Steps

/-- Two writes past two known-length prefixes. -/
theorem W2_append_right2 (A C X : List Bool) (qa qc p : ℕ) (b1 b2 : Bool)
    (ha : A.length = qa) (hc : C.length = qc) (hp : p + 1 < X.length) :
    writeAt (writeAt (A ++ (C ++ X)) (qa + (qc + p)) b1) (qa + (qc + p) + 1) b2
      = A ++ (C ++ writeAt (writeAt X p b1) (p + 1) b2) := by
  have hl1 : (writeAt X p b1).length = X.length := by
    rw [writeAt_of_lt b1 (by omega), List.length_set]
  rw [writeAt_append_right2 A C X qa qc p b1 ha hc (by omega),
    show qa + (qc + p) + 1 = qa + (qc + (p + 1)) from by omega,
    writeAt_append_right2 A C _ qa qc (p + 1) b2 ha hc (by omega)]

/-! ### Scan run-invariants -/

section Scans
variable (T : List Bool) (q k : ℕ) (s : Bool)

theorem run_skipBs2
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true ∧ T.getD (q + 2 * i + 1) false = false) :
    run nestVarMachine (2 * k) ⟨(0, s), q, T⟩
      = ⟨(0, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), run_two_skipB' hk.1 hk.2]
    rfl

theorem run_skipWIs (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run nestVarMachine (2 * k) ⟨(2, s), q, T⟩
      = ⟨(2, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), run_two_skipWI (h k (by omega))]
    rfl

theorem run_skipPs2
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true ∧ T.getD (q + 2 * i + 1) false = false) :
    run nestVarMachine (2 * k) ⟨(4, s), q, T⟩
      = ⟨(4, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), run_two_skipP' hk.1 hk.2]
    rfl

theorem run_skipWSs (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run nestVarMachine (2 * k) ⟨(6, s), q, T⟩
      = ⟨(6, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), run_two_skipWS (h k (by omega))]
    rfl

theorem run_skipPSs (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run nestVarMachine (2 * k) ⟨(8, s), q, T⟩
      = ⟨(8, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), run_two_skipPS (h k (by omega))]
    rfl

theorem run_skipJs2
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true ∧ T.getD (q + 2 * i + 1) false = false) :
    run nestVarMachine (2 * k) ⟨(10, s), q, T⟩
      = ⟨(10, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), run_two_skipJ' hk.1 hk.2]
    rfl

theorem run_seekAs2 (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run nestVarMachine (2 * k) ⟨(12, s), q, T⟩
      = ⟨(12, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), run_two_seekA' (h k (by omega))]
    rfl

theorem run_seekBs2 (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run nestVarMachine (2 * k) ⟨(14, s), q, T⟩
      = ⟨(14, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), run_two_seekB' (h k (by omega))]
    rfl

theorem run_seekFs2 (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run nestVarMachine (2 * k) ⟨(20, s), q, T⟩
      = ⟨(20, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), run_two_seekF' (h k (by omega))]
    rfl

theorem run_skipWHs (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run nestVarMachine (2 * k) ⟨(26, s), q, T⟩
      = ⟨(26, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), run_two_skipWH (h k (by omega))]
    rfl

theorem run_skipPHs (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run nestVarMachine (2 * k) ⟨(28, s), q, T⟩
      = ⟨(28, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), run_two_skipPH (h k (by omega))]
    rfl

theorem run_skipWNs (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run nestVarMachine (2 * k) ⟨(36, s), q, T⟩
      = ⟨(36, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), run_two_skipWN (h k (by omega))]
    rfl

end Scans

/-- The variable's heal invariant (evolving tape, past both bound regions). -/
theorem run_healJs2 (A C : List Bool) (B P k : ℕ) (E : List Bool)
    (ha : A.length = 2 * B + 2) (hc : C.length = 2 * P + 2) (hk : k ≤ P) (s : Bool)
    (i : ℕ) (hi : i ≤ k) :
    run nestVarMachine (2 * i) ⟨(30, s), 2 * B + 2 * P + 4, A ++ (C ++ (jhT P k 0 ++ E))⟩
      = ⟨(30, if i = 0 then s else true), 2 * B + 2 * P + 4 + 2 * i,
          A ++ (C ++ (jhT P k i ++ E))⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hlo : (A ++ (C ++ (jhT P k i ++ E))).getD (2 * B + 2 * P + 4 + 2 * i) false = true := by
      rw [show 2 * B + 2 * P + 4 + 2 * i = 2 * B + 2 + (2 * P + 2 + 2 * i) from by omega]
      exact liftJ2 A C _ ha hc (jhE_pair_lo P k i E (by omega))
    have hhi : (A ++ (C ++ (jhT P k i ++ E))).getD (2 * B + 2 * P + 4 + 2 * i + 1) false
        = false := by
      rw [show 2 * B + 2 * P + 4 + 2 * i + 1 = 2 * B + 2 + (2 * P + 2 + (2 * i + 1))
        from by omega]
      exact liftJ2 A C _ ha hc (jhE_pair_hi P k i E (by omega))
    have hw : writeAt (A ++ (C ++ (jhT P k i ++ E))) (2 * B + 2 * P + 4 + 2 * i + 1) true
        = A ++ (C ++ (jhT P k (i + 1) ++ E)) := by
      rw [show 2 * B + 2 * P + 4 + 2 * i + 1 = 2 * B + 2 + (2 * P + 2 + (2 * i + 1))
          from by omega,
        writeAt_append_right2 A C _ (2 * B + 2) (2 * P + 2) (2 * i + 1) true ha hc
          (by rw [List.length_append, jhT_length P k i (by omega) hk]; omega),
        jhT_heal P k i E (by omega) hk]
    rw [show 2 * (i + 1) = 2 * i + 2 from by ring, run_add, ih (by omega),
      run_two_healJ' hlo hhi, hw]
    rfl

/-- The inner bound's heal invariant (evolving tape, past the outer bound). -/
theorem run_healPs2 (A : List Bool) (B P : ℕ) (E : List Bool) (ha : A.length = 2 * B + 2)
    (s : Bool) (i : ℕ) (hi : i ≤ P) :
    run nestVarMachine (2 * i) ⟨(38, s), 2 * B + 2, A ++ (hlT P 0 ++ E)⟩
      = ⟨(38, if i = 0 then s else true), 2 * B + 2 + 2 * i, A ++ (hlT P i ++ E)⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hlo : (A ++ (hlT P i ++ E)).getD (2 * B + 2 + 2 * i) false = true :=
      liftJ A _ ha (hlE_pair_lo P i E (by omega))
    have hhi : (A ++ (hlT P i ++ E)).getD (2 * B + 2 + 2 * i + 1) false = false := by
      rw [show 2 * B + 2 + 2 * i + 1 = 2 * B + 2 + (2 * i + 1) from by omega]
      exact liftJ A _ ha (hlE_pair_hi P i E (by omega))
    have hw : writeAt (A ++ (hlT P i ++ E)) (2 * B + 2 + 2 * i + 1) true
        = A ++ (hlT P (i + 1) ++ E) := by
      rw [show 2 * B + 2 + 2 * i + 1 = 2 * B + 2 + (2 * i + 1) from by omega,
        writeAt_append_right A _ (2 * B + 2) (2 * i + 1) true ha
          (by rw [List.length_append, hlT_length P i (by omega)]; omega),
        hlT_heal P i E (by omega)]
    rw [show 2 * (i + 1) = 2 * i + 2 from by ring, run_add, ih (by omega),
      run_two_healP' hlo hhi, hw]
    rfl

/-- The zeroing-walk invariant (evolving tape, past both bound regions). -/
theorem run_zeros2 (A C : List Bool) (B P : ℕ) (E : List Bool)
    (ha : A.length = 2 * B + 2) (hc : C.length = 2 * P + 2) (hP : 0 < P) (s : Bool)
    (m : ℕ) (hm : m ≤ P - 1) :
    run nestVarMachine (4 * m) ⟨(42, s), 2 * B + 2 * P + 6, A ++ (C ++ (zeroT P 0 ++ E))⟩
      = ⟨(42, if m = 0 then s else true), 2 * B + 2 * P + 6 + 2 * m,
          A ++ (C ++ (zeroT P m ++ E))⟩ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hlo : (A ++ (C ++ (zeroT P m ++ E))).getD (2 * B + 2 * P + 6 + 2 * m) false
        = true := by
      rw [show 2 * B + 2 * P + 6 + 2 * m = 2 * B + 2 + (2 * P + 2 + 2 * (m + 1)) from by omega]
      exact liftJ2 A C _ ha hc (zeroE_data_lo P m E (by omega))
    have hhi : (A ++ (C ++ (zeroT P m ++ E))).getD (2 * B + 2 * P + 6 + 2 * m + 1) false
        = true := by
      rw [show 2 * B + 2 * P + 6 + 2 * m + 1 = 2 * B + 2 + (2 * P + 2 + (2 * (m + 1) + 1))
        from by omega]
      exact liftJ2 A C _ ha hc (zeroE_data_hi P m E (by omega))
    have hw : writeAt (writeAt (A ++ (C ++ (zeroT P m ++ E)))
          (2 * B + 2 * P + 6 + 2 * m) false) (2 * B + 2 * P + 6 + 2 * m + 1) false
        = A ++ (C ++ (zeroT P (m + 1) ++ E)) := by
      rw [show 2 * B + 2 * P + 6 + 2 * m = 2 * B + 2 + (2 * P + 2 + 2 * (m + 1)) from by omega,
        W2_append_right2 A C _ (2 * B + 2) (2 * P + 2) (2 * (m + 1)) false false ha hc
          (by rw [List.length_append, zeroT_length P m (by omega) hP]; omega),
        zeroT_step P m E (by omega)]
    rw [show 4 * (m + 1) = 4 * m + 4 from by ring, run_add, ih (by omega),
      run_four_zeroStep' hlo hhi, hw]
    rfl

/-- The outer bound's restore invariant. -/
theorem run_healBs2 (v : ℕ) (E : List Bool) (s : Bool) (i : ℕ) (hi : i ≤ v) :
    run nestVarMachine (2 * i) ⟨(48, s), 0, hlT v 0 ++ E⟩
      = ⟨(48, if i = 0 then s else true), 2 * i, hlT v i ++ E⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [show 2 * (i + 1) = 2 * i + 2 from by ring, run_add, ih (by omega),
      run_two_healB' (hlE_pair_lo v i E (by omega)) (hlE_pair_hi v i E (by omega)),
      hlT_heal v i E (by omega)]
    rfl

/-! ## The splice sub-round -/

/-- **One splice sub-round**: skip both bounds, mark the variable's pair `j'`, seek to the output
terminator, splice one doubled `true`, reset. -/
theorem run_nv_subround (B P a c i j' : ℕ) (OUT : List Bool) (ha : a ≤ B) (hc : c ≤ P)
    (hiP : i ≤ P) (hj : j' < i) (s : Bool) :
    run nestVarMachine (2 * B + 4 * P + 2 * (OUT.length + j') + 12)
      ⟨(6, s), 0, cntT B a ++ (cntT P c ++ (jsT P i j' ++ encodeD (OUT ++ List.replicate j' true)))⟩
      = ⟨(6, false), 0, cntT B a ++ (cntT P c
          ++ (jsT P i (j' + 1) ++ encodeD (OUT ++ List.replicate (j' + 1) true)))⟩ := by
  have hcb := cntT_length B a ha
  have hcc := cntT_length P c hc
  -- skip the outer bound
  have w1 := run_skipWSs (cntT B a ++ (cntT P c ++ (jsT P i j'
      ++ encodeD (OUT ++ List.replicate j' true)))) 0 B s
    (fun i' hi' => by simpa using cntE_lo B a _ i' ha hi')
  simp only [Nat.zero_add] at w1
  have w2 := run_two_crossWS (s := if B = 0 then s else true) (p := 2 * B)
    (T := cntT B a ++ (cntT P c ++ (jsT P i j' ++ encodeD (OUT ++ List.replicate j' true))))
    (cntE_cm_lo B a _ ha) (cntE_cm_hi B a _ ha)
  -- skip the inner bound
  have w3 := run_skipPSs (cntT B a ++ (cntT P c ++ (jsT P i j'
      ++ encodeD (OUT ++ List.replicate j' true)))) (2 * B + 2) P false
    (fun i' hi' => liftJ _ _ hcb (cntE_lo P c _ i' hc hi'))
  have w4 := run_two_crossPS (s := if P = 0 then false else true) (p := 2 * B + 2 + 2 * P)
    (T := cntT B a ++ (cntT P c ++ (jsT P i j' ++ encodeD (OUT ++ List.replicate j' true))))
    (liftJ _ _ hcb (cntE_cm_lo P c _ hc))
    (by rw [show 2 * B + 2 + 2 * P + 1 = 2 * B + 2 + (2 * P + 1) from by omega]
        exact liftJ _ _ hcb (cntE_cm_hi P c _ hc))
  rw [show 2 * B + 2 + 2 * P + 2 = 2 * B + 2 * P + 4 from by omega] at w4
  -- find and mark the variable's pair `j'`
  have w5 := run_skipJs2 (cntT B a ++ (cntT P c ++ (jsT P i j'
      ++ encodeD (OUT ++ List.replicate j' true)))) (2 * B + 2 * P + 4) j' false
    (fun i' hi' => ⟨by
        rw [show 2 * B + 2 * P + 4 + 2 * i' = 2 * B + 2 + (2 * P + 2 + 2 * i') from by omega]
        exact liftJ2 _ _ _ hcb hcc (jsE_mark_lo P i j' _ i' hi'), by
        rw [show 2 * B + 2 * P + 4 + 2 * i' + 1 = 2 * B + 2 + (2 * P + 2 + (2 * i' + 1))
          from by omega]
        exact liftJ2 _ _ _ hcb hcc (jsE_mark_hi P i j' _ i' hi')⟩)
  have w6 := run_two_markJ' (s := if j' = 0 then false else true)
    (p := 2 * B + 2 * P + 4 + 2 * j')
    (T := cntT B a ++ (cntT P c ++ (jsT P i j' ++ encodeD (OUT ++ List.replicate j' true))))
    (by rw [show 2 * B + 2 * P + 4 + 2 * j' = 2 * B + 2 + (2 * P + 2 + 2 * j') from by omega]
        exact liftJ2 _ _ _ hcb hcc (jsE_data P i j' _ (2 * j') (by omega) (by omega) (by omega)))
    (by rw [show 2 * B + 2 * P + 4 + 2 * j' + 1 = 2 * B + 2 + (2 * P + 2 + (2 * j' + 1))
        from by omega]
        exact liftJ2 _ _ _ hcb hcc
          (jsE_data P i j' _ (2 * j' + 1) (by omega) (by omega) (by omega)))
  have hw6 : writeAt (cntT B a ++ (cntT P c ++ (jsT P i j'
        ++ encodeD (OUT ++ List.replicate j' true)))) (2 * B + 2 * P + 4 + 2 * j' + 1) false
      = cntT B a ++ (cntT P c ++ (jsT P i (j' + 1)
          ++ encodeD (OUT ++ List.replicate j' true))) := by
    rw [show 2 * B + 2 * P + 4 + 2 * j' + 1 = 2 * B + 2 + (2 * P + 2 + (2 * j' + 1))
        from by omega,
      writeAt_append_right2 _ _ _ (2 * B + 2) (2 * P + 2) (2 * j' + 1) false hcb hcc
        (by rw [List.length_append, jsT_length P i j' (by omega) hiP]; omega),
      jsT_mark P i j' _ (by omega) hiP]
  rw [hw6] at w6
  -- seek across the variable's rest and boundary
  have w7 := run_seekAs2 (cntT B a ++ (cntT P c ++ (jsT P i (j' + 1)
      ++ encodeD (OUT ++ List.replicate j' true)))) (2 * B + 2 * P + 4 + 2 * j' + 2)
    (i - j' - 1) true (fun i' hi' => by
      have e1 : (cntT B a ++ (cntT P c ++ (jsT P i (j' + 1)
          ++ encodeD (OUT ++ List.replicate j' true)))).getD
          (2 * B + 2 * P + 4 + 2 * j' + 2 + 2 * i') false = true := by
        rw [show 2 * B + 2 * P + 4 + 2 * j' + 2 + 2 * i'
            = 2 * B + 2 + (2 * P + 2 + (2 * j' + 2 + 2 * i')) from by omega]
        exact liftJ2 _ _ _ hcb hcc (jsE_data P i (j' + 1) _ (2 * j' + 2 + 2 * i')
          (by omega) (by omega) (by omega))
      have e2 : (cntT B a ++ (cntT P c ++ (jsT P i (j' + 1)
          ++ encodeD (OUT ++ List.replicate j' true)))).getD
          (2 * B + 2 * P + 4 + 2 * j' + 2 + 2 * i' + 1) false = true := by
        rw [show 2 * B + 2 * P + 4 + 2 * j' + 2 + 2 * i' + 1
            = 2 * B + 2 + (2 * P + 2 + (2 * j' + 2 + 2 * i' + 1)) from by omega]
        exact liftJ2 _ _ _ hcb hcc (jsE_data P i (j' + 1) _ (2 * j' + 2 + 2 * i' + 1)
          (by omega) (by omega) (by omega))
      rw [e1, e2])
  rw [show 2 * B + 2 * P + 4 + 2 * j' + 2 + 2 * (i - j' - 1) = 2 * B + 2 * P + 4 + 2 * i
    from by omega] at w7
  have w8 := run_two_crossA'
    (s := storedD (cntT B a ++ (cntT P c ++ (jsT P i (j' + 1)
      ++ encodeD (OUT ++ List.replicate j' true)))) (2 * B + 2 * P + 4 + 2 * j' + 2) true
      (i - j' - 1))
    (p := 2 * B + 2 * P + 4 + 2 * i)
    (T := cntT B a ++ (cntT P c ++ (jsT P i (j' + 1)
      ++ encodeD (OUT ++ List.replicate j' true))))
    (by rw [show 2 * B + 2 * P + 4 + 2 * i = 2 * B + 2 + (2 * P + 2 + 2 * i) from by omega]
        exact liftJ2 _ _ _ hcb hcc (jsE_m_lo P i (j' + 1) _ (by omega)))
    (by rw [show 2 * B + 2 * P + 4 + 2 * i + 1 = 2 * B + 2 + (2 * P + 2 + (2 * i + 1))
        from by omega]
        exact liftJ2 _ _ _ hcb hcc (jsE_m_hi P i (j' + 1) _ (by omega)))
  -- seek the padding, then the output
  have w9 := run_seekBs2 (cntT B a ++ (cntT P c ++ (jsT P i (j' + 1)
      ++ encodeD (OUT ++ List.replicate j' true)))) (2 * B + 2 * P + 4 + 2 * i + 2)
    (P - i) false (fun i' hi' => by
      have e1 : (cntT B a ++ (cntT P c ++ (jsT P i (j' + 1)
          ++ encodeD (OUT ++ List.replicate j' true)))).getD
          (2 * B + 2 * P + 4 + 2 * i + 2 + 2 * i') false = false := by
        rw [show 2 * B + 2 * P + 4 + 2 * i + 2 + 2 * i'
            = 2 * B + 2 + (2 * P + 2 + (2 * i + 2 + 2 * i')) from by omega]
        exact liftJ2 _ _ _ hcb hcc (jsE_pad P i (j' + 1) _ (2 * i + 2 + 2 * i')
          (by omega) hiP (by omega) (by omega))
      have e2 : (cntT B a ++ (cntT P c ++ (jsT P i (j' + 1)
          ++ encodeD (OUT ++ List.replicate j' true)))).getD
          (2 * B + 2 * P + 4 + 2 * i + 2 + 2 * i' + 1) false = false := by
        rw [show 2 * B + 2 * P + 4 + 2 * i + 2 + 2 * i' + 1
            = 2 * B + 2 + (2 * P + 2 + (2 * i + 2 + 2 * i' + 1)) from by omega]
        exact liftJ2 _ _ _ hcb hcc (jsE_pad P i (j' + 1) _ (2 * i + 2 + 2 * i' + 1)
          (by omega) hiP (by omega) (by omega))
      rw [e1, e2])
  rw [show 2 * B + 2 * P + 4 + 2 * i + 2 + 2 * (P - i) = 2 * B + 4 * P + 6 from by omega] at w9
  have hq3 : (cntT B a).length + (cntT P c).length + (jsT P i (j' + 1)).length
      = 2 * B + 4 * P + 6 := by
    rw [hcb, hcc, jsT_length P i (j' + 1) (by omega) hiP]; omega
  have w10 := run_seekBs2 (cntT B a ++ (cntT P c ++ (jsT P i (j' + 1)
      ++ encodeD (OUT ++ List.replicate j' true)))) (2 * B + 4 * P + 6)
    (OUT.length + j')
    (storedD (cntT B a ++ (cntT P c ++ (jsT P i (j' + 1)
      ++ encodeD (OUT ++ List.replicate j' true)))) (2 * B + 2 * P + 4 + 2 * i + 2) false
      (P - i))
    (fun i' hi' => preD3_data_eq (cntT B a) (cntT P c) (jsT P i (j' + 1))
      (OUT ++ List.replicate j' true) (2 * B + 4 * P + 6) i' hq3
      (by rw [List.length_append, List.length_replicate]; omega))
  -- detect and splice
  have hm1 := preD3_mark_lo (cntT B a) (cntT P c) (jsT P i (j' + 1))
    (OUT ++ List.replicate j' true) (2 * B + 4 * P + 6) hq3
  have hm2 := preD3_mark_hi (cntT B a) (cntT P c) (jsT P i (j' + 1))
    (OUT ++ List.replicate j' true) (2 * B + 4 * P + 6) hq3
  rw [show (OUT ++ List.replicate j' true).length = OUT.length + j' from by
    rw [List.length_append, List.length_replicate]] at hm1 hm2
  have w11 := run_two_detectB'
    (s := storedD (cntT B a ++ (cntT P c ++ (jsT P i (j' + 1)
      ++ encodeD (OUT ++ List.replicate j' true)))) (2 * B + 4 * P + 6)
      (storedD (cntT B a ++ (cntT P c ++ (jsT P i (j' + 1)
        ++ encodeD (OUT ++ List.replicate j' true)))) (2 * B + 2 * P + 4 + 2 * i + 2) false
        (P - i)) (OUT.length + j'))
    (p := 2 * B + 4 * P + 6 + 2 * (OUT.length + j')) hm1 hm2
  have hsn := writes_snoc3 (cntT B a) (cntT P c) (jsT P i (j' + 1))
    (OUT ++ List.replicate j' true) (2 * B + 4 * P + 6) hq3 true
  rw [show (OUT ++ List.replicate j' true).length = OUT.length + j' from by
      rw [List.length_append, List.length_replicate],
    List.append_assoc, ← List.replicate_succ'] at hsn
  have w12 := run_four_true' (s := false) (p := 2 * B + 4 * P + 6 + 2 * (OUT.length + j'))
    (T := cntT B a ++ (cntT P c ++ (jsT P i (j' + 1)
      ++ encodeD (OUT ++ List.replicate j' true))))
  rw [hsn] at w12
  -- assemble
  rw [show 2 * B + 4 * P + 2 * (OUT.length + j') + 12
      = 2 * B + (2 + (2 * P + (2 + (2 * j' + (2 + (2 * (i - j' - 1) + (2 + (2 * (P - i)
          + (2 * (OUT.length + j') + (2 + 4)))))))))) from by omega,
    run_add, w1, run_add, w2, run_add, w3, run_add, w4, run_add, w5, run_add, w6,
    run_add, w7, run_add, w8, run_add, w9, run_add, w10, run_add, w11, w12]

/-! ## The inner round and its induction -/

/-- Cumulative clock of the first `j'` splice sub-rounds. -/
def nvSubs (B P L : ℕ) : ℕ → ℕ
  | 0 => 0
  | j' + 1 => nvSubs B P L j' + (2 * B + 4 * P + 2 * (L + j') + 12)

theorem run_nv_subrounds (B P a c i : ℕ) (OUT : List Bool) (ha : a ≤ B) (hc : c ≤ P)
    (hiP : i ≤ P) (s : Bool) (j'' : ℕ) (hj : j'' ≤ i) :
    run nestVarMachine (nvSubs B P OUT.length j'')
      ⟨(6, s), 0, cntT B a ++ (cntT P c ++ (jsT P i 0 ++ encodeD OUT))⟩
      = ⟨(6, if j'' = 0 then s else false), 0, cntT B a ++ (cntT P c
          ++ (jsT P i j'' ++ encodeD (OUT ++ List.replicate j'' true)))⟩ := by
  induction j'' with
  | zero =>
    simp
    rfl
  | succ j'' ih =>
    rw [show nvSubs B P OUT.length (j'' + 1)
        = nvSubs B P OUT.length j'' + (2 * B + 4 * P + 2 * (OUT.length + j'') + 12) from rfl,
      run_add, ih (by omega),
      run_nv_subround B P a c i j'' OUT ha hc hiP (by omega), if_neg (by omega)]

/-- The inner round's clock. -/
def nvInner (B P L i : ℕ) : ℕ := nvSubs B P L i + 6 * B + 6 * P + 2 * L + 6 * i + 26

/-- **One inner round**: mark the inner bound's pair `i`, splice the variable (value `i`), emit the closing
`false`, heal the variable, increment it in place. -/
theorem run_nv_inner (B P a i : ℕ) (OUT : List Bool) (ha : a ≤ B) (hiP : i < P) (s : Bool) :
    run nestVarMachine (nvInner B P OUT.length i)
      ⟨(2, s), 0, cntT B a ++ (cntT P i ++ (jT P i ++ encodeD OUT))⟩
      = ⟨(2, false), 0, cntT B a ++ (cntT P (i + 1)
          ++ (jT P (i + 1) ++ encodeD (OUT ++ encodeNat i)))⟩ := by
  have hcb := cntT_length B a ha
  have hcc := cntT_length P (i + 1) (by omega : i + 1 ≤ P)
  -- reach and mark the inner bound's pair `i`
  have r1 := run_skipWIs (cntT B a ++ (cntT P i ++ (jT P i ++ encodeD OUT))) 0 B s
    (fun i' hi' => by simpa using cntE_lo B a _ i' ha hi')
  simp only [Nat.zero_add] at r1
  have r2 := run_two_crossWI (s := if B = 0 then s else true) (p := 2 * B)
    (T := cntT B a ++ (cntT P i ++ (jT P i ++ encodeD OUT)))
    (cntE_cm_lo B a _ ha) (cntE_cm_hi B a _ ha)
  have r3 := run_skipPs2 (cntT B a ++ (cntT P i ++ (jT P i ++ encodeD OUT))) (2 * B + 2) i
    false (fun i' hi' => ⟨liftJ _ _ hcb (cntE_mark_lo P i _ i' hi'), by
      rw [show 2 * B + 2 + 2 * i' + 1 = 2 * B + 2 + (2 * i' + 1) from by omega]
      exact liftJ _ _ hcb (cntE_mark_hi P i _ i' hi')⟩)
  have r4 := run_two_markP' (s := if i = 0 then false else true) (p := 2 * B + 2 + 2 * i)
    (T := cntT B a ++ (cntT P i ++ (jT P i ++ encodeD OUT)))
    (liftJ _ _ hcb (cntE_data P i _ (2 * i) (by omega) (by omega) (by omega)))
    (by rw [show 2 * B + 2 + 2 * i + 1 = 2 * B + 2 + (2 * i + 1) from by omega]
        exact liftJ _ _ hcb (cntE_data P i _ (2 * i + 1) (by omega) (by omega) (by omega)))
  have hw4 : writeAt (cntT B a ++ (cntT P i ++ (jT P i ++ encodeD OUT)))
      (2 * B + 2 + 2 * i + 1) false
      = cntT B a ++ (cntT P (i + 1) ++ (jT P i ++ encodeD OUT)) := by
    rw [show 2 * B + 2 + 2 * i + 1 = 2 * B + 2 + (2 * i + 1) from by omega,
      writeAt_append_right _ _ (2 * B + 2) (2 * i + 1) false hcb
        (by rw [List.length_append, cntT_length P i (by omega)]; omega),
      cntT_mark P i _ hiP]
  rw [hw4] at r4
  -- the splice sub-rounds
  have r5 := run_nv_subrounds B P a (i + 1) i OUT ha (by omega) (by omega) true i (le_refl i)
  rw [jsT_zero] at r5
  -- the closing `false`
  have r6 := run_skipWSs (cntT B a ++ (cntT P (i + 1) ++ (jsT P i i
      ++ encodeD (OUT ++ List.replicate i true)))) 0 B (if i = 0 then true else false)
    (fun i' hi' => by simpa using cntE_lo B a _ i' ha hi')
  simp only [Nat.zero_add] at r6
  have r7 := run_two_crossWS
    (s := if B = 0 then (if i = 0 then true else false) else true) (p := 2 * B)
    (T := cntT B a ++ (cntT P (i + 1) ++ (jsT P i i
      ++ encodeD (OUT ++ List.replicate i true))))
    (cntE_cm_lo B a _ ha) (cntE_cm_hi B a _ ha)
  have r8 := run_skipPSs (cntT B a ++ (cntT P (i + 1) ++ (jsT P i i
      ++ encodeD (OUT ++ List.replicate i true)))) (2 * B + 2) P false
    (fun i' hi' => liftJ _ _ hcb (cntE_lo P (i + 1) _ i' (by omega) hi'))
  have r9 := run_two_crossPS (s := if P = 0 then false else true) (p := 2 * B + 2 + 2 * P)
    (T := cntT B a ++ (cntT P (i + 1) ++ (jsT P i i
      ++ encodeD (OUT ++ List.replicate i true))))
    (liftJ _ _ hcb (cntE_cm_lo P (i + 1) _ (by omega)))
    (by rw [show 2 * B + 2 + 2 * P + 1 = 2 * B + 2 + (2 * P + 1) from by omega]
        exact liftJ _ _ hcb (cntE_cm_hi P (i + 1) _ (by omega)))
  rw [show 2 * B + 2 + 2 * P + 2 = 2 * B + 2 * P + 4 from by omega] at r9
  have r10 := run_skipJs2 (cntT B a ++ (cntT P (i + 1) ++ (jsT P i i
      ++ encodeD (OUT ++ List.replicate i true)))) (2 * B + 2 * P + 4) i false
    (fun i' hi' => ⟨by
        rw [show 2 * B + 2 * P + 4 + 2 * i' = 2 * B + 2 + (2 * P + 2 + 2 * i') from by omega]
        exact liftJ2 _ _ _ hcb hcc (jsE_mark_lo P i i _ i' hi'), by
        rw [show 2 * B + 2 * P + 4 + 2 * i' + 1 = 2 * B + 2 + (2 * P + 2 + (2 * i' + 1))
          from by omega]
        exact liftJ2 _ _ _ hcb hcc (jsE_mark_hi P i i _ i' hi')⟩)
  have r11 := run_two_doneJ' (s := if i = 0 then false else true)
    (p := 2 * B + 2 * P + 4 + 2 * i)
    (T := cntT B a ++ (cntT P (i + 1) ++ (jsT P i i
      ++ encodeD (OUT ++ List.replicate i true))))
    (by rw [show 2 * B + 2 * P + 4 + 2 * i = 2 * B + 2 + (2 * P + 2 + 2 * i) from by omega]
        exact liftJ2 _ _ _ hcb hcc (jsE_m_lo P i i _ (le_refl i)))
    (by rw [show 2 * B + 2 * P + 4 + 2 * i + 1 = 2 * B + 2 + (2 * P + 2 + (2 * i + 1))
        from by omega]
        exact liftJ2 _ _ _ hcb hcc (jsE_m_hi P i i _ (le_refl i)))
  have r12 := run_seekFs2 (cntT B a ++ (cntT P (i + 1) ++ (jsT P i i
      ++ encodeD (OUT ++ List.replicate i true)))) (2 * B + 2 * P + 4 + 2 * i + 2)
    (P - i) false (fun i' hi' => by
      have e1 : (cntT B a ++ (cntT P (i + 1) ++ (jsT P i i
          ++ encodeD (OUT ++ List.replicate i true)))).getD
          (2 * B + 2 * P + 4 + 2 * i + 2 + 2 * i') false = false := by
        rw [show 2 * B + 2 * P + 4 + 2 * i + 2 + 2 * i'
            = 2 * B + 2 + (2 * P + 2 + (2 * i + 2 + 2 * i')) from by omega]
        exact liftJ2 _ _ _ hcb hcc (jsE_pad P i i _ (2 * i + 2 + 2 * i')
          (le_refl i) (by omega) (by omega) (by omega))
      have e2 : (cntT B a ++ (cntT P (i + 1) ++ (jsT P i i
          ++ encodeD (OUT ++ List.replicate i true)))).getD
          (2 * B + 2 * P + 4 + 2 * i + 2 + 2 * i' + 1) false = false := by
        rw [show 2 * B + 2 * P + 4 + 2 * i + 2 + 2 * i' + 1
            = 2 * B + 2 + (2 * P + 2 + (2 * i + 2 + 2 * i' + 1)) from by omega]
        exact liftJ2 _ _ _ hcb hcc (jsE_pad P i i _ (2 * i + 2 + 2 * i' + 1)
          (le_refl i) (by omega) (by omega) (by omega))
      rw [e1, e2])
  rw [show 2 * B + 2 * P + 4 + 2 * i + 2 + 2 * (P - i) = 2 * B + 4 * P + 6 from by omega] at r12
  have hq3 : (cntT B a).length + (cntT P (i + 1)).length + (jsT P i i).length
      = 2 * B + 4 * P + 6 := by
    rw [hcb, hcc, jsT_length P i i (le_refl i) (by omega)]; omega
  have r13 := run_seekFs2 (cntT B a ++ (cntT P (i + 1) ++ (jsT P i i
      ++ encodeD (OUT ++ List.replicate i true)))) (2 * B + 4 * P + 6)
    (OUT.length + i)
    (storedD (cntT B a ++ (cntT P (i + 1) ++ (jsT P i i
      ++ encodeD (OUT ++ List.replicate i true)))) (2 * B + 2 * P + 4 + 2 * i + 2) false
      (P - i))
    (fun i' hi' => preD3_data_eq (cntT B a) (cntT P (i + 1)) (jsT P i i)
      (OUT ++ List.replicate i true) (2 * B + 4 * P + 6) i' hq3
      (by rw [List.length_append, List.length_replicate]; omega))
  have hm1 := preD3_mark_lo (cntT B a) (cntT P (i + 1)) (jsT P i i)
    (OUT ++ List.replicate i true) (2 * B + 4 * P + 6) hq3
  have hm2 := preD3_mark_hi (cntT B a) (cntT P (i + 1)) (jsT P i i)
    (OUT ++ List.replicate i true) (2 * B + 4 * P + 6) hq3
  rw [show (OUT ++ List.replicate i true).length = OUT.length + i from by
    rw [List.length_append, List.length_replicate]] at hm1 hm2
  have r14 := run_two_detectF'
    (s := storedD (cntT B a ++ (cntT P (i + 1) ++ (jsT P i i
      ++ encodeD (OUT ++ List.replicate i true)))) (2 * B + 4 * P + 6)
      (storedD (cntT B a ++ (cntT P (i + 1) ++ (jsT P i i
        ++ encodeD (OUT ++ List.replicate i true)))) (2 * B + 2 * P + 4 + 2 * i + 2) false
        (P - i)) (OUT.length + i))
    (p := 2 * B + 4 * P + 6 + 2 * (OUT.length + i)) hm1 hm2
  have hsn := writes_snoc3 (cntT B a) (cntT P (i + 1)) (jsT P i i)
    (OUT ++ List.replicate i true) (2 * B + 4 * P + 6) hq3 false
  rw [show (OUT ++ List.replicate i true).length = OUT.length + i from by
      rw [List.length_append, List.length_replicate],
    show (OUT ++ List.replicate i true) ++ [false] = OUT ++ encodeNat i from by
      rw [List.append_assoc]; rfl] at hsn
  have r15 := run_four_false' (s := false) (p := 2 * B + 4 * P + 6 + 2 * (OUT.length + i))
    (T := cntT B a ++ (cntT P (i + 1) ++ (jsT P i i
      ++ encodeD (OUT ++ List.replicate i true))))
  rw [hsn] at r15
  -- heal the variable and increment it in place
  have r16 := run_skipWHs (cntT B a ++ (cntT P (i + 1) ++ (jsT P i i
      ++ encodeD (OUT ++ encodeNat i)))) 0 B false
    (fun i' hi' => by simpa using cntE_lo B a _ i' ha hi')
  simp only [Nat.zero_add] at r16
  have r17 := run_two_crossWH (s := if B = 0 then false else true) (p := 2 * B)
    (T := cntT B a ++ (cntT P (i + 1) ++ (jsT P i i ++ encodeD (OUT ++ encodeNat i))))
    (cntE_cm_lo B a _ ha) (cntE_cm_hi B a _ ha)
  have r18 := run_skipPHs (cntT B a ++ (cntT P (i + 1) ++ (jsT P i i
      ++ encodeD (OUT ++ encodeNat i)))) (2 * B + 2) P false
    (fun i' hi' => liftJ _ _ hcb (cntE_lo P (i + 1) _ i' (by omega) hi'))
  have r19 := run_two_crossPH (s := if P = 0 then false else true) (p := 2 * B + 2 + 2 * P)
    (T := cntT B a ++ (cntT P (i + 1) ++ (jsT P i i ++ encodeD (OUT ++ encodeNat i))))
    (liftJ _ _ hcb (cntE_cm_lo P (i + 1) _ (by omega)))
    (by rw [show 2 * B + 2 + 2 * P + 1 = 2 * B + 2 + (2 * P + 1) from by omega]
        exact liftJ _ _ hcb (cntE_cm_hi P (i + 1) _ (by omega)))
  rw [show 2 * B + 2 + 2 * P + 2 = 2 * B + 2 * P + 4 from by omega] at r19
  have r20 := run_healJs2 (cntT B a) (cntT P (i + 1)) B P i
    (encodeD (OUT ++ encodeNat i)) hcb hcc (by omega) false i (le_refl i)
  rw [jhT_zero] at r20
  have r21 := run_two_toIncr' (s := if i = 0 then false else true)
    (p := 2 * B + 2 * P + 4 + 2 * i)
    (T := cntT B a ++ (cntT P (i + 1) ++ (jhT P i i ++ encodeD (OUT ++ encodeNat i))))
    (by rw [show 2 * B + 2 * P + 4 + 2 * i = 2 * B + 2 + (2 * P + 2 + 2 * i) from by omega]
        exact liftJ2 _ _ _ hcb hcc (jhE_m_lo P i _))
    (by rw [show 2 * B + 2 * P + 4 + 2 * i + 1 = 2 * B + 2 + (2 * P + 2 + (2 * i + 1))
        from by omega]
        exact liftJ2 _ _ _ hcb hcc (jhE_m_hi P i _))
  have r22 := run_four_incr' (s := false) (p := 2 * B + 2 * P + 4 + 2 * i)
    (T := cntT B a ++ (cntT P (i + 1) ++ (jhT P i i ++ encodeD (OUT ++ encodeNat i))))
  have hw22 : writeAt (writeAt (writeAt (writeAt (cntT B a ++ (cntT P (i + 1)
        ++ (jhT P i i ++ encodeD (OUT ++ encodeNat i)))) (2 * B + 2 * P + 4 + 2 * i) true)
        (2 * B + 2 * P + 4 + 2 * i + 1) true) (2 * B + 2 * P + 4 + 2 * i + 2) false)
        (2 * B + 2 * P + 4 + 2 * i + 3) true
      = cntT B a ++ (cntT P (i + 1) ++ (jT P (i + 1) ++ encodeD (OUT ++ encodeNat i))) := by
    rw [jhT_last,
      show 2 * B + 2 * P + 4 + 2 * i = 2 * B + 2 + (2 * P + 2 + 2 * i) from by omega,
      W4_append_right (cntT B a) _ (2 * B + 2) (2 * P + 2 + 2 * i) true true false true hcb
        (by simp only [List.length_append, cntT_length P (i + 1) (by omega : i + 1 ≤ P),
              jT_length P i (by omega : i ≤ P)]
            omega),
      W4_append_right (cntT P (i + 1)) _ (2 * P + 2) (2 * i) true true false true hcc
        (by rw [List.length_append, jT_length P i (by omega)]; omega),
      jT_incr P i _ hiP]
  rw [hw22] at r22
  -- assemble
  rw [show nvInner B P OUT.length i
      = 2 * B + (2 + (2 * i + (2 + (nvSubs B P OUT.length i + (2 * B + (2 + (2 * P + (2 + (2 * i + (2 + (2 * (P - i) + (2 * (OUT.length + i) + (2 + (4 + (2 * B + (2 + (2 * P + (2 + (2 * i + (2 + (4)))))))))))))))))))))
      from by rw [nvInner]; omega,
    run_add, r1, run_add, r2, run_add, r3, run_add, r4, run_add, r5, run_add, r6,
    run_add, r7, run_add, r8, run_add, r9, run_add, r10, run_add, r11, run_add, r12,
    run_add, r13, run_add, r14, run_add, r15, run_add, r16, run_add, r17, run_add, r18,
    run_add, r19, run_add, r20, run_add, r21, r22]

/-! ## The rounds, the finale, and the top theorem -/

/-- Cumulative clock of the first `i` inner rounds. -/
def nvInners (B P L : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => nvInners B P L i + nvInner B P (L + rangeLen i) i

theorem run_nv_inners (B P a : ℕ) (OUT : List Bool) (ha : a ≤ B) (s : Bool)
    (i'' : ℕ) (hi : i'' ≤ P) :
    run nestVarMachine (nvInners B P OUT.length i'')
      ⟨(2, s), 0, cntT B a ++ (cntT P 0 ++ (jT P 0 ++ encodeD OUT))⟩
      = ⟨(2, if i'' = 0 then s else false), 0, cntT B a ++ (cntT P i''
          ++ (jT P i'' ++ encodeD (OUT ++ rangeEnc i'')))⟩ := by
  induction i'' with
  | zero =>
    simp [rangeEnc]
    rfl
  | succ i'' ih =>
    have hrd := run_nv_inner B P a i'' (OUT ++ rangeEnc i'') ha (by omega)
      (if i'' = 0 then s else false)
    rw [show (OUT ++ rangeEnc i'').length = OUT.length + rangeLen i'' from by
        rw [List.length_append, rangeEnc_length],
      List.append_assoc, show rangeEnc i'' ++ encodeNat i'' = rangeEnc (i'' + 1) from rfl] at hrd
    rw [show nvInners B P OUT.length (i'' + 1)
        = nvInners B P OUT.length i'' + nvInner B P (OUT.length + rangeLen i'') i'' from rfl,
      run_add, ih (by omega), hrd, if_neg (by omega)]

/-- The outer round's clock. -/
def nvOuterRC (B P L t : ℕ) : ℕ := nvInners B P L P + 2 * t + 4 * B + 8 * P + 12

/-- **One outer round**: mark the outer bound's pair `t`, run the inner loop to completion, heal the inner
bound, **zero the variable**, and reset. -/
theorem run_nv_outer (B P t : ℕ) (OUT : List Bool) (ht : t < B) (hP : 0 < P) (s : Bool) :
    run nestVarMachine (nvOuterRC B P OUT.length t)
      ⟨(0, s), 0, cntT B t ++ (cntT P 0 ++ (jT P 0 ++ encodeD OUT))⟩
      = ⟨(0, false), 0, cntT B (t + 1) ++ (cntT P 0
          ++ (jT P 0 ++ encodeD (OUT ++ rangeEnc P)))⟩ := by
  have hcb := cntT_length B (t + 1) (by omega : t + 1 ≤ B)
  -- find and mark the outer bound's pair `t`
  have o1 := run_skipBs2 (cntT B t ++ (cntT P 0 ++ (jT P 0 ++ encodeD OUT))) 0 t s
    (fun i hi => ⟨by simpa using cntE_mark_lo B t _ i hi,
                  by simpa using cntE_mark_hi B t _ i hi⟩)
  simp only [Nat.zero_add] at o1
  have o2 := run_two_markB' (s := if t = 0 then s else true) (p := 2 * t)
    (T := cntT B t ++ (cntT P 0 ++ (jT P 0 ++ encodeD OUT)))
    (cntE_data B t _ (2 * t) (by omega) (by omega) (by omega))
    (cntE_data B t _ (2 * t + 1) (by omega) (by omega) (by omega))
  rw [cntT_mark B t _ ht] at o2
  -- the inner loop
  have o3 := run_nv_inners B P (t + 1) OUT (by omega) true P (le_refl P)
  -- the inner finale: detect exhaustion
  have o4 := run_skipWIs (cntT B (t + 1) ++ (cntT P P ++ (jT P P
      ++ encodeD (OUT ++ rangeEnc P)))) 0 B (if P = 0 then true else false)
    (fun i hi => by simpa using cntE_lo B (t + 1) _ i (by omega) hi)
  simp only [Nat.zero_add] at o4
  have o5 := run_two_crossWI
    (s := if B = 0 then (if P = 0 then true else false) else true) (p := 2 * B)
    (T := cntT B (t + 1) ++ (cntT P P ++ (jT P P ++ encodeD (OUT ++ rangeEnc P))))
    (cntE_cm_lo B (t + 1) _ (by omega)) (cntE_cm_hi B (t + 1) _ (by omega))
  have o6 := run_skipPs2 (cntT B (t + 1) ++ (cntT P P ++ (jT P P
      ++ encodeD (OUT ++ rangeEnc P)))) (2 * B + 2) P false
    (fun i hi => ⟨liftJ _ _ hcb (cntE_mark_lo P P _ i hi), by
      rw [show 2 * B + 2 + 2 * i + 1 = 2 * B + 2 + (2 * i + 1) from by omega]
      exact liftJ _ _ hcb (cntE_mark_hi P P _ i hi)⟩)
  have o7 := run_two_doneP' (s := if P = 0 then false else true) (p := 2 * B + 2 + 2 * P)
    (T := cntT B (t + 1) ++ (cntT P P ++ (jT P P ++ encodeD (OUT ++ rangeEnc P))))
    (liftJ _ _ hcb (cntE_cm_lo P P _ (le_refl P)))
    (by rw [show 2 * B + 2 + 2 * P + 1 = 2 * B + 2 + (2 * P + 1) from by omega]
        exact liftJ _ _ hcb (cntE_cm_hi P P _ (le_refl P)))
  -- heal the inner bound
  have o8 := run_skipWNs (cntT B (t + 1) ++ (cntT P P ++ (jT P P
      ++ encodeD (OUT ++ rangeEnc P)))) 0 B false
    (fun i hi => by simpa using cntE_lo B (t + 1) _ i (by omega) hi)
  simp only [Nat.zero_add] at o8
  have o9 := run_two_crossWN (s := if B = 0 then false else true) (p := 2 * B)
    (T := cntT B (t + 1) ++ (cntT P P ++ (jT P P ++ encodeD (OUT ++ rangeEnc P))))
    (cntE_cm_lo B (t + 1) _ (by omega)) (cntE_cm_hi B (t + 1) _ (by omega))
  have o10 := run_healPs2 (cntT B (t + 1)) B P (jT P P ++ encodeD (OUT ++ rangeEnc P)) hcb
    false P (le_refl P)
  have o11 := run_two_toZero' (s := if P = 0 then false else true) (p := 2 * B + 2 + 2 * P)
    (T := cntT B (t + 1) ++ (hlT P P ++ (jT P P ++ encodeD (OUT ++ rangeEnc P))))
    (liftJ _ _ hcb (hlE_cm_lo P _))
    (by rw [show 2 * B + 2 + 2 * P + 1 = 2 * B + 2 + (2 * P + 1) from by omega]
        exact liftJ _ _ hcb (hlE_cm_hi P _))
  rw [show 2 * B + 2 + 2 * P + 2 = 2 * B + 2 * P + 4 from by omega] at o11
  -- the zeroing walk
  have hcc' : (hlT P P).length = 2 * P + 2 := hlT_length P P (le_refl P)
  have o12 := run_two_zeroHead' (s := false) (p := 2 * B + 2 * P + 4)
    (T := cntT B (t + 1) ++ (hlT P P ++ (jT P P ++ encodeD (OUT ++ rangeEnc P))))
  have hw12 : writeAt (writeAt (cntT B (t + 1) ++ (hlT P P ++ (jT P P
        ++ encodeD (OUT ++ rangeEnc P)))) (2 * B + 2 * P + 4) false)
        (2 * B + 2 * P + 4 + 1) true
      = cntT B (t + 1) ++ (hlT P P ++ (zeroT P 0 ++ encodeD (OUT ++ rangeEnc P))) := by
    rw [show 2 * B + 2 * P + 4 = 2 * B + 2 + (2 * P + 2 + 0) from by omega,
      W2_append_right2 (cntT B (t + 1)) (hlT P P) _ (2 * B + 2) (2 * P + 2) 0 false true hcb
        hcc' (by rw [List.length_append, jT_length P P (le_refl P)]; omega),
      zeroT_head P _ hP]
  rw [hw12] at o12
  rw [show 2 * B + 2 * P + 4 + 2 = 2 * B + 2 * P + 6 from by omega] at o12
  have o13 := run_zeros2 (cntT B (t + 1)) (hlT P P) B P (encodeD (OUT ++ rangeEnc P)) hcb
    hcc' hP false (P - 1) (le_refl _)
  have o14 := run_four_zeroLast'
    (s := if P - 1 = 0 then false else true) (p := 2 * B + 2 * P + 6 + 2 * (P - 1))
    (T := cntT B (t + 1) ++ (hlT P P ++ (zeroT P (P - 1) ++ encodeD (OUT ++ rangeEnc P))))
    (by rw [show 2 * B + 2 * P + 6 + 2 * (P - 1) = 2 * B + 2 + (2 * P + 2 + 2 * P)
        from by omega]
        exact liftJ2 _ _ _ hcb hcc' (zeroE_m_lo P _ hP))
    (by rw [show 2 * B + 2 * P + 6 + 2 * (P - 1) + 1 = 2 * B + 2 + (2 * P + 2 + (2 * P + 1))
        from by omega]
        exact liftJ2 _ _ _ hcb hcc' (zeroE_m_hi P _ hP))
  have hw14 : writeAt (writeAt (cntT B (t + 1) ++ (hlT P P ++ (zeroT P (P - 1)
        ++ encodeD (OUT ++ rangeEnc P)))) (2 * B + 2 * P + 6 + 2 * (P - 1)) false)
        (2 * B + 2 * P + 6 + 2 * (P - 1) + 1) false
      = cntT B (t + 1) ++ (hlT P P ++ (jT P 0 ++ encodeD (OUT ++ rangeEnc P))) := by
    rw [show 2 * B + 2 * P + 6 + 2 * (P - 1) = 2 * B + 2 + (2 * P + 2 + 2 * P) from by omega,
      W2_append_right2 (cntT B (t + 1)) (hlT P P) _ (2 * B + 2) (2 * P + 2) (2 * P) false
        false hcb hcc'
        (by rw [List.length_append, zeroT_length P (P - 1) (le_refl _) hP]; omega),
      zeroT_last P _ hP]
  rw [hw14] at o14
  -- assemble
  rw [show nvOuterRC B P OUT.length t
      = 2 * t + (2 + (nvInners B P OUT.length P + (2 * B + (2 + (2 * P + (2 + (2 * B + (2 + (2 * P + (2 + (2 + (4 * (P - 1) + (4)))))))))))))
      from by rw [nvOuterRC]; omega,
    run_add, o1, run_add, o2, run_add, o3, run_add, o4, run_add, o5, run_add, o6,
    run_add, o7, run_add, o8, run_add, o9, ← hlT_zero, run_add, o10, run_add, o11,
    run_add, o12, run_add, o13, o14, hlT_last, ← cntT_zero]

/-- Cumulative clock of the first `k` outer rounds. -/
def nvOuters (B P L : ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 => nvOuters B P L t + nvOuterRC B P (L + t * rangeLen P) t

theorem run_nv_outers (B P : ℕ) (out : List Bool) (hP : 0 < P) (k : ℕ) (hk : k ≤ B)
    (s : Bool) :
    run nestVarMachine (nvOuters B P out.length k)
      ⟨(0, s), 0, cntT B 0 ++ (cntT P 0 ++ (jT P 0 ++ encodeD out))⟩
      = ⟨(0, if k = 0 then s else false), 0, cntT B k ++ (cntT P 0
          ++ (jT P 0 ++ encodeD (out ++ blkRep (rangeEnc P) k)))⟩ := by
  induction k with
  | zero =>
    simp [blkRep]
    rfl
  | succ k ih =>
    have hrd := run_nv_outer B P k (out ++ blkRep (rangeEnc P) k) (by omega) hP
      (if k = 0 then s else false)
    rw [show (out ++ blkRep (rangeEnc P) k).length = out.length + k * rangeLen P from by
        rw [List.length_append, blkRep_length, rangeEnc_length],
      List.append_assoc,
      show blkRep (rangeEnc P) k ++ rangeEnc P = blkRep (rangeEnc P) (k + 1) from rfl] at hrd
    rw [show nvOuters B P out.length (k + 1)
        = nvOuters B P out.length k + nvOuterRC B P (out.length + k * rangeLen P) k from rfl,
      run_add, ih (by omega), hrd, if_neg (by omega)]

/-- The full clock. -/
def nvClock (B P L : ℕ) : ℕ := nvOuters B P L B + (2 * B + (2 + (2 * B + 2)))

/-- **The nested loop with a live variable runs to completion** (promise `0 < P`).  On
`unaryD B ++ (unaryD P ++ (jT P 0 ++ encodeD out))` the machine halts by itself at the explicit clock with
tape **exactly** `unaryD B ++ (unaryD P ++ (jT P 0 ++ encodeD (out ++ blkRep (rangeEnc P) B)))` — `B`
copies of the full range block, both bounds restored, **the variable zeroed**. -/
theorem nestVar_run (B P : ℕ) (hP : 0 < P) (out : List Bool) :
    run nestVarMachine (nvClock B P out.length)
      (init nestVarMachine (unaryD B ++ (unaryD P ++ (jT P 0 ++ encodeD out))))
      = ⟨(50, false), 2 * B + 1, unaryD B ++ (unaryD P
          ++ (jT P 0 ++ encodeD (out ++ blkRep (rangeEnc P) B)))⟩ := by
  rw [init_nv, ← cntT_zero, ← cntT_zero, nvClock, run_add,
    run_nv_outers B P out hP B (le_refl B) false, ite_self]
  have f1 := run_skipBs2 (cntT B B ++ (cntT P 0 ++ (jT P 0
      ++ encodeD (out ++ blkRep (rangeEnc P) B)))) 0 B false
    (fun i hi => ⟨by simpa using cntE_mark_lo B B _ i hi,
                  by simpa using cntE_mark_hi B B _ i hi⟩)
  simp only [Nat.zero_add] at f1
  have f2 := run_two_toRstB' (s := if B = 0 then false else true) (p := 2 * B)
    (T := cntT B B ++ (cntT P 0 ++ (jT P 0 ++ encodeD (out ++ blkRep (rangeEnc P) B))))
    (cntE_cm_lo B B _ (le_refl B)) (cntE_cm_hi B B _ (le_refl B))
  have f3 := run_healBs2 B (cntT P 0 ++ (jT P 0 ++ encodeD (out ++ blkRep (rangeEnc P) B)))
    false B (le_refl B)
  have f4 := run_two_doneB' (s := if B = 0 then false else true) (p := 2 * B)
    (hlE_cm_lo B (cntT P 0 ++ (jT P 0 ++ encodeD (out ++ blkRep (rangeEnc P) B))))
  rw [run_add, f1, run_add, f2, ← hlT_zero, run_add, f3, f4, hlT_last, cntT_zero, cntT_zero]

/-- The machine **halts by itself** at its clock. -/
theorem nestVar_halted (B P : ℕ) (hP : 0 < P) (out : List Bool) :
    nestVarMachine.halt
      (run nestVarMachine (nvClock B P out.length)
        (init nestVarMachine (unaryD B ++ (unaryD P ++ (jT P 0 ++ encodeD out))))).st
      = true := by
  rw [nestVar_run B P hP out]; rfl

/-- **The output**: both bounds restored, the variable zeroed, the `B·P` range blocks emitted. -/
theorem nestVar_output (B P : ℕ) (hP : 0 < P) (out : List Bool) :
    (run nestVarMachine (nvClock B P out.length)
      (init nestVarMachine (unaryD B ++ (unaryD P ++ (jT P 0 ++ encodeD out))))).tp
      = unaryD B ++ (unaryD P ++ (jT P 0 ++ encodeD (out ++ blkRep (rangeEnc P) B))) := by
  rw [nestVar_run B P hP out]

/-! ## Polynomial clock bounds -/

theorem nvSubs_le (B P L j : ℕ) (hj : j ≤ P) :
    nvSubs B P L j ≤ j * (2 * B + 4 * P + 2 * (L + P) + 12) := by
  induction j with
  | zero => simp [nvSubs]
  | succ j ih =>
    calc nvSubs B P L (j + 1)
        = nvSubs B P L j + (2 * B + 4 * P + 2 * (L + j) + 12) := rfl
      _ ≤ j * (2 * B + 4 * P + 2 * (L + P) + 12) + (2 * B + 4 * P + 2 * (L + P) + 12) :=
          Nat.add_le_add (ih (by omega)) (by omega)
      _ = (j + 1) * (2 * B + 4 * P + 2 * (L + P) + 12) := by ring

/-- The per-inner-round bound, atom-preserved. -/
def nvIRB (B P L : ℕ) : ℕ :=
  P * (2 * B + 4 * P + 2 * (L + P) + 12) + 6 * B + 12 * P + 2 * L + 26

theorem nvInner_le (B P L i : ℕ) (hi : i ≤ P) : nvInner B P L i ≤ nvIRB B P L := by
  have h := nvSubs_le B P L i hi
  have h2 : nvSubs B P L i ≤ P * (2 * B + 4 * P + 2 * (L + P) + 12) :=
    le_trans h (Nat.mul_le_mul_right _ hi)
  rw [nvInner, nvIRB]
  omega

theorem nvIRB_mono (B P L1 L2 : ℕ) (h : L1 ≤ L2) : nvIRB B P L1 ≤ nvIRB B P L2 := by
  rw [nvIRB, nvIRB]
  have : P * (2 * B + 4 * P + 2 * (L1 + P) + 12) ≤ P * (2 * B + 4 * P + 2 * (L2 + P) + 12) :=
    Nat.mul_le_mul_left P (by omega)
  omega

theorem nvInners_le (B P L i : ℕ) (hi : i ≤ P) :
    nvInners B P L i ≤ i * nvIRB B P (L + P * P) := by
  induction i with
  | zero => simp [nvInners]
  | succ i ih =>
    have hstep : nvInner B P (L + rangeLen i) i ≤ nvIRB B P (L + P * P) := by
      refine le_trans (nvInner_le B P (L + rangeLen i) i (by omega)) ?_
      refine nvIRB_mono B P _ _ ?_
      have h1 : rangeLen i ≤ i * i := rangeLen_le i
      have h2 : i * i ≤ P * P := Nat.mul_le_mul (by omega) (by omega)
      omega
    calc nvInners B P L (i + 1)
        = nvInners B P L i + nvInner B P (L + rangeLen i) i := rfl
      _ ≤ i * nvIRB B P (L + P * P) + nvIRB B P (L + P * P) :=
          Nat.add_le_add (ih (by omega)) hstep
      _ = (i + 1) * nvIRB B P (L + P * P) := by ring

/-- The per-outer-round bound. -/
def nvORB (B P L : ℕ) : ℕ := P * nvIRB B P (L + P * P) + 6 * B + 8 * P + 12

theorem nvOuterRC_le (B P L t : ℕ) (ht : t ≤ B) : nvOuterRC B P L t ≤ nvORB B P L := by
  have h := nvInners_le B P L P (le_refl P)
  rw [nvOuterRC, nvORB]
  omega

theorem nvORB_mono (B P L1 L2 : ℕ) (h : L1 ≤ L2) : nvORB B P L1 ≤ nvORB B P L2 := by
  rw [nvORB, nvORB]
  have := nvIRB_mono B P (L1 + P * P) (L2 + P * P) (by omega)
  have h2 : P * nvIRB B P (L1 + P * P) ≤ P * nvIRB B P (L2 + P * P) :=
    Nat.mul_le_mul_left P this
  omega

theorem nvOuters_le (B P L k : ℕ) (hk : k ≤ B) :
    nvOuters B P L k ≤ k * nvORB B P (L + B * rangeLen P) := by
  induction k with
  | zero => simp [nvOuters]
  | succ k ih =>
    have hstep : nvOuterRC B P (L + k * rangeLen P) k ≤ nvORB B P (L + B * rangeLen P) := by
      refine le_trans (nvOuterRC_le B P (L + k * rangeLen P) k (by omega)) ?_
      refine nvORB_mono B P _ _ ?_
      have : k * rangeLen P ≤ B * rangeLen P := Nat.mul_le_mul_right _ (by omega)
      omega
    calc nvOuters B P L (k + 1)
        = nvOuters B P L k + nvOuterRC B P (L + k * rangeLen P) k := rfl
      _ ≤ k * nvORB B P (L + B * rangeLen P) + nvORB B P (L + B * rangeLen P) :=
          Nat.add_le_add (ih (by omega)) hstep
      _ = (k + 1) * nvORB B P (L + B * rangeLen P) := by ring

/-- **The clock is polynomial** (explicit, atom-preserved). -/
theorem nvClock_le (B P L : ℕ) :
    nvClock B P L ≤ B * nvORB B P (L + B * rangeLen P) + (4 * B + 4) := by
  have h := nvOuters_le B P L B (le_refl B)
  rw [nvClock]
  omega

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitNestVar
