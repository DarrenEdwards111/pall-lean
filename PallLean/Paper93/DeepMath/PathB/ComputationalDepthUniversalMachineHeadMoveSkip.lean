import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUniversalMachineHeadMove

/-!
# Head-move construction, brick 2: sequencing field-walks (`skip2`)

`scanUnary` (brick 1) walks the head across ONE unary field and halts on its terminator.  The
universal control must cross SEVERAL consecutive fields — e.g. `encodeConf c = encNat st ++ encNat hd
++ encList encBool tp`, where reaching the simulated tape means walking past the `state` field and the
`head` field first.  A single `scanUnary` cannot: once it halts it is stuck forever.  Crossing two
fields therefore genuinely needs a multi-phase fixed-control machine that re-arms its scanner after
each field boundary.  This brick builds that machine, `skip2`, and proves it.

## What is proved

* **`getD_encNat_true` / `getD_encNat_false`** — reusable: reading inside / at the terminator of an
  `encNat v` field sitting at offset `|pre|` on any tape returns the expected bit.  (Factored so both
  head-move bricks share the encoding-indexing arithmetic.)
* **`skip2`** — an honest three-state `ComposableMachine` (`fieldA`, `fieldB`, `done`).  In `fieldA`
  it scans right over `true`s; on the terminating `false` it steps PAST it and switches to `fieldB`;
  `fieldB` does the same and switches to `done` (halt).  No writes — the tape is untouched.
* **`skip2_phaseA` / `skip2_phaseB`** — each phase walks one unary field and re-arms / halts, landing
  one cell past the terminator (by induction, as in brick 1).
* **`skip2_run`** — the composition: from `fieldA`, across a value-`a` field then a value-`b` field,
  after `(a+1) + (b+1)` steps the machine is halted at `hd + a + 1 + b + 1`, tape unchanged.
* **`skip2_parses`** (payoff): on any tape `pre ++ encNat a ++ encNat b ++ post` with the head at
  `|pre|`, `skip2` walks past BOTH fields, halting at `|pre| + a + 1 + b + 1` — the physical
  two-field skip that reaches the third field's first cell.

## Honest scope

This is the second head-move primitive: crossing a fixed number of consecutive variable-length fields,
realised as a real multi-phase `ComposableMachine` and proved correct against the encoding.  With
brick 1 (single-field walk) it gives navigation of the config's internal fields.  What remains for the
full `uStepOnTape` control: the data-dependent seek (move the head to the simulated-head position
stored on the tape — a unary counter with tape mutation/restoration), the local read/write, rule
lookup, and sequencing; then the lazy-delay diagonal (brick 5).  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.UniversalMachineHeadMoveSkip

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.UniversalMachineSerial
open PallLean.Paper93.DeepMath.PathB.UniversalMachineHeadMove

/-! ## Reusable encoding-indexing facts -/

/-- Reading strictly inside an `encNat v` field (at offset `|pre| + i`, `i < v`) yields `true`. -/
theorem getD_encNat_true (pre post : List Bool) (v i : ℕ) (h : i < v) :
    (pre ++ encNat v ++ post).getD (pre.length + i) false = true := by
  rw [encNat_eq_replicate]
  simp only [List.append_assoc]
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_append_right (Nat.le_add_right pre.length i), Nat.add_sub_cancel_left,
    List.getElem?_append_left (by rw [List.length_replicate]; exact h),
    List.getElem?_replicate_of_lt h]
  rfl

/-- Reading the terminator of an `encNat v` field (at offset `|pre| + v`) yields `false`. -/
theorem getD_encNat_false (pre post : List Bool) (v : ℕ) :
    (pre ++ encNat v ++ post).getD (pre.length + v) false = false := by
  rw [encNat_eq_replicate]
  simp only [List.append_assoc]
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_append_right (Nat.le_add_right pre.length v), Nat.add_sub_cancel_left,
    List.getElem?_append_right (by simp)]
  simp

/-- `|encNat v| = v + 1`. -/
theorem encNat_length' (v : ℕ) : (encNat v).length = v + 1 := by
  simp [encNat_eq_replicate]

/-! ## The two-field skip machine -/

/-- Control states of `skip2`: scanning the first field, scanning the second, or done. -/
inductive Skip2 where
  | fieldA : Skip2
  | fieldB : Skip2
  | done : Skip2
  deriving DecidableEq

instance : Fintype Skip2 := ⟨{.fieldA, .fieldB, .done}, fun x => by cases x <;> decide⟩

/-- **The two-field skip machine.**  A fixed-control `ComposableMachine`.  `fieldA`/`fieldB` scan
right over `true`s; on the terminating `false` the head steps PAST it and the phase advances
(`fieldA → fieldB → done`).  No writes — the tape is never modified. -/
def skip2 : Machine where
  State := Skip2
  fin := inferInstance
  dec := inferInstance
  start := Skip2.fieldA
  halt := fun s => match s with | .done => true | _ => false
  δ := fun s _b => match s with
    | .fieldA => if _b then (Skip2.fieldA, none, (1 : Move)) else (Skip2.fieldB, none, (1 : Move))
    | .fieldB => if _b then (Skip2.fieldB, none, (1 : Move)) else (Skip2.done, none, (1 : Move))
    | .done => (Skip2.done, none, (2 : Move))
  accept := fun _ => false

/-- Front-step form for the field-walk induction. -/
theorem skip2_run_succ_head (t : ℕ) (c : Cfg skip2) :
    run skip2 (t + 1) c = run skip2 t (step skip2 c) :=
  Function.iterate_succ_apply (step skip2) t c

/-- `step` in an active (non-halted) state, unfolded. -/
theorem skip2_step_active {c : Cfg skip2} (hne : skip2.halt c.st = false) :
    step skip2 c = ⟨(skip2.δ c.st (c.tp.getD c.hd false)).1,
                    moveHead c.hd (skip2.δ c.st (c.tp.getD c.hd false)).2.2,
                    (match (skip2.δ c.st (c.tp.getD c.hd false)).2.1 with
                      | none => c.tp | some w => writeAt c.tp c.hd w)⟩ := by
  unfold step; rw [hne]; rfl

theorem skip2_step_A_true {c : Cfg skip2} (hs : c.st = Skip2.fieldA)
    (hb : c.tp.getD c.hd false = true) : step skip2 c = ⟨Skip2.fieldA, c.hd + 1, c.tp⟩ := by
  rw [skip2_step_active (by rw [hs]; rfl), hs, hb]; rfl

theorem skip2_step_A_false {c : Cfg skip2} (hs : c.st = Skip2.fieldA)
    (hb : c.tp.getD c.hd false = false) : step skip2 c = ⟨Skip2.fieldB, c.hd + 1, c.tp⟩ := by
  rw [skip2_step_active (by rw [hs]; rfl), hs, hb]; rfl

theorem skip2_step_B_true {c : Cfg skip2} (hs : c.st = Skip2.fieldB)
    (hb : c.tp.getD c.hd false = true) : step skip2 c = ⟨Skip2.fieldB, c.hd + 1, c.tp⟩ := by
  rw [skip2_step_active (by rw [hs]; rfl), hs, hb]; rfl

theorem skip2_step_B_false {c : Cfg skip2} (hs : c.st = Skip2.fieldB)
    (hb : c.tp.getD c.hd false = false) : step skip2 c = ⟨Skip2.done, c.hd + 1, c.tp⟩ := by
  rw [skip2_step_active (by rw [hs]; rfl), hs, hb]; rfl

/-- **Phase A (proved).**  From `fieldA`, walking a value-`a` field re-arms into `fieldB` one cell
past the terminator: `run skip2 (a+1) c = ⟨fieldB, c.hd + a + 1, c.tp⟩`. -/
theorem skip2_phaseA (a : ℕ) : ∀ (c : Cfg skip2), c.st = Skip2.fieldA →
    (∀ i, i < a → c.tp.getD (c.hd + i) false = true) →
    c.tp.getD (c.hd + a) false = false →
    run skip2 (a + 1) c = ⟨Skip2.fieldB, c.hd + a + 1, c.tp⟩ := by
  induction a with
  | zero =>
    intro c hs _ hstop
    rw [Nat.add_zero] at hstop
    rw [show run skip2 1 c = step skip2 c from rfl, skip2_step_A_false hs hstop]
  | succ a ih =>
    intro c hs htrue hstop
    have h0 : c.tp.getD c.hd false = true := by
      have := htrue 0 (Nat.succ_pos a); rwa [Nat.add_zero] at this
    rw [skip2_run_succ_head, skip2_step_A_true hs h0]
    have hkey := ih ⟨Skip2.fieldA, c.hd + 1, c.tp⟩ rfl
      (fun i hi => by
        show c.tp.getD (c.hd + 1 + i) false = true
        have := htrue (i + 1) (by omega)
        rwa [show c.hd + (i + 1) = c.hd + 1 + i from by omega] at this)
      (by
        show c.tp.getD (c.hd + 1 + a) false = false
        rwa [show c.hd + (a + 1) = c.hd + 1 + a from by omega] at hstop)
    rw [hkey]
    show (⟨Skip2.fieldB, c.hd + 1 + a + 1, c.tp⟩ : Cfg skip2) = ⟨Skip2.fieldB, c.hd + (a + 1) + 1, c.tp⟩
    rw [show c.hd + 1 + a + 1 = c.hd + (a + 1) + 1 from by omega]

/-- **Phase B (proved).**  From `fieldB`, walking a value-`b` field halts (`done`) one cell past the
terminator: `run skip2 (b+1) c = ⟨done, c.hd + b + 1, c.tp⟩`. -/
theorem skip2_phaseB (b : ℕ) : ∀ (c : Cfg skip2), c.st = Skip2.fieldB →
    (∀ i, i < b → c.tp.getD (c.hd + i) false = true) →
    c.tp.getD (c.hd + b) false = false →
    run skip2 (b + 1) c = ⟨Skip2.done, c.hd + b + 1, c.tp⟩ := by
  induction b with
  | zero =>
    intro c hs _ hstop
    rw [Nat.add_zero] at hstop
    rw [show run skip2 1 c = step skip2 c from rfl, skip2_step_B_false hs hstop]
  | succ b ih =>
    intro c hs htrue hstop
    have h0 : c.tp.getD c.hd false = true := by
      have := htrue 0 (Nat.succ_pos b); rwa [Nat.add_zero] at this
    rw [skip2_run_succ_head, skip2_step_B_true hs h0]
    have hkey := ih ⟨Skip2.fieldB, c.hd + 1, c.tp⟩ rfl
      (fun i hi => by
        show c.tp.getD (c.hd + 1 + i) false = true
        have := htrue (i + 1) (by omega)
        rwa [show c.hd + (i + 1) = c.hd + 1 + i from by omega] at this)
      (by
        show c.tp.getD (c.hd + 1 + b) false = false
        rwa [show c.hd + (b + 1) = c.hd + 1 + b from by omega] at hstop)
    rw [hkey]
    show (⟨Skip2.done, c.hd + 1 + b + 1, c.tp⟩ : Cfg skip2) = ⟨Skip2.done, c.hd + (b + 1) + 1, c.tp⟩
    rw [show c.hd + 1 + b + 1 = c.hd + (b + 1) + 1 from by omega]

/-- **The two-field skip (proved).**  From `fieldA`, across a value-`a` field then a value-`b` field
(the second starting one cell past the first's terminator), after `(a+1) + (b+1)` steps the machine is
halted at `hd + a + 1 + b + 1`, tape unchanged. -/
theorem skip2_run (a b : ℕ) (c : Cfg skip2) (hs : c.st = Skip2.fieldA)
    (hA : ∀ i, i < a → c.tp.getD (c.hd + i) false = true)
    (hAf : c.tp.getD (c.hd + a) false = false)
    (hB : ∀ j, j < b → c.tp.getD (c.hd + a + 1 + j) false = true)
    (hBf : c.tp.getD (c.hd + a + 1 + b) false = false) :
    run skip2 (a + 1 + (b + 1)) c = ⟨Skip2.done, c.hd + a + 1 + b + 1, c.tp⟩ := by
  rw [run_add, skip2_phaseA a c hs hA hAf]
  have hB' := skip2_phaseB b ⟨Skip2.fieldB, c.hd + a + 1, c.tp⟩ rfl
    (fun j hj => by show c.tp.getD (c.hd + a + 1 + j) false = true; exact hB j hj)
    (by show c.tp.getD (c.hd + a + 1 + b) false = false; exact hBf)
  rw [hB']

/-- **Payoff (proved): the physical two-field skip.**  On any tape `pre ++ encNat a ++ encNat b ++
post` with the head at the first field's start (`|pre|`), `skip2` walks past both fields, halting at
`|pre| + a + 1 + b + 1` (the first cell of the third field), tape unchanged. -/
theorem skip2_parses (pre post : List Bool) (a b : ℕ) :
    run skip2 (a + 1 + (b + 1)) ⟨Skip2.fieldA, pre.length, pre ++ encNat a ++ encNat b ++ post⟩
      = ⟨Skip2.done, pre.length + a + 1 + b + 1, pre ++ encNat a ++ encNat b ++ post⟩ := by
  have hassocA : pre ++ encNat a ++ encNat b ++ post = pre ++ encNat a ++ (encNat b ++ post) := by
    rw [List.append_assoc]
  have hassocB : pre ++ encNat a ++ encNat b ++ post = (pre ++ encNat a) ++ encNat b ++ post := by
    rw [List.append_assoc]
  have hlen : (pre ++ encNat a).length = pre.length + a + 1 := by
    rw [List.length_append, encNat_length']; omega
  apply skip2_run a b ⟨Skip2.fieldA, pre.length, pre ++ encNat a ++ encNat b ++ post⟩ rfl
  · intro i hi
    show (pre ++ encNat a ++ encNat b ++ post).getD (pre.length + i) false = true
    rw [hassocA]; exact getD_encNat_true pre (encNat b ++ post) a i hi
  · show (pre ++ encNat a ++ encNat b ++ post).getD (pre.length + a) false = false
    rw [hassocA]; exact getD_encNat_false pre (encNat b ++ post) a
  · intro j hj
    show (pre ++ encNat a ++ encNat b ++ post).getD (pre.length + a + 1 + j) false = true
    rw [hassocB, ← hlen]
    exact getD_encNat_true (pre ++ encNat a) post b j hj
  · show (pre ++ encNat a ++ encNat b ++ post).getD (pre.length + a + 1 + b) false = false
    rw [hassocB, ← hlen]
    exact getD_encNat_false (pre ++ encNat a) post b

end PallLean.Paper93.DeepMath.PathB.UniversalMachineHeadMoveSkip

#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineHeadMoveSkip.skip2_run
#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineHeadMoveSkip.skip2_parses
