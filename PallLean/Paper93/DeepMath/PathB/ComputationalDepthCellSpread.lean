import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingComplexity

/-!
# Concrete cell-spreading simulation (foundation)

Goal: build an explicit space-expansion simulator `spreadM M` — each tape cell of `M` laid out over
two cells (value cell + inserted blank), head at doubled coordinates — and discharge the
`hpreserve` hypothesis of `crossingEnergy_survives_expansion` by proving crossing counts are
preserved at the embedded boundaries.

This file lands: the **tape encoding** (`spreadTape` + read/length lemmas), the **simulator machine**
(`spreadM`, `spreadCfg`), the **`getD` core** (`writeAt_getD`, `append_replicate_getD` — writes read
back positionally, up to trailing blanks), and the **congruence carrier** (`Congr`, `step_congr` —
the `getD`-equivalence a step cannot see through, which handles the delicate part below).
`hpreserve` is **not** yet discharged.

The **full semantic simulation is now machine-checked**: `two_step_spread` (two simulator steps
realise one `M` step, up to `Congr`), `run_spread` (`Congr (run (spreadM M) (2t) (spreadCfg c))
(spreadCfg (run M t c))` by induction via `step_congr` + transitivity), and `headAt_spread_even`
(the simulator's head at even times is exactly `2·(M's head)`).  The `getD`-equivalence subtlety
(writing past the tape end leaves a trailing-blank list mismatch invisible to `getD`) is fully
handled by `Congr`/`step_congr`.

What remains for `hpreserve` is only the crossing bijection `crossingCount M c b T ≤
crossingCount (spreadM M) (spreadCfg c) (2b) (2T)`: each `M`-crossing of `b` at step `t` is a
`spreadM`-crossing of `2b` at step `2t` or `2t+1`, giving an injection.  This needs the odd-time head
`headAt (spreadM) (2t+1)` (the first half-move, obtainable from `step_congr` + `spread_step_inl`) and
a per-step count — the final ~80 lines.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CellSpread

open PallLean.Paper93.DeepMath.PathB.ComposableMachine

/-- Lay each cell out over two: value cell followed by an inserted blank. -/
def spreadTape : List Bool → List Bool
  | [] => []
  | a :: rest => a :: false :: spreadTape rest

@[simp] theorem spreadTape_length (tp : List Bool) : (spreadTape tp).length = 2 * tp.length := by
  induction tp with
  | nil => simp [spreadTape]
  | cons a rest ih => simp only [spreadTape, List.length_cons, ih]; omega

/-- Even positions hold the original cell values. -/
theorem spreadTape_getD_even (tp : List Bool) (i : ℕ) :
    (spreadTape tp).getD (2 * i) false = tp.getD i false := by
  induction tp generalizing i with
  | nil => simp [spreadTape]
  | cons a rest ih =>
    cases i with
    | zero => simp [spreadTape]
    | succ j =>
      have hidx : 2 * (j + 1) = 2 * j + 1 + 1 := by omega
      rw [hidx]
      simp only [spreadTape, List.getD_cons_succ]
      exact ih j

/-- Odd positions are the inserted blanks. -/
theorem spreadTape_getD_odd (tp : List Bool) (i : ℕ) :
    (spreadTape tp).getD (2 * i + 1) false = false := by
  induction tp generalizing i with
  | nil => simp [spreadTape]
  | cons a rest ih =>
    cases i with
    | zero => simp [spreadTape]
    | succ j =>
      have hidx : 2 * (j + 1) + 1 = 2 * j + 1 + 1 + 1 := by omega
      rw [hidx]
      simp only [spreadTape, List.getD_cons_succ]
      exact ih j

/-! ## The move-doubling simulator machine -/

/-- The concrete cell-spreading simulator.  Control state is either `inl s` — phase 0, in `M`-state
`s`, about to read the value cell and perform `M`'s transition plus the first half of the doubled
move — or `inr (s', mv)` — phase 1, having done the work, completing the doubled move `mv`.  Two
`spreadM` steps realise one `M` step on the doubled layout: `inl s → inr (s',mv) → inl s'`, head
`2h → 2h ± 1 → 2(h ± 1)` (and reset `2h → 0 → 0`, whose second half is a stay). -/
noncomputable def spreadM (M : Machine) : Machine where
  State := M.State ⊕ (M.State × Move)
  fin := inferInstance
  dec := inferInstance
  start := Sum.inl M.start
  halt := fun s => match s with
    | Sum.inl s => M.halt s
    | Sum.inr _ => false
  δ := fun s a => match s with
    | Sum.inl s =>
        let tr := M.δ s a
        (Sum.inr (tr.1, tr.2.2), tr.2.1, tr.2.2)
    | Sum.inr sm => (Sum.inl sm.1, none, if sm.2 = 3 then 2 else sm.2)
  accept := fun s => match s with
    | Sum.inl s => M.accept s
    | Sum.inr _ => false

/-- The spread of an `M`-configuration: doubled head, spread tape, phase-0 state. -/
def spreadCfg {M : Machine} (c : Cfg M) : Cfg (spreadM M) :=
  ⟨Sum.inl c.st, 2 * c.hd, spreadTape c.tp⟩

/-! ## `getD` core: writes read back positionally, up to trailing blanks -/

/-- Appending trailing blanks does not change any `getD` read. -/
theorem append_replicate_getD (t : List Bool) (n i : ℕ) :
    (t ++ List.replicate n false).getD i false = t.getD i false := by
  by_cases hi : i < t.length
  · rw [List.getD, List.getD, List.getElem?_append_left hi]
  · push_neg at hi
    have h1 : t[i]? = none := List.getElem?_eq_none hi
    have h2 : (t ++ List.replicate n false)[i]? = (List.replicate n false)[i - t.length]? :=
      List.getElem?_append_right hi
    rw [List.getD, List.getD, h1, h2, Option.getD_none]
    rcases lt_or_ge (i - t.length) n with hlt | hge
    · rw [List.getElem?_replicate]; simp [hlt]
    · rw [List.getElem?_eq_none (by simpa using hge)]; rfl

/-- Positional read-after-write for `ComposableMachine.writeAt`: reading position `p` gives `w`,
every other position reads exactly as before. -/
theorem writeAt_getD (t : List Bool) (p : ℕ) (w : Bool) (i : ℕ) :
    (writeAt t p w).getD i false = if i = p then w else t.getD i false := by
  unfold writeAt
  set u := t ++ List.replicate (p + 1 - t.length) false with hu
  have hlen : p < u.length := by
    rw [hu, List.length_append, List.length_replicate]; omega
  by_cases hip : i = p
  · subst hip
    simp [List.getD, List.getElem?_set_self hlen]
  · have hne : (u.set p w)[i]? = u[i]? := List.getElem?_set_ne (Ne.symm hip)
    rw [if_neg hip, List.getD, hne, ← List.getD, hu, append_replicate_getD]

/-! ## Configuration congruence: equal up to trailing blanks -/

/-- Two configurations are congruent if they have the same state and head and read equally
everywhere (`getD`-equal tapes).  The step function cannot tell congruent configurations apart. -/
def Congr {M' : Machine} (d1 d2 : Cfg M') : Prop :=
  d1.st = d2.st ∧ d1.hd = d2.hd ∧ ∀ i, d1.tp.getD i false = d2.tp.getD i false

theorem Congr.rfl' {M' : Machine} (d : Cfg M') : Congr d d := ⟨rfl, rfl, fun _ => rfl⟩

theorem Congr.trans' {M' : Machine} {a b c : Cfg M'} (h1 : Congr a b) (h2 : Congr b c) :
    Congr a c := ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, fun i => (h1.2.2 i).trans (h2.2.2 i)⟩

/-- **`step` respects congruence.**  Congruent configurations step to congruent configurations —
the read, the transition, the move, and the write all agree up to trailing blanks. -/
theorem step_congr {M' : Machine} {d1 d2 : Cfg M'} (h : Congr d1 d2) :
    Congr (step M' d1) (step M' d2) := by
  obtain ⟨hst, hhd, htp⟩ := h
  have hread : d1.tp.getD d1.hd false = d2.tp.getD d2.hd false := by rw [hhd]; exact htp d2.hd
  unfold step
  by_cases hh : M'.halt d1.st = true
  · rw [if_pos hh, if_pos (hst ▸ hh)]; exact ⟨hst, hhd, htp⟩
  · rw [if_neg hh, if_neg (hst ▸ hh)]
    have hopt : (M'.δ d1.st (d1.tp.getD d1.hd false)).2.1
              = (M'.δ d2.st (d2.tp.getD d2.hd false)).2.1 := by rw [hst, hread]
    refine ⟨by rw [hst, hread], by rw [hst, hread, hhd], ?_⟩
    intro i
    show (match (M'.δ d1.st (d1.tp.getD d1.hd false)).2.1 with
          | none => d1.tp | some w => writeAt d1.tp d1.hd w).getD i false
       = (match (M'.δ d2.st (d2.tp.getD d2.hd false)).2.1 with
          | none => d2.tp | some w => writeAt d2.tp d2.hd w).getD i false
    rw [hopt]
    cases (M'.δ d2.st (d2.tp.getD d2.hd false)).2.1 with
    | none => exact htp i
    | some val =>
        rw [writeAt_getD, writeAt_getD, hhd]
        by_cases hi : i = d2.hd
        · rw [if_pos hi, if_pos hi]
        · rw [if_neg hi, if_neg hi]; exact htp i

/-! ## Two-step simulation and the run induction -/

/-- A non-halted step, spelled out. -/
theorem step_active {M' : Machine} (d : Cfg M') (hh : ¬ M'.halt d.st = true) :
    step M' d = ⟨(M'.δ d.st (d.tp.getD d.hd false)).1,
                 moveHead d.hd (M'.δ d.st (d.tp.getD d.hd false)).2.2,
                 match (M'.δ d.st (d.tp.getD d.hd false)).2.1 with
                 | none => d.tp | some w => writeAt d.tp d.hd w⟩ := by
  unfold step; rw [if_neg hh]; rfl

/-- The doubled move lands on the doubled target. -/
theorem head_two_step (h : ℕ) (mv : Move) :
    moveHead (moveHead (2 * h) mv) (if mv = 3 then 2 else mv) = 2 * moveHead h mv := by
  fin_cases mv <;> simp [moveHead] <;> omega

/-- First simulator step from a phase-0 configuration. -/
theorem spread_step_inl {M : Machine} (c : Cfg M) (hh : ¬ M.halt c.st = true) :
    step (spreadM M) (spreadCfg c)
      = ⟨Sum.inr ((M.δ c.st (c.tp.getD c.hd false)).1, (M.δ c.st (c.tp.getD c.hd false)).2.2),
         moveHead (2 * c.hd) (M.δ c.st (c.tp.getD c.hd false)).2.2,
         match (M.δ c.st (c.tp.getD c.hd false)).2.1 with
         | none => spreadTape c.tp
         | some v => writeAt (spreadTape c.tp) (2 * c.hd) v⟩ := by
  rw [step_active (spreadCfg c) hh]
  simp only [spreadM, spreadCfg, spreadTape_getD_even]

/-- Second simulator step from a phase-1 configuration completes the doubled move. -/
theorem spread_step_inr {M : Machine} (s' : M.State) (mv : Move) (hd : ℕ) (tp : List Bool) :
    step (spreadM M) ⟨Sum.inr (s', mv), hd, tp⟩
      = ⟨Sum.inl s', moveHead hd (if mv = 3 then 2 else mv), tp⟩ := by
  rw [step_active (M' := spreadM M) ⟨Sum.inr (s', mv), hd, tp⟩ (by simp [spreadM])]
  simp only [spreadM]

/-- **Two steps of the simulator realise one `M` step**, up to congruence. -/
theorem two_step_spread {M : Machine} (c : Cfg M) :
    Congr (step (spreadM M) (step (spreadM M) (spreadCfg c))) (spreadCfg (step M c)) := by
  by_cases hh : M.halt c.st = true
  · have h1 : step (spreadM M) (spreadCfg c) = spreadCfg c := step_of_halted (spreadM M) hh
    rw [h1, h1, step_of_halted M hh]; exact Congr.rfl' _
  · rw [spread_step_inl c hh, spread_step_inr, step_active c hh]
    refine ⟨rfl, head_two_step c.hd _, ?_⟩
    intro i
    simp only [spreadCfg]
    cases hw : (M.δ c.st (c.tp.getD c.hd false)).2.1 with
    | none => rfl
    | some v =>
        rw [writeAt_getD]
        rcases Nat.even_or_odd i with he | ho
        · obtain ⟨j, hje⟩ := he
          have hij : i = 2 * j := by omega
          subst hij
          rw [spreadTape_getD_even, spreadTape_getD_even, writeAt_getD]
          by_cases hjc : j = c.hd
          · rw [if_pos (by omega), if_pos hjc]
          · rw [if_neg (by omega), if_neg hjc]
        · obtain ⟨j, hjo⟩ := ho
          subst hjo
          rw [spreadTape_getD_odd, if_neg (by omega), spreadTape_getD_odd]

/-- **The simulation invariant.**  After `2t` simulator steps the configuration is congruent to the
spread of `M`'s configuration after `t` steps — in particular the head sits at `2·(M's head)`. -/
theorem run_spread {M : Machine} (c : Cfg M) (t : ℕ) :
    Congr (run (spreadM M) (2 * t) (spreadCfg c)) (spreadCfg (run M t c)) := by
  induction t with
  | zero => simp only [Nat.mul_zero, run_zero]; exact Congr.rfl' _
  | succ t ih =>
    have hstep : run (spreadM M) (2 * (t + 1)) (spreadCfg c)
               = step (spreadM M) (step (spreadM M) (run (spreadM M) (2 * t) (spreadCfg c))) := by
      rw [show 2 * (t + 1) = 2 * t + 1 + 1 from by omega, run_succ, run_succ]
    rw [hstep, run_succ]
    exact Congr.trans' (step_congr (step_congr ih)) (two_step_spread (run M t c))

/-- The simulator's head at even times is exactly the doubled head of `M`. -/
theorem headAt_spread_even {M : Machine} (c : Cfg M) (t : ℕ) :
    (run (spreadM M) (2 * t) (spreadCfg c)).hd = 2 * (run M t c).hd :=
  (run_spread c t).2.1

end PallLean.Paper93.DeepMath.PathB.CellSpread
