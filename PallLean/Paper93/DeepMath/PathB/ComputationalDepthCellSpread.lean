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

The `getD`-equivalence subtlety: `spreadM` writes the value cell then completes a doubled move, so
two of its steps realise one `M` step — but only *up to `getD`-equivalence* on the tape.  When `M`
writes past its current tape end, `writeAt (spreadTape tp) (2h) w` and `spreadTape (writeAt tp h w)`
agree at every position yet differ as lists by a trailing blank.  `Congr`/`step_congr` now carry that
equivalence through the run.  What remains is mechanical: the two-step lemma
`Congr (step² (spreadCfg c)) (spreadCfg (step M c))` (head arithmetic per move + tape via the
even/odd read lemmas), the run induction via `step_congr` + transitivity, and the crossing bijection
`crossingCount M c b T = crossingCount (spreadM M) (spreadCfg c) (2b+1) (2T)`.

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

end PallLean.Paper93.DeepMath.PathB.CellSpread
