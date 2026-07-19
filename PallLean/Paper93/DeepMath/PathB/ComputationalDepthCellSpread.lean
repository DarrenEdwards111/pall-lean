import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingComplexity

/-!
# Concrete cell-spreading simulation (foundation)

Goal: build an explicit space-expansion simulator `spreadM M` — each tape cell of `M` laid out over
two cells (value cell + inserted blank), head at doubled coordinates — and discharge the
`hpreserve` hypothesis of `crossingEnergy_survives_expansion` by proving crossing counts are
preserved at the embedded boundaries.

This file lands the **tape encoding** (`spreadTape` + read/length lemmas) and the **simulator
machine** (`spreadM`, `spreadCfg`).  What remains to actually discharge `hpreserve` is the two-step
simulation lemma and the crossing bijection; `hpreserve` is **not** discharged here.

Honest note on the remaining work: `spreadM` writes the value cell then completes a doubled move, so
two of its steps realise one `M` step — but only *up to `getD`-equivalence* on the tape.  When `M`
writes past its current tape end, `writeAt (spreadTape tp) (2h) w` and `spreadTape (writeAt tp h w)`
agree at every position yet differ as lists by a trailing blank.  So the simulation lemma must be
stated over a `getD`-equivalence relation on configurations (proved preserved by `step`), not raw
equality — the delicate remaining piece, roughly a couple hundred lines.

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

end PallLean.Paper93.DeepMath.PathB.CellSpread
