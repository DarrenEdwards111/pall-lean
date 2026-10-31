import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ConcreteNTM
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0NTM

/-!
# Phase-internal refinement, completed — decode/re-encode (tape walk) and apply (O(1)) (proved)

Entry 310 cell-refined the lookup phase (`M.length` single-rule steps).  This file grinds out the remaining three
phases, all the same fold-as-small-steps pattern:

* **decode / re-encode** — a tape-cell traversal: process one cell per step, `|tape|` primitive steps.
  `walk_reaches` proves the generic cell-by-cell pass (`List.foldl`, `|cells|` steps) — the cost model for decode
  (reading the encoded tape) and re-encode (writing it).  Their *correctness* is the already-proved function-level
  `decodeSim_encodeSim` (`…ACC0UniversalDecode`); their *cost* is `|tape|` primitive cell-steps, proved here.
* **apply** — `O(1)`: applying a rule is **3** primitive field-updates — write the symbol, move the head, set the
  state — composing to `applyTrans c t` (`apply_phase_celled`).

So all four phases are now refined to primitive single-operation steps: decode `|tape|`, lookup `M.length` (entry 310),
apply `3`, re-encode `|tape|` — each an exact primitive step count, together the per-`uEncStep` `stepOverhead` (entry
305).

## What is proved (clean axioms, no `sorry`)

* **`walkStep`, `walkNTM`, `walk_reaches`** — the generic tape-cell traversal: from `(cells, acc)`, in exactly
  `cells.length` primitive steps, reach `([], cells.foldl g acc)`.  The decode/re-encode cell-cost model.
* **`applyStep`, `applyNTM`, `apply_phase_celled`** — applying a rule in exactly **3** primitive steps:
  `reachIn (applyNTM t) 3 (0, c) (3, applyTrans c t)` (write → move → state).

## Honest scope

This refines the decode/re-encode phases to the generic `|tape|`-step tape-cell traversal (`walk_reaches`, their cost;
correctness is the proved `decodeSim_encodeSim`) and the apply phase to **3** primitive field-update steps
(`apply_phase_celled`).  With lookup (entry 310), **all four phases are now cell-refined to exact primitive step
counts**.  Pure mechanical list/automata bookkeeping, classical, not an open problem.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0PhaseCellOpsRest

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (NTM reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (CConfig TMTrans moveHead writeAt applyTrans)

/-! ## Decode / re-encode — the tape-cell traversal -/

/-- One primitive tape-cell step: consume the head cell, folding it into the accumulator via `g`. -/
def walkStep (g : List Bool → Bool → List Bool) :
    (List Bool × List Bool) → (List Bool × List Bool) → Prop
  | (b :: rest, acc), st => st = (rest, g acc b)
  | ([], acc), st => st = ([], acc)

/-- The tape-cell traversal machine (one cell per step). -/
def walkNTM (g : List Bool → Bool → List Bool) : NTM where
  Config := List Bool × List Bool
  step := walkStep g
  init := fun x => (x, [])
  accept := fun _ => False

/-- **The tape-cell traversal (PROVED).**  From `(cells, acc)`, in exactly `cells.length` primitive steps, the walk
reaches `([], cells.foldl g acc)` — processing one cell at a time.  Induction on `cells`.  This is the cost model for
the decode (read) and re-encode (write) phases: `|tape|` primitive cell-steps. -/
theorem walk_reaches (g : List Bool → Bool → List Bool) (cells acc : List Bool) :
    reachIn (walkNTM g) cells.length (cells, acc) ([], cells.foldl g acc) := by
  induction cells generalizing acc with
  | nil => simp [reachIn]
  | cons b rest ih =>
    rw [List.length_cons, List.foldl_cons]
    exact ⟨(rest, g acc b), rfl, ih _⟩

/-! ## Apply — `O(1)`: write, move, set state -/

/-- One primitive apply step: phase `0` writes the symbol, `1` moves the head, `2` sets the state. -/
def applyStep (t : TMTrans) : (ℕ × CConfig) → (ℕ × CConfig) → Prop
  | (0, c), st => st = (1, (c.1, c.2.1, writeAt c.2.2 c.2.1 t.2.2.1))
  | (1, c), st => st = (2, (c.1, moveHead c.2.1 t.2.2.2, c.2.2))
  | (2, c), st => st = (3, (t.2.1, c.2.1, c.2.2))
  | (_, c), st => st = (3, c)

/-- The apply micro-machine (a 3-step controller). -/
def applyNTM (t : TMTrans) : NTM where
  Config := ℕ × CConfig
  step := applyStep t
  init := fun _ => (0, (0, 0, []))
  accept := fun _ => False

/-- **The apply phase in 3 primitive steps (PROVED).**  Applying a rule `t` to `c` is three primitive field-updates —
write the symbol, move the head, set the state — composing exactly to `applyTrans c t`:
`reachIn (applyNTM t) 3 (0, c) (3, applyTrans c t)`. -/
theorem apply_phase_celled (t : TMTrans) (c : CConfig) :
    reachIn (applyNTM t) 3 (0, c) (3, applyTrans c t) := by
  obtain ⟨st0, h0, tape0⟩ := c
  exact ⟨(1, (st0, h0, writeAt tape0 h0 t.2.2.1)), rfl,
         (2, (st0, moveHead h0 t.2.2.2, writeAt tape0 h0 t.2.2.1)), rfl,
         (3, applyTrans (st0, h0, tape0) t), rfl, rfl⟩

/-!
**All four phases cell-refined.**  Decode and re-encode are the generic tape-cell traversal (`walk_reaches`, `|tape|`
primitive steps — their cost; correctness is the proved `decodeSim_encodeSim`); apply is **3** primitive field-update
steps (`apply_phase_celled`); lookup is `M.length` single-rule steps (entry 310).  Each phase macro-step is now an exact
primitive step count, together the per-`uEncStep` `stepOverhead` (entry 305).  The transition-table compile is fully
ground from logical tracking down to primitive single-operation steps.  Pure mechanical bookkeeping.  Not faked, not a
separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0PhaseCellOpsRest

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PhaseCellOpsRest.walk_reaches
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PhaseCellOpsRest.apply_phase_celled
