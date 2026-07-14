import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinRendShift
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinScanRightSep
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinLoopEnds

/-!
# Cook–Levin M1 — the master `read a_v` machine (state, δ, non-vacuity)

Per `WELD_PLAN_READAV.md §9`.  One `Machine` welding the eight proven sub-machines with a loop-back.

**State** `Fin 10 × Fin 9 × Bool × Bool` = `(group, sub-phase, c₀, c₁)`.  `group` (`Fin 10`) selects the active
phase-group; `sub-phase` (`Fin 9`, wide enough for `rendShift`'s 9 phases) is the active sub-machine's local phase;
`(c₀, c₁)` is its carry (a pair for `rendShift`, one bit for the scans).

**Groups** `INIT=0, LOOPCHK=1, REPA=2, SHA=3, RANCH1=4, REPB=5, SHB=6, RANCH2=7, RRES=8, HALT=9`.  The flow is
`INIT → LOOPCHK → {counter: REPA→SHA→RANCH1→REPB→SHB→RANCH2 →(loop)→ LOOPCHK  |  done: RRES → HALT}`.

Each group's transition is a **helper** (`rendStep`/`scanLeftStep`/`scanRightStep`/`loopStep`/`readResStep`) that
reproduces the corresponding sub-machine's δ *verbatim* — so the per-group **simulation lemmas** (next chunk) that
lift the sub-machines' run-lemmas are immediate.  At a sub-machine's halt phase the master takes a **control-only
seam** (re-tag the group, reset the sub-phase; a constant head move) — the exact `comp`-switch pattern.

Non-vacuity holds by construction: **finite** `State` (a product of `Fin`/`Bool`), **forced** init
(`⟨start, 0, x⟩`), **local** δ.  This file: the machine + `master_forced_init`.  (This is the machine definition;
the seam head-moves are verified/refined with the simulation lemmas and the correctness chain — `§6`, `§9`.)

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinMaster

open PallLean.Paper93.DeepMath.PathB.ComposableMachine

/-! ## Per-sub-machine transition helpers (verbatim copies of the sub-machine δ's) -/

/-- `rendShift.δ` (delete a pair; halt phase `8`). -/
def rendStep (sp : Fin 9) (c0 c1 b : Bool) : (Fin 9 × Bool × Bool) × Option Bool × Fin 4 :=
  if sp = 0 then ((1, c0, c1), none, 1)
  else if sp = 1 then ((2, c0, c1), none, 1)
  else if sp = 2 then ((3, b, c1), none, 1)
  else if sp = 3 then ((4, c0, b), none, 0)
  else if sp = 4 then ((5, c0, c1), none, 0)
  else if sp = 5 then ((6, c0, c1), none, 0)
  else if sp = 6 then ((7, c0, c1), some c0, 1)
  else if sp = 7 then (if c0 && !c1 then ((8, c0, c1), some c1, 2) else ((0, c0, c1), some c1, 1))
  else ((8, c0, c1), none, 2)

/-- `scanLeftSep.δ` (scan left to `SEP`; halt phase `2`; stored high cell in `c₀`). -/
def scanLeftStep (sp : Fin 9) (c0 b : Bool) : (Fin 9 × Bool × Bool) × Option Bool × Fin 4 :=
  if sp = 0 then ((1, b, false), none, 0)
  else if sp = 1 then (if !b && c0 then ((2, c0, false), none, 2) else ((0, c0, false), none, 0))
  else ((2, c0, false), none, 2)

/-- `scanRightSep.δ` (scan right to `SEP`; halt phase `2`; stored low cell in `c₀`). -/
def scanRightStep (sp : Fin 9) (c0 b : Bool) : (Fin 9 × Bool × Bool) × Option Bool × Fin 4 :=
  if sp = 0 then ((1, b, false), none, 1)
  else if sp = 1 then (if !c0 && b then ((2, c0, false), none, 2) else ((0, c0, false), none, 1))
  else ((2, c0, false), none, 2)

/-- `loopCtrl.δ` (read the bit left of `SEP`; halt phase `2`; bit in `c₀`). -/
def loopStep (sp : Fin 9) (c0 b : Bool) : (Fin 9 × Bool × Bool) × Option Bool × Fin 4 :=
  if sp = 0 then ((1, c0, false), none, 0)
  else if sp = 1 then ((2, b, false), none, 2)
  else ((2, c0, false), none, 2)

/-- `readRes.δ` (read `a_v` at `SEP+2`; halt phase `3`; value in `c₀`). -/
def readResStep (sp : Fin 9) (c0 b : Bool) : (Fin 9 × Bool × Bool) × Option Bool × Fin 4 :=
  if sp = 0 then ((1, c0, false), none, 1)
  else if sp = 1 then ((2, c0, false), none, 1)
  else if sp = 2 then ((3, b, false), none, 2)
  else ((3, c0, false), none, 2)

/-! ## The master machine -/

/-- Repackage a helper result under a group tag. -/
def inGroup (g : Fin 10) (r : (Fin 9 × Bool × Bool) × Option Bool × Fin 4) :
    (Fin 10 × Fin 9 × Bool × Bool) × Option Bool × Fin 4 :=
  ((g, r.1.1, r.1.2.1, r.1.2.2), r.2.1, r.2.2)

/-- A control-only seam: jump to group `g` sub-phase `0` with cleared carry, moving the head by `m`. -/
def seam (g : Fin 10) (m : Fin 4) : (Fin 10 × Fin 9 × Bool × Bool) × Option Bool × Fin 4 :=
  ((g, 0, false, false), none, m)

/-- The welded master machine.  `State = (group, sub-phase, c₀, c₁)`. -/
def masterM : Machine where
  State := Fin 10 × Fin 9 × Bool × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, 0, false, false)
  halt := fun s => decide (s.1 = 9)
  δ := fun s b =>
    let g := s.1; let sp := s.2.1; let c0 := s.2.2.1; let c1 := s.2.2.2
    if g = 0 then                       -- INIT (scanRightSep), halt sub-phase 2
      if sp = 2 then seam 1 0           -- → LOOPCHK, step left (SEP high → SEP low)
      else inGroup 0 (scanRightStep sp c0 b)
    else if g = 1 then                  -- LOOPCHK (loopCtrl), halt sub-phase 2, bit in c0
      if sp = 2 then (if c0 then seam 2 1 else seam 8 1)   -- counter → REPA ; done → RRES
      else inGroup 1 (loopStep sp c0 b)
    else if g = 2 then                  -- REPA: walk right to the a₀ shift dest (3 steps)
      if sp = 0 then ((2, 1, c0, c1), none, 1)
      else if sp = 1 then ((2, 2, c0, c1), none, 1)
      else seam 3 1
    else if g = 3 then                  -- SHA (rendShift, delete a₀), halt sub-phase 8
      if sp = 8 then seam 4 0 else inGroup 3 (rendStep sp c0 c1 b)
    else if g = 4 then                  -- RANCH1 (scanLeftSep, REND → SEP), halt sub-phase 2
      if sp = 2 then seam 5 0 else inGroup 4 (scanLeftStep sp c0 b)
    else if g = 5 then                  -- REPB: walk left to the counter shift dest (2 steps)
      if sp = 0 then ((5, 1, c0, c1), none, 0)
      else seam 6 0
    else if g = 6 then                  -- SHB (rendShift, delete counter), halt sub-phase 8
      if sp = 8 then seam 7 0 else inGroup 6 (rendStep sp c0 c1 b)
    else if g = 7 then                  -- RANCH2 (scanLeftSep, REND → SEP), halt sub-phase 2
      if sp = 2 then seam 1 0 else inGroup 7 (scanLeftStep sp c0 b)   -- loop-back → LOOPCHK
    else if g = 8 then                  -- RRES (readRes, read a_v), halt sub-phase 3
      if sp = 3 then seam 9 2 else inGroup 8 (readResStep sp c0 b)
    else ((9, sp, c0, c1), none, 2)     -- HALT (idempotent)
  accept := fun s => s.2.2.1

/-- **Forced init** — the master copies the input with the fixed start state and head `0`; no free-init cheat. -/
theorem master_forced_init (x : List Bool) : init masterM x = ⟨(0, 0, false, false), 0, x⟩ := rfl

/-- The state is finite (non-vacuity: a product of `Fin`/`Bool`). -/
example : Fintype masterM.State := inferInstance

/-- The master halts exactly in the `HALT` group. -/
theorem master_halt_iff (s : masterM.State) : masterM.halt s = true ↔ s.1 = 9 := by
  simp [masterM]

end PallLean.Paper93.DeepMath.PathB.CookLevinMaster
