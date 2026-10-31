import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3TestBit

/-!
# Entry 401 — universal-TM-table build: the n-step right move `moveRightN3` (proved)

The marker match (entry 399 onward) shuttles the head between a config-key cell and a rule-key cell at a *data-dependent*
distance.  The return trip is distance-independent (`seekMarkLeft` finds the marker), but the outbound trip moves a
definite number of cells `d`.  This brick is that outbound move: a **corridor** of `n` states, each writing back its
cell and stepping right, leaving the tape identical.

## What is proved (clean axioms, no `sorry`)

* **`moveRightN3 s n`** — recursively `[] ↦ []`, `n+1 ↦ moveRight3 s (s+1) ++ moveRightN3 (s+1) n`: a corridor advancing
  the control state by `1` per cell.
* **`moveRightN3_run`** (PROVED) — `j + n ≤ tp.length ⇒ reachIn (toNTM3 (moveRightN3 s n)) n (s, j, tp) (s+n, j+n, tp)`:
  `n` rightward steps from state `s`/head `j` to state `s+n`/head `j+n`, tape identical (each intermediate cell is in
  bounds, so each write-back is the identity).

## Honest scope

This is the **bounded right move** — the outbound leg of the marker shuttle.  It does **not** yet compare, nor restore, nor
loop the match.  Building those fragment by fragment is the genuine remaining construction, **not faked**.  Nothing here
is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MoveN

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 toNTM3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Move (moveRight3 moveRight3_run_eq)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_seq3)

/-- **The n-step right-move corridor.**  Advance the control state by `1` per rightward cell. -/
def moveRightN3 (s : ℕ) : ℕ → TMachine3
  | 0 => []
  | (n + 1) => moveRight3 s (s + 1) ++ moveRightN3 (s + 1) n

/-- **The n-step right move run (PROVED).**  `moveRightN3 s n` advances head `j → j+n` and state `s → s+n` in `n` steps,
tape identical, provided the whole stretch is in bounds. -/
theorem moveRightN3_run (s n j : ℕ) (tp : List Sym3) (hbound : j + n ≤ tp.length) :
    reachIn (toNTM3 (moveRightN3 s n)) n (s, j, tp) (s + n, j + n, tp) := by
  induction n generalizing s j with
  | zero => exact rfl
  | succ n ih =>
      have run1 := moveRight3_run_eq s (s + 1) j tp (by omega)
      have run2 := ih (s + 1) (j + 1) (by omega)
      have comp := reachIn_seq3 _ _ _ _ _ _ _ run1 run2
      rw [show (1 : ℕ) + n = n + 1 from by omega, show s + 1 + n = s + (n + 1) from by omega,
        show j + 1 + n = j + (n + 1) from by omega] at comp
      exact comp

/-!
**The bounded right move, proved.**  `moveRightN3 s n` is the outbound leg of the marker shuttle, advancing the head a
definite `n` cells list-preservingly.  Next: chain `markCarry3 → moveRightN3 → testBit3 → seekMarkLeft → unmark3` into a
distance-independent single-bit compare — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MoveN

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MoveN.moveRightN3_run
