import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMCopyBitReturn

/-!
# Entry 364 — universal-TM-table build: the single-base copy step `copyStep` (proved)

`copyBitReturn` (entry 363) is the copy-and-return body, but it takes four separate state arguments
(`s, sT0, sF0, E`).  To *loop* it — chaining one iteration's exit state into the next iteration's entry state — we fix
the internal states relative to a single base `s`, so the body has one entry state `s` and one exit state `s + 3m+3`.

`copyStep m s` lays the internal states out disjointly: the carry tracks at `s+1` and `s+m+2`, the write/converge state
at `s+2m+3`, and the return walk over `s+2m+3 … s+3m+3`.  It copies cell `j` to cell `j+m` and returns the head to
`j+1`, ending in the single state `s + 3m+3` — the loopable unit of a block copy.

## What is proved (clean axioms, no `sorry`)

* **`copyStep m s`** — `copyBitReturn m s (s+1) (s+m+2) (s+2*m+3)`.
* **`copyStep_run`** (PROVED) — `∃ tp', reachIn (toNTM (copyStep m s)) (2*m+2) (s, j, tp) (s+3*m+3, j+1, tp') ∧
  tp'.getD (j+m) false = tp.getD j false ∧ ∀ q, q ≠ j+m → tp'.getD q false = tp.getD q false`: the step runs `2m+2`
  steps from the single entry state `s` to the single exit state `s+3m+3`, copying cell `j` to `j+m` and returning the
  head to `j+1`.

## Honest scope

This is the **single-base copy step** — `copyBitReturn` repackaged with one entry and one exit state, the loopable unit.
It does **not** yet loop over a field (the block copy, with its region-disjointness invariant), nor the full apply, nor
the rule-table scan-and-match loop.  Building those fragment by fragment is the genuine remaining construction, **not
faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCopyStep

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMachine toNTM)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCopyBitReturn (copyBitReturn copyBitReturn_run)

/-- **The single-base copy step.**  `copyBitReturn` with its internal states fixed relative to the base `s`: carry
tracks at `s+1`, `s+m+2`, write/converge at `s+2m+3`, return walk ending at `s+3m+3`. -/
def copyStep (m s : ℕ) : TMachine :=
  copyBitReturn m s (s + 1) (s + m + 2) (s + 2 * m + 3)

/-- **The single-base copy step run (PROVED).**  `copyStep m s` runs `2m+2` steps from the single entry state `s` to
the single exit state `s+3m+3`, copying cell `j` to `j+m` and returning the head to `j+1`. -/
theorem copyStep_run (m s j : ℕ) (tp : List Bool) :
    ∃ tp', reachIn (toNTM (copyStep m s)) (2 * m + 2) (s, j, tp) (s + 3 * m + 3, j + 1, tp') ∧
      tp'.getD (j + m) false = tp.getD j false ∧
      ∀ q, q ≠ j + m → tp'.getD q false = tp.getD q false := by
  obtain ⟨tp', hr, ht, ho⟩ := copyBitReturn_run m s (s + 1) (s + m + 2) (s + 2 * m + 3) j tp
  rw [show (s + 2 * m + 3) + m = s + 3 * m + 3 from by omega] at hr
  exact ⟨tp', hr, ht, ho⟩

/-!
**The single-base copy step, proved.**  `copyStep m s` has one entry state `s` and one exit state `s+3m+3`, so a block
copy can chain it (each iteration's exit feeding the next iteration's entry).  Next: the block copy (loop `copyStep`
over a field with the region-disjointness invariant), the full apply, and the rule-table loop — fragment by verified
fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCopyStep

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCopyStep.copyStep_run
