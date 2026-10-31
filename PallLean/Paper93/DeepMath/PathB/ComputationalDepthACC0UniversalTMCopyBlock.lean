import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMCopyStep

/-!
# Entry 365 — universal-TM-table build: the block copy `copyBlock` (proved)

`copyStep` (entry 364) copies one cell across the gap and returns for the next.  The apply phase transplants a whole
*field* — a block of `L` cells.  `copyBlock m L s` loops `copyStep` `L` times (each iteration's exit state feeding the
next, shifting the state base by `3m+3` per step), copying the source block `[j, j+L)` to the destination block
`[j+m, j+m+L)`.

Correctness needs the **region-disjointness invariant `L ≤ m`**: the destination `[j+m, j+m+L)` must not overlap the
source `[j, j+L)` (which holds iff `m ≥ L`), so each iteration reads the *original* source cell rather than a cell an
earlier iteration already overwrote.

## What is proved (clean axioms, no `sorry`)

* **`copyBlock m L s`** — recursively, `0 ↦ []` and `L+1 ↦ copyStep m s ++ copyBlock m L (s + (3*m+3))`.
* **`copyBlock_run`** (PROVED) — for `L ≤ m`,
  `∃ tp', reachIn (toNTM (copyBlock m L s)) (L*(2*m+2)) (s, j, tp) (s + L*(3*m+3), j+L, tp') ∧
  (∀ i < L, tp'.getD (j+m+i) false = tp.getD (j+i) false) ∧ (∀ q < j+m, tp'.getD q false = tp.getD q false)`: the block
  copy runs `L*(2m+2)` steps, the destination block `[j+m, j+m+L)` now mirrors the source block `[j, j+L)`, and every
  cell before the destination (in particular the whole source) is unchanged.

## Honest scope

This is the **block copy** — transplanting a contiguous field, with its region-disjointness invariant.  It does **not**
yet assemble the full apply (combine block copies and `writeConst`s to rewrite the configuration per the matched rule),
nor the rule-table scan-and-match loop.  Building those fragment by fragment is the genuine remaining construction,
**not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCopyBlock

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMachine toNTM)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCopyStep (copyStep copyStep_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompose (reachIn_seq)

/-- **The block copy.**  Loop `copyStep` `L` times, shifting the state base by `3m+3` per iteration; copies the source
block `[j, j+L)` to the destination block `[j+m, j+m+L)`. -/
def copyBlock (m : ℕ) : ℕ → ℕ → TMachine
  | 0, _ => []
  | L + 1, s => copyStep m s ++ copyBlock m L (s + (3 * m + 3))

/-- **The block copy run (PROVED).**  For `L ≤ m`, `copyBlock m L s` runs `L*(2m+2)` steps from `(s, j, tp)` to
`(s + L*(3m+3), j+L, tp')`, with the destination block `[j+m, j+m+L)` mirroring the source block `[j, j+L)` and every
cell before the destination unchanged. -/
theorem copyBlock_run (m : ℕ) : ∀ (L s j : ℕ) (tp : List Bool), L ≤ m →
    ∃ tp', reachIn (toNTM (copyBlock m L s)) (L * (2 * m + 2)) (s, j, tp)
        (s + L * (3 * m + 3), j + L, tp') ∧
      (∀ i, i < L → tp'.getD (j + m + i) false = tp.getD (j + i) false) ∧
      (∀ q, q < j + m → tp'.getD q false = tp.getD q false) := by
  intro L
  induction L with
  | zero =>
      intro s j tp _
      refine ⟨tp, ?_, fun i hi => absurd hi (Nat.not_lt_zero i), fun q _ => rfl⟩
      simp only [Nat.zero_mul, Nat.add_zero]
      rfl
  | succ L ih =>
      intro s j tp hL
      obtain ⟨tp1, run1, hT1, hO1⟩ := copyStep_run m s j tp
      obtain ⟨tp2, run2, hcopy2, hbef2⟩ := ih (s + (3 * m + 3)) (j + 1) tp1 (by omega)
      refine ⟨tp2, ?_, ?_, ?_⟩
      · have comp := reachIn_seq (copyStep m s) (copyBlock m L (s + (3 * m + 3)))
          (2 * m + 2) (L * (2 * m + 2)) _ _ _ run1 run2
        convert comp using 1
        · rw [add_mul, one_mul]; omega
        · rw [Prod.mk.injEq, Prod.mk.injEq]
          refine ⟨?_, ?_, rfl⟩
          · rw [add_mul, one_mul]; omega
          · omega
      · intro i hi
        cases i with
        | zero =>
            rw [Nat.add_zero, Nat.add_zero, hbef2 (j + m) (by omega)]
            exact hT1
        | succ i' =>
            rw [show j + m + (i' + 1) = (j + 1) + m + i' from by omega,
              hcopy2 i' (by omega), hO1 ((j + 1) + i') (by omega)]
            congr 1
            omega
      · intro q hq
        rw [hbef2 q (by omega), hO1 q (by omega)]

/-!
**The block copy, proved.**  `copyBlock m L s` (for `L ≤ m`) transplants the source field `[j, j+L)` to the destination
`[j+m, j+m+L)`, leaving the source — and everything before the destination — untouched.  The region-disjointness `L ≤ m`
is what lets each iteration read the original source.  Next: the full apply (combine block copies and `writeConst`s to
rewrite the configuration per the matched rule), then the rule-table scan-and-match loop — fragment by verified
fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCopyBlock

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCopyBlock.copyBlock_run
