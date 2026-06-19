import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMWalkLeftK

/-!
# Entry 363 — universal-TM-table build: the copy-and-return body `copyBitReturn` (proved)

The apply phase transplants a whole field by copying it cell by cell.  `copyBit` (entry 360) copies one cell across a
gap but leaves the head *past* the destination; to copy the next source cell the head must return.  `copyBitReturn`
composes the copy with the `walkLeftK` (entry 362) return trip into the **loop body** of a block copy: it copies cell
`j` to cell `j+m` and repositions the head at the *next* source cell `j+1`.

This is the first composite of the apply phase — the verified iteration unit a field copy loops.

## What is proved (clean axioms, no `sorry`)

* **`copyBitReturn m s sT0 sF0 E`** — `copyBit m s sT0 sF0 E ++ walkLeftK m E`: copy cell `j` to `j+m`, then walk `m`
  cells back left to the next source cell.
* **`copyBitReturn_run`** (PROVED) — `∃ tp', reachIn (toNTM (copyBitReturn m s sT0 sF0 E)) (2*m+2) (s, j, tp)
  (E+m, j+1, tp') ∧ tp'.getD (j+m) false = tp.getD j false ∧ ∀ q, q ≠ j+m → tp'.getD q false = tp.getD q false`: the
  body runs `2m+2` steps to `(E+m, j+1, tp')`, with cell `j+m` now holding cell `j`'s value, every other cell unchanged,
  and the head back at the next source cell.

## Honest scope

This is the **copy-and-return body** — one iteration of a block copy (copy a cell across the gap, return for the next).
It does **not** yet loop the body over a whole field (the block copy), nor assemble the full apply, nor the rule-table
scan-and-match loop.  Building those fragment by fragment is the genuine remaining construction, **not faked**.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCopyBitReturn

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMachine toNTM)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCopyBit (copyBit copyBit_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMWalkLeftK (walkLeftK walkLeftK_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompose (reachIn_seq)

/-- **The copy-and-return body.**  Copy cell `j` to cell `j+m` (`copyBit`), then walk `m` cells back left to the next
source cell `j+1` (`walkLeftK`). -/
def copyBitReturn (m s sT0 sF0 E : ℕ) : TMachine :=
  copyBit m s sT0 sF0 E ++ walkLeftK m E

/-- **The copy-and-return body run (PROVED).**  `copyBitReturn m s sT0 sF0 E` runs `2m+2` steps from `(s, j, tp)` to
`(E+m, j+1, tp')`, with cell `j+m` now holding cell `j`'s value, every other cell unchanged, and the head back at the
next source cell `j+1`. -/
theorem copyBitReturn_run (m s sT0 sF0 E j : ℕ) (tp : List Bool) :
    ∃ tp', reachIn (toNTM (copyBitReturn m s sT0 sF0 E)) (2 * m + 2) (s, j, tp) (E + m, j + 1, tp') ∧
      tp'.getD (j + m) false = tp.getD j false ∧
      ∀ q, q ≠ j + m → tp'.getD q false = tp.getD q false := by
  obtain ⟨tp1, runCopy, hTarget, hOther⟩ := copyBit_run m s sT0 sF0 E j tp
  obtain ⟨tp2, runWalk, pWalk⟩ := walkLeftK_run m E (j + m + 1) tp1
  refine ⟨tp2, ?_, ?_, ?_⟩
  · have comp := reachIn_seq (copyBit m s sT0 sF0 E) (walkLeftK m E) (m + 2) m _ _ _ runCopy runWalk
    convert comp using 1
    · omega
    · rw [Prod.mk.injEq, Prod.mk.injEq]; exact ⟨rfl, by omega, rfl⟩
  · rw [pWalk (j + m)]; exact hTarget
  · intro q hq; rw [pWalk q]; exact hOther q hq

/-!
**The copy-and-return body, proved.**  `copyBitReturn` copies one cell across the gap and returns the head to the next
source cell — the verified iteration unit of a block copy.  Next: loop the body over a whole field (the block copy),
then the full apply (transplant the matched rule's new state and symbol), then the rule-table loop — fragment by
verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCopyBitReturn

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCopyBitReturn.copyBitReturn_run
