import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMCopyBlock

/-!
# Entry 366 — universal-TM-table build: the head-neutral block copy `copyBlockReturn` (proved)

`copyBlock` (entry 365) transplants a field but leaves the head advanced past the source (at `j+L`).  The apply phase
performs *several* field operations, so it is convenient for a field copy to leave the head where it started.
`copyBlockReturn` composes the block copy with a `walkLeftK` (entry 362) return of `L` cells, so the head ends back at
the source start `j` — the field-level analog of `copyBitReturn` (entry 363).

## What is proved (clean axioms, no `sorry`)

* **`copyBlockReturn m L s`** — `copyBlock m L s ++ walkLeftK L (s + L * (3*m+3))`.
* **`copyBlockReturn_run`** (PROVED) — for `L ≤ m`,
  `∃ tp', reachIn (toNTM (copyBlockReturn m L s)) (L*(2*m+2) + L) (s, j, tp) (s + L*(3*m+3) + L, j, tp') ∧
  (∀ i < L, tp'.getD (j+m+i) false = tp.getD (j+i) false) ∧ (∀ q < j+m, tp'.getD q false = tp.getD q false)`: the
  head-neutral block copy runs `L*(2m+2)+L` steps, the destination block mirrors the source, everything before the
  destination is unchanged, and the head is back at the source start `j`.

## Honest scope

This is the **head-neutral block copy** — a field transplant that returns the head, so apply-phase field operations
compose from a common base.  It does **not** yet assemble the full apply (rewrite the configuration per the matched
rule), nor the rule-table scan-and-match loop.  Building those fragment by fragment is the genuine remaining
construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCopyBlockReturn

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMachine toNTM)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCopyBlock (copyBlock copyBlock_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMWalkLeftK (walkLeftK walkLeftK_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompose (reachIn_seq)

/-- **The head-neutral block copy.**  Copy the field (`copyBlock`), then walk `L` cells back left (`walkLeftK`) so the
head ends at the source start. -/
def copyBlockReturn (m L s : ℕ) : TMachine :=
  copyBlock m L s ++ walkLeftK L (s + L * (3 * m + 3))

/-- **The head-neutral block copy run (PROVED).**  For `L ≤ m`, `copyBlockReturn m L s` runs `L*(2m+2)+L` steps from
`(s, j, tp)` to `(s + L*(3m+3) + L, j, tp')`, with the destination block mirroring the source, everything before the
destination unchanged, and the head back at the source start `j`. -/
theorem copyBlockReturn_run (m L s j : ℕ) (tp : List Bool) (hL : L ≤ m) :
    ∃ tp', reachIn (toNTM (copyBlockReturn m L s)) (L * (2 * m + 2) + L) (s, j, tp)
        (s + L * (3 * m + 3) + L, j, tp') ∧
      (∀ i, i < L → tp'.getD (j + m + i) false = tp.getD (j + i) false) ∧
      (∀ q, q < j + m → tp'.getD q false = tp.getD q false) := by
  obtain ⟨tp1, runB, hcopy, hbef⟩ := copyBlock_run m L s j tp hL
  obtain ⟨tp2, runW, pW⟩ := walkLeftK_run L (s + L * (3 * m + 3)) (j + L) tp1
  refine ⟨tp2, ?_, ?_, ?_⟩
  · have comp := reachIn_seq (copyBlock m L s) (walkLeftK L (s + L * (3 * m + 3)))
      (L * (2 * m + 2)) L _ _ _ runB runW
    convert comp using 1
    rw [Prod.mk.injEq, Prod.mk.injEq]; exact ⟨by omega, by omega, rfl⟩
  · intro i hi; rw [pW (j + m + i)]; exact hcopy i hi
  · intro q hq; rw [pW q]; exact hbef q hq

/-!
**The head-neutral block copy, proved.**  `copyBlockReturn` transplants a field and returns the head to the source
start, so apply-phase field operations compose from a common base.  Next: the full apply (rewrite the configuration's
state and symbol per the matched rule, sequencing copies/writes), then the rule-table scan-and-match loop — fragment by
verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCopyBlockReturn

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCopyBlockReturn.copyBlockReturn_run
