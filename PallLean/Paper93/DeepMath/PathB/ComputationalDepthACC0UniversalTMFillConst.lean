import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMCopyBit

/-!
# Entry 361 — universal-TM-table build: the constant block fill `fillConst` (proved)

`writeConst` (entry 359) overwrites *one* cell.  The apply phase often overwrites a whole *block* — e.g. clearing or
setting a known-length field.  `fillConst b L s` overwrites the `L` cells starting at the head with the constant `b`,
walking right, through the states `s, …, s+L`.  It is the write-side analog of `walkRightK` (entry 357): a `reachIn_seq`
fold of `writeConst`s.

## What is proved (clean axioms, no `sorry`)

* **`fillConst b L s`** — recursively, `0 ↦ []` and `L+1 ↦ writeConst b s (s+1) ++ fillConst b L (s+1)`: one
  `writeConst` per cell.
* **`fillConst_run`** (PROVED) — `∃ tp', reachIn (toNTM (fillConst b L s)) L (s, h, tp) (s+L, h+L, tp') ∧
  (∀ i < L, tp'.getD (h+i) false = b) ∧ (∀ q < h, tp'.getD q false = tp.getD q false) ∧
  (∀ q, h+L ≤ q → tp'.getD q false = tp.getD q false)`: the fill runs `L` steps to state `s+L` at head `h+L`, with the
  block `[h, h+L)` now holding `b` and every cell outside it unchanged.

## Honest scope

This is the **constant block fill** — overwriting a known-length region with a constant, fully specified (block set,
outside untouched).  It does **not** yet assemble the full apply (transplant the matched rule's new state and symbol
into the configuration, which combines `copyBit`/`fillConst`), nor the rule-table scan-and-match loop.  Building those
fragment by fragment is the genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMFillConst

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMachine toNTM writeAt)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanNat (writeAt_getD)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMWriteConst (writeConst writeConst_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompose (reachIn_seq)

/-- **The constant block fill.**  One `writeConst b` per cell; from `s` it overwrites `L` cells with `b`, reaching
`s+L`. -/
def fillConst (b : Bool) : ℕ → ℕ → TMachine
  | 0, _ => []
  | L + 1, s => writeConst b s (s + 1) ++ fillConst b L (s + 1)

/-- **The constant block fill run (PROVED).**  `fillConst b L s` runs `L` steps from `(s, h, tp)` to `(s+L, h+L, tp')`,
with the block `[h, h+L)` set to `b` and every cell outside it unchanged. -/
theorem fillConst_run (b : Bool) (L s h : ℕ) (tp : List Bool) :
    ∃ tp', reachIn (toNTM (fillConst b L s)) L (s, h, tp) (s + L, h + L, tp') ∧
      (∀ i, i < L → tp'.getD (h + i) false = b) ∧
      (∀ q, q < h → tp'.getD q false = tp.getD q false) ∧
      (∀ q, h + L ≤ q → tp'.getD q false = tp.getD q false) := by
  induction L generalizing s h tp with
  | zero =>
      exact ⟨tp, rfl, fun i hi => absurd hi (Nat.not_lt_zero i), fun q _ => rfl, fun q _ => rfl⟩
  | succ L ih =>
      have runC := writeConst_run b s (s + 1) h tp
      obtain ⟨tp2, run2, hwr2, hbef2, haft2⟩ := ih (s + 1) (h + 1) (writeAt tp h b)
      refine ⟨tp2, ?_, ?_, ?_, ?_⟩
      · have comp := reachIn_seq (writeConst b s (s + 1)) (fillConst b L (s + 1)) 1 L _ _ _ runC run2
        convert comp using 1
        · omega
        · rw [Prod.mk.injEq, Prod.mk.injEq]; exact ⟨by omega, by omega, rfl⟩
      · intro i hi
        cases i with
        | zero => rw [Nat.add_zero, hbef2 h (Nat.lt_succ_self h), writeAt_getD, if_pos rfl]
        | succ i' =>
            rw [show h + (i' + 1) = (h + 1) + i' from by omega]
            exact hwr2 i' (by omega)
      · intro q hq
        rw [hbef2 q (by omega), writeAt_getD, if_neg (by omega)]
      · intro q hq
        rw [haft2 q (by omega), writeAt_getD, if_neg (by omega)]

/-!
**The constant block fill, proved.**  `fillConst b L s` overwrites a known-length region with a constant, fully
specified (the block holds `b`, everything outside is untouched) — the write-side analog of `walkRightK`.  Next: the
full apply (transplant the matched rule's new state and symbol into the configuration, combining `copyBit`/`fillConst`),
then the rule-table scan-and-match loop — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMFillConst

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMFillConst.fillConst_run
