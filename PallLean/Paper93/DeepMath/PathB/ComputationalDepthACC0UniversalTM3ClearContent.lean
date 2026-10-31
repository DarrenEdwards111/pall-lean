import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3Walk

/-!
# Entry 429 — universal-TM-table build: the clearer's content `clearBlock_getD_outside` / `_inside` (proved)

The state update must clear the old configuration field before transferring the new one (entry 428).  For that we need to
know the *effect* of the clearer (`walkRightClearField3` / `clearBlock`, entry 418): which cells it changes and which it
leaves alone.  This brick proves that — the clearer-correctness lemmas, the dual of the writer-correctness lemma
(`writeFieldBlock_eq_encode`, entry 424).

* Cells **outside** the cleared region `[h, h+m)` are preserved.
* Cells **inside** `[h, h+m)` become `O`.

Crucially, the "outside preserved" direction is exactly what shows a *distant* field (e.g. the rule's new-state field)
survives clearing the config field.

## What is proved (clean axioms, no `sorry`)

* **`clearBlock_getD_outside`** (PROVED) — `j < h ∨ h+m ≤ j ⇒ (clearBlock tp h m).getD j O = tp.getD j O`.
* **`clearBlock_getD_inside`** (PROVED) — `h ≤ j → j < h+m ⇒ (clearBlock tp h m).getD j O = O`.

## Honest scope

These are the **clearer-correctness** content lemmas — they characterise `clearBlock`'s effect.  They do **not** by
themselves assemble the clear-then-transfer state update, nor `EmitsEncodedStep3`.  Building those fragment by fragment is
the genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ClearContent

open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 writeAt3 writeAt3_getD)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Walk (clearBlock)

/-- **The clearer preserves cells outside the field (PROVED).** -/
theorem clearBlock_getD_outside (tp : List Sym3) (h m j : ℕ) (hj : j < h ∨ h + m ≤ j) :
    (clearBlock tp h m).getD j Sym3.O = tp.getD j Sym3.O := by
  induction m generalizing h tp with
  | zero => rfl
  | succ m ih =>
      show (clearBlock (writeAt3 tp h Sym3.O) (h + 1) m).getD j Sym3.O = tp.getD j Sym3.O
      rw [ih (writeAt3 tp h Sym3.O) (h + 1) (by omega), writeAt3_getD, if_neg (by omega)]

/-- **The clearer clears cells inside the field (PROVED).** -/
theorem clearBlock_getD_inside (tp : List Sym3) (h m j : ℕ) (hge : h ≤ j) (hlt : j < h + m) :
    (clearBlock tp h m).getD j Sym3.O = Sym3.O := by
  induction m generalizing h tp with
  | zero => omega
  | succ m ih =>
      show (clearBlock (writeAt3 tp h Sym3.O) (h + 1) m).getD j Sym3.O = Sym3.O
      rcases Nat.lt_or_ge j (h + 1) with hj1 | hj1
      · have hjh : j = h := by omega
        subst hjh
        rw [clearBlock_getD_outside (writeAt3 tp j Sym3.O) (j + 1) m j (Or.inl (by omega)),
          writeAt3_getD, if_pos rfl]
      · exact ih (writeAt3 tp h Sym3.O) (h + 1) hj1 (by omega)

/-!
**The clearer's content, proved.**  `clearBlock_getD_outside`/`_inside` characterise the clearer's effect — outside the
field preserved, inside cleared to `O`.  The outside direction shows a distant field survives clearing the config field.
Next: the clear-then-transfer state update, and `EmitsEncodedStep3` — fragment by verified fragment, not faked.  Not a
separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ClearContent

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ClearContent.clearBlock_getD_outside
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ClearContent.clearBlock_getD_inside
