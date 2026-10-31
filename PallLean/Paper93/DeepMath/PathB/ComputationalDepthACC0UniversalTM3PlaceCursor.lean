import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3Move

/-!
# Entry 488 — generic scan loop: cursor placement `placeCursor` (proved)

The two-cursor comparison machines (entries 472–483) operate on the *canonical* tape `cursTape` — the base field tape with a
marker `M` written at the cursor cell.  To run them on the real rule table, those cursors must first be **placed**: write `M`
on a field cell (an `I`).  This brick is that one-step primitive — the inverse of the cursor erase (`eraseMark3`, 482).

`placeCursor s s' := [((s, I), (s', M, stay))]`.

## What is proved (clean axioms, no `sorry`)

* **`placeCursor s s'`** — at an `I` cell, write `M` and go to `s'`.
* **`placeCursor_run`** (PROVED) — `tp.getD j O = I → reachIn (toNTM3 (placeCursor s s')) 1 (s, j, tp) (s', j, writeAt3 tp
  j M)` — the cursor is placed (the cell `I → M`).

## Honest scope

This is the **cursor-placement** primitive (comparison setup).  It does **not** assemble the full record comparison, wire
it into the scan loop, build the generic apply, nor a fixed `U` / `EmitsEncodedStepEx3`.  Building those fragment by fragment
is the genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3PlaceCursor

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (Move moveHead)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym
  (Sym3 TMachine3 concreteStep3 readSym3 writeAt3 applyTrans3 toNTM3)

/-- **Place a cursor.**  At an `I` cell, write the marker `M` and go to `s'`. -/
def placeCursor (s s' : ℕ) : TMachine3 := [((s, Sym3.I), (s', Sym3.M, (2 : Move)))]

/-- **The cursor placement (PROVED).** -/
theorem placeCursor_run (s s' j : ℕ) (tp : List Sym3) (hI : tp.getD j Sym3.O = Sym3.I) :
    reachIn (toNTM3 (placeCursor s s')) 1 (s, j, tp) (s', j, writeAt3 tp j Sym3.M) := by
  refine ⟨(s', j, writeAt3 tp j Sym3.M), ?_, rfl⟩
  have hIr : readSym3 (s, j, tp) = Sym3.I := hI
  exact ⟨((s, Sym3.I), (s', Sym3.M, (2 : Move))), by simp [placeCursor], by simp [hIr],
    by simp [applyTrans3, moveHead]⟩

/-!
**Cursor placement, proved.**  `placeCursor` writes a comparison cursor onto a field cell — the setup step that turns the
real rule table into the canonical `cursTape` the comparison machines consume.  Next: place both cursors and run the full
record comparison, then wire it into the scan loop — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3PlaceCursor

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3PlaceCursor.placeCursor_run
