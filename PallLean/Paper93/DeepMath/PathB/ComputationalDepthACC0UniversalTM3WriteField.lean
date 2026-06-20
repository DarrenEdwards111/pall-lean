import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3Unmark
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3Compose

/-!
# Entry 422 — universal-TM-table build: the unary-field writer `writeUnaryFieldN3` (proved)

Assembling the encoded next configuration (toward `EmitsEncodedStep3`) requires *writing* unary fields onto the tape — the
output dual of the field scanner (`scanNatFrom3`, entry 395) and clearer (`walkRightClearField3`, entry 418).  This brick
is that writer: it lays down `n` ones followed by an `O` separator, advancing the head, i.e. it writes `encodeNatBits3 n`
in place.

The construction is the obvious corridor: a step that writes `I` and moves right, repeated `n` times, then a final `O`
separator.

## What is proved (clean axioms, no `sorry`)

* **`writeIMove3 s s'`** / **`writeIMove3_run`** (PROVED) — write `I` at the head, move right: `reachIn 1 (s, j, tp) (s',
  j+1, writeAt3 tp j I)`.
* **`writeFieldBlock tp j n`** — `tp` with cells `j … j+n-1` set to `I` and cell `j+n` set to `O` (fold in loop order).
* **`writeUnaryFieldN3 s sOut n`** / **`writeUnaryFieldN3_run`** (PROVED) — `∃ N, reachIn N (s, j, tp) (sOut, j+n,
  writeFieldBlock tp j n)`: writes the unary field of length `n` at `j`, head ending on the separator.

## Honest scope

This is the **unary-field writer** — the output primitive for emitting encoded fields.  It writes a field of a *given*
length; the simulated *state* update transfers a field whose length is read from the matched rule (a data-dependent copy,
entry 415, after clearing the old field, entry 418).  Wiring those and `EmitsEncodedStep3` is the genuine remaining
construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3WriteField

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (Move moveHead)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym
  (Sym3 TMachine3 concreteStep3 readSym3 toNTM3 writeAt3 applyTrans3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Unmark (unmark3 unmark3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_seq3)

/-- **The write-one step.**  Write `I` at the head, move right, go to `s'`. -/
def writeIMove3 (s s' : ℕ) : TMachine3 :=
  [((s, Sym3.O), (s', Sym3.I, (1 : Move))), ((s, Sym3.I), (s', Sym3.I, (1 : Move))),
   ((s, Sym3.M), (s', Sym3.I, (1 : Move)))]

/-- **The write-one step (PROVED), uniformly in the read symbol.** -/
theorem writeIMove3_step (s s' j : ℕ) (tp : List Sym3) :
    concreteStep3 (writeIMove3 s s') (s, j, tp) (s', j + 1, writeAt3 tp j Sym3.I) := by
  rcases h : readSym3 (s, j, tp) with _ | _ | _
  · exact ⟨((s, Sym3.O), (s', Sym3.I, (1 : Move))), by simp [writeIMove3], by simp [h], by simp [applyTrans3, moveHead]⟩
  · exact ⟨((s, Sym3.I), (s', Sym3.I, (1 : Move))), by simp [writeIMove3], by simp [h], by simp [applyTrans3, moveHead]⟩
  · exact ⟨((s, Sym3.M), (s', Sym3.I, (1 : Move))), by simp [writeIMove3], by simp [h], by simp [applyTrans3, moveHead]⟩

/-- **The write-one run (PROVED).** -/
theorem writeIMove3_run (s s' j : ℕ) (tp : List Sym3) :
    reachIn (toNTM3 (writeIMove3 s s')) 1 (s, j, tp) (s', j + 1, writeAt3 tp j Sym3.I) :=
  ⟨_, writeIMove3_step s s' j tp, rfl⟩

/-- **The written field**, in loop order: write `I` at `j`, recurse on `j+1`; at `0`, write the `O` separator. -/
def writeFieldBlock (tp : List Sym3) (j : ℕ) : ℕ → List Sym3
  | 0 => writeAt3 tp j Sym3.O
  | (n + 1) => writeFieldBlock (writeAt3 tp j Sym3.I) (j + 1) n

/-- **The unary-field writer.**  Write `n` ones (advancing), then the separator `O`. -/
def writeUnaryFieldN3 (s sOut : ℕ) : ℕ → TMachine3
  | 0 => unmark3 s sOut Sym3.O
  | (n + 1) => writeIMove3 s (s + 1) ++ writeUnaryFieldN3 (s + 1) sOut n

/-- **The unary-field writer run (PROVED).**  Writes `encodeNatBits3 n` at `j`, head ending on the separator `j+n`. -/
theorem writeUnaryFieldN3_run (sOut n s j : ℕ) (tp : List Sym3) :
    ∃ N, reachIn (toNTM3 (writeUnaryFieldN3 s sOut n)) N (s, j, tp) (sOut, j + n, writeFieldBlock tp j n) := by
  induction n generalizing s j tp with
  | zero => exact ⟨1, unmark3_run s sOut Sym3.O j tp⟩
  | succ n ih =>
      have h1 := writeIMove3_run s (s + 1) j tp
      obtain ⟨N, hrec⟩ := ih (s + 1) (j + 1) (writeAt3 tp j Sym3.I)
      rw [show j + 1 + n = j + (n + 1) from by omega] at hrec
      exact ⟨1 + N, reachIn_seq3 (writeIMove3 s (s + 1)) (writeUnaryFieldN3 (s + 1) sOut n) 1 N _ _ _ h1 hrec⟩

/-!
**The unary-field writer, proved.**  `writeUnaryFieldN3` lays down a unary field of given length — the output primitive for
emitting encoded fields.  Next: transfer the simulated state from the matched rule (data-dependent copy + clear), wire the
apply data-flow, and assemble `EmitsEncodedStep3` — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3WriteField

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3WriteField.writeUnaryFieldN3_run
