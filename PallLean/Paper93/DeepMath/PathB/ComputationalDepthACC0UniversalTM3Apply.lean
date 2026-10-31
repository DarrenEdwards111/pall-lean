import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3HeadMove

/-!
# Entry 421 — universal-TM-table build: the apply tape step `applyStep3` (proved)

This assembles the **tape transformation of one simulated step** under the marker-on-current-cell head representation
(entries 419/420): write the rule's symbol at the current cell, then move the head per the rule's direction.  With the
marker `M` at `q` (current cell `q+1`), the three directions are:

* **stay** (`writeSymAtHead3`): write `w` at the current cell `q+1`, head back at the marker `q`.
* **right** (`moveRightWrite3`): the combined "write `w`, move right" — result `q ← w`, `q+1 ← M` (TM-correct: after
  writing the head cell and stepping right, the written symbol sits just left of the new head).
* **left** (`moveLeftWrite3`): write `w` at `q+1`, then the local left head move (`headMoveLeft3`, entry 419).

Each is built from the proven single-cell machines and chained with `reachIn_seq3`.

## What is proved (clean axioms, no `sorry`)

* **`writeSymAtHead3 s sOut w`** / **`writeSymAtHead3_run`** (PROVED) — `q+1 < tp.length` ⇒ `∃ N, reachIn N (s, q, tp)
  (sOut, q, writeAt3 tp (q+1) w)`.
* **`moveRightWrite3 s sOut w`** / **`moveRightWrite3_run`** (PROVED) — `q+1 < tp.length` ⇒ `∃ N, reachIn N (s, q, tp)
  (sOut, q+1, writeAt3 (writeAt3 tp q w) (q+1) M)`.
* **`moveLeftWrite3 s sOut w`** / **`moveLeftWrite3_run`** (PROVED) — `1 ≤ q`, `q+1 < tp.length`, `tp[q-1] ∈ {O,I}` ⇒
  `∃ N, reachIn N (s, q, tp) (sOut, q-1, writeAt3 (writeAt3 (writeAt3 tp (q+1) w) q (tp.getD (q-1) O)) (q-1) M)`.

## Honest scope

This is the **apply tape step** — the symbol write and head move of one simulated step.  It does **not** yet update the
simulated *state* field, nor wire the write symbol / direction from the matched rule, nor assemble `EmitsEncodedStep3`.
Building those fragment by fragment is the genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Apply

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 toNTM3 writeAt3 writeAt3_getD)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Move (moveRight3 moveRight3_run_eq)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Mark (moveLeft3 moveLeft3_run_eq)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Unmark (unmark3 unmark3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3HeadMove (headMoveLeft3 headMoveLeft3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_seq3)

/-- **Write the symbol at the current cell (stay).**  Step onto the current cell `q+1`, write `w`, return to the marker. -/
def writeSymAtHead3 (s sOut : ℕ) (w : Sym3) : TMachine3 :=
  moveRight3 s (s + 1) ++ unmark3 (s + 1) (s + 2) w ++ moveLeft3 (s + 2) sOut

/-- **The stay-write run (PROVED).**  Writes `w` at the current cell `q+1`, head back at the marker `q`. -/
theorem writeSymAtHead3_run (s sOut q : ℕ) (w : Sym3) (tp : List Sym3) (hq : q + 1 < tp.length) :
    ∃ N, reachIn (toNTM3 (writeSymAtHead3 s sOut w)) N (s, q, tp) (sOut, q, writeAt3 tp (q + 1) w) := by
  have h1 := moveRight3_run_eq s (s + 1) q tp (by omega)
  have h2 := unmark3_run (s + 1) (s + 2) w (q + 1) tp
  have hlen : (writeAt3 tp (q + 1) w).length = tp.length := by
    simp only [writeAt3, List.length_set, List.length_append, List.length_replicate]; omega
  have h3 := moveLeft3_run_eq (s + 2) sOut (q + 1) (writeAt3 tp (q + 1) w) (by rw [hlen]; omega)
  rw [show q + 1 - 1 = q from by omega] at h3
  have s12 := reachIn_seq3 (moveRight3 s (s + 1)) (unmark3 (s + 1) (s + 2) w) 1 1 _ _ _ h1 h2
  exact ⟨1 + 1 + 1, reachIn_seq3 (moveRight3 s (s + 1) ++ unmark3 (s + 1) (s + 2) w) (moveLeft3 (s + 2) sOut)
    (1 + 1) 1 _ _ _ s12 h3⟩

/-- **Write the symbol and move the head right.**  Write `w` at the marker cell, step right, mark the new cell. -/
def moveRightWrite3 (s sOut : ℕ) (w : Sym3) : TMachine3 :=
  unmark3 s (s + 1) w ++ moveRight3 (s + 1) (s + 2) ++ unmark3 (s + 2) sOut Sym3.M

/-- **The write-and-move-right run (PROVED).**  Result `q ← w`, `q+1 ← M`, head on the new marker. -/
theorem moveRightWrite3_run (s sOut q : ℕ) (w : Sym3) (tp : List Sym3) (hq : q + 1 < tp.length) :
    ∃ N, reachIn (toNTM3 (moveRightWrite3 s sOut w)) N (s, q, tp)
      (sOut, q + 1, writeAt3 (writeAt3 tp q w) (q + 1) Sym3.M) := by
  have h1 := unmark3_run s (s + 1) w q tp
  have hlen : (writeAt3 tp q w).length = tp.length := by
    simp only [writeAt3, List.length_set, List.length_append, List.length_replicate]; omega
  have h2 := moveRight3_run_eq (s + 1) (s + 2) q (writeAt3 tp q w) (by rw [hlen]; omega)
  have h3 := unmark3_run (s + 2) sOut Sym3.M (q + 1) (writeAt3 tp q w)
  have s12 := reachIn_seq3 (unmark3 s (s + 1) w) (moveRight3 (s + 1) (s + 2)) 1 1 _ _ _ h1 h2
  exact ⟨1 + 1 + 1, reachIn_seq3 (unmark3 s (s + 1) w ++ moveRight3 (s + 1) (s + 2)) (unmark3 (s + 2) sOut Sym3.M)
    (1 + 1) 1 _ _ _ s12 h3⟩

/-- **Write the symbol and move the head left.**  Write `w` at the current cell, then the local left head move. -/
def moveLeftWrite3 (s sOut : ℕ) (w : Sym3) : TMachine3 :=
  writeSymAtHead3 s (s + 3) w ++ headMoveLeft3 (s + 3) sOut

/-- **The write-and-move-left run (PROVED).**  The written symbol stays at `q+1` (right of the new head); the marker moves
to `q-1`. -/
theorem moveLeftWrite3_run (s sOut q : ℕ) (w : Sym3) (tp : List Sym3) (hq1 : 1 ≤ q) (hq : q + 1 < tp.length)
    (hcl : tp.getD (q - 1) Sym3.O = Sym3.O ∨ tp.getD (q - 1) Sym3.O = Sym3.I) :
    ∃ N, reachIn (toNTM3 (moveLeftWrite3 s sOut w)) N (s, q, tp)
      (sOut, q - 1, writeAt3 (writeAt3 (writeAt3 tp (q + 1) w) q (tp.getD (q - 1) Sym3.O)) (q - 1) Sym3.M) := by
  obtain ⟨N1, hw⟩ := writeSymAtHead3_run s (s + 3) q w tp hq
  have hlen : (writeAt3 tp (q + 1) w).length = tp.length := by
    simp only [writeAt3, List.length_set, List.length_append, List.length_replicate]; omega
  have hcl' : (writeAt3 tp (q + 1) w).getD (q - 1) Sym3.O = Sym3.O ∨
      (writeAt3 tp (q + 1) w).getD (q - 1) Sym3.O = Sym3.I := by rw [writeAt3_getD, if_neg (by omega)]; exact hcl
  obtain ⟨N2, hhl⟩ := headMoveLeft3_run (s + 3) sOut q (writeAt3 tp (q + 1) w) hcl' hq1 (by rw [hlen]; omega)
  rw [show (writeAt3 tp (q + 1) w).getD (q - 1) Sym3.O = tp.getD (q - 1) Sym3.O from by
    rw [writeAt3_getD, if_neg (by omega)]] at hhl
  exact ⟨N1 + N2, reachIn_seq3 (writeSymAtHead3 s (s + 3) w) (headMoveLeft3 (s + 3) sOut) N1 N2 _ _ _ hw hhl⟩

/-!
**The apply tape step, proved.**  `writeSymAtHead3` / `moveRightWrite3` / `moveLeftWrite3` realise the symbol write and head
move of one simulated step under the marker representation — the TM-step tape transformation.  Next: update the simulated
state field, wire the write symbol / move direction from the matched rule, and assemble `EmitsEncodedStep3` — fragment by
verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Apply

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Apply.writeSymAtHead3_run
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Apply.moveRightWrite3_run
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Apply.moveLeftWrite3_run
