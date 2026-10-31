import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3BitCompare

/-!
# Entry 411 — universal-TM-table build: the single-cell copy `copyBitAtDist3` (proved)

After the rule-table match (entry 410) finds the applicable transition, the *apply* phase copies the rule's right-hand
side into the configuration: the new state (a unary field), the write symbol, and a head move.  The conceptual core is a
**single-cell copy at a distance** — read a source cell and write its value into a destination cell `d` away — the
copy-side analogue of `bitCompareAtDist3` (entry 404).

The clean way to do it avoids markers entirely: *read the source bit without modifying it* (`readCarry3` writes the read
symbol straight back, branching the control state on its value), walk right `d` cells, write the carried bit at the
destination, then walk **back** the same fixed `d` cells (`moveLeftN3`) — no seek needed, because the return distance is
exactly `d`.  Only the destination cell changes; the source and head are left exactly as they were.

## What is proved (clean axioms, no `sorry`)

* **`moveLeftN3 s n`** — the `n`-step left-move corridor (mirror of `moveRightN3`); **`moveLeftN3_run`** (PROVED):
  `n ≤ j → j < tp.length → reachIn n (s, j, tp) (s+n, j-n, tp)`, tape identical.
* **`readCarry3 s sO sI`** — read the head cell, write it back, *stay*, branch to `sO`/`sI` on `O`/`I`; **`readCarry3_run_O`
  / `_I`** (PROVED): tape unchanged, head unchanged, control routed on the bit.
* **`copyArm3 s sOut d b`** / **`copyArm3_run`** (PROVED) — one lineage: go right `d`, write `b`, come back, end at `sOut`,
  tape `= writeAt3 tp (p+d) b`.
* **`copyBitAtDist3 s sOut d`** / **`copyBitAtDist3_run`** (PROVED) — `readCarry3 ++ copyArm3 (O) ++ copyArm3 (I)`: copies
  the source bit `tp[p]` into cell `p+d`, head back at `p`, source unchanged.  `∃ N, reachIn N (s, p, tp) (sOut, p,
  writeAt3 tp (p+d) (tp.getD p O))`.

## Honest scope

This is the **single-cell copy** — the foundational brick of the apply phase, the analogue of the single-bit compare.  It
does **not** yet loop over a whole field (the new-state copy), nor write the symbol / move the simulated head, nor
assemble `apply3`.  Building those fragment by fragment is the genuine remaining construction, **not faked**.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CopyBit

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (Move moveHead)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn reachIn_add)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym
  (Sym3 TMachine3 concreteStep3 readSym3 toNTM3 writeAt3 applyTrans3 writeAt3_getD writeAt3_id_of_lt)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Move (moveRight3 moveRight3_run_eq)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Mark (moveLeft3 moveLeft3_run_eq)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MoveN (moveRightN3 moveRightN3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Unmark (unmark3 unmark3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_append_left3 reachIn_append_right3 reachIn_seq3)

/-- Length is preserved by an in-bounds write. -/
private theorem writeAt3_length_eq (tp : List Sym3) (p : ℕ) (w : Sym3) (hp : p < tp.length) :
    (writeAt3 tp p w).length = tp.length := by
  simp only [writeAt3, List.length_set, List.length_append, List.length_replicate]
  omega

/-- **The n-step left-move corridor** (mirror of `moveRightN3`). -/
def moveLeftN3 (s : ℕ) : ℕ → TMachine3
  | 0 => []
  | (n + 1) => moveLeft3 s (s + 1) ++ moveLeftN3 (s + 1) n

/-- **The n-step left move (PROVED).**  `n ≤ j` and `j < tp.length` ⇒ head `j → j-n`, state `s → s+n`, tape identical. -/
theorem moveLeftN3_run (s n j : ℕ) (tp : List Sym3) (hnj : n ≤ j) (hb : j < tp.length) :
    reachIn (toNTM3 (moveLeftN3 s n)) n (s, j, tp) (s + n, j - n, tp) := by
  induction n generalizing s j with
  | zero => exact rfl
  | succ n ih =>
      have run1 := moveLeft3_run_eq s (s + 1) j tp hb
      have run2 := ih (s + 1) (j - 1) (by omega) (by omega)
      have comp := reachIn_seq3 (moveLeft3 s (s + 1)) (moveLeftN3 (s + 1) n) 1 n _ _ _ run1 run2
      rw [show (1 : ℕ) + n = n + 1 from by omega, show s + 1 + n = s + (n + 1) from by omega,
        show j - 1 - n = j - (n + 1) from by omega] at comp
      exact comp

/-- **The read-and-carry machine.**  Read the head cell, write it back (tape unchanged), *stay*, and branch the control
state on the value: `sO` if `O`, `sI` if `I` (the `M` case is a dead branch). -/
def readCarry3 (s sO sI : ℕ) : TMachine3 :=
  [((s, Sym3.O), (sO, Sym3.O, (2 : Move))), ((s, Sym3.I), (sI, Sym3.I, (2 : Move))),
   ((s, Sym3.M), (sO, Sym3.M, (2 : Move)))]

/-- **Read-and-carry on `O` (PROVED).**  Tape and head unchanged, control routed to `sO`. -/
theorem readCarry3_run_O (s sO sI j : ℕ) (tp : List Sym3) (h : readSym3 (s, j, tp) = Sym3.O) (hj : j < tp.length) :
    reachIn (toNTM3 (readCarry3 s sO sI)) 1 (s, j, tp) (sO, j, tp) := by
  have hh : tp.getD j Sym3.O = Sym3.O := h
  have hw : writeAt3 tp j Sym3.O = tp := hh ▸ writeAt3_id_of_lt tp j hj
  refine ⟨(sO, j, tp), ?_, rfl⟩
  exact ⟨((s, Sym3.O), (sO, Sym3.O, (2 : Move))), by simp [readCarry3], by simp [h],
    by simp [applyTrans3, moveHead, hw]⟩

/-- **Read-and-carry on `I` (PROVED).**  Tape and head unchanged, control routed to `sI`. -/
theorem readCarry3_run_I (s sO sI j : ℕ) (tp : List Sym3) (h : readSym3 (s, j, tp) = Sym3.I) (hj : j < tp.length) :
    reachIn (toNTM3 (readCarry3 s sO sI)) 1 (s, j, tp) (sI, j, tp) := by
  have hh : tp.getD j Sym3.O = Sym3.I := h
  have hw : writeAt3 tp j Sym3.I = tp := hh ▸ writeAt3_id_of_lt tp j hj
  refine ⟨(sI, j, tp), ?_, rfl⟩
  exact ⟨((s, Sym3.I), (sI, Sym3.I, (2 : Move))), by simp [readCarry3], by simp [h],
    by simp [applyTrans3, moveHead, hw]⟩

/-- **One copy lineage.**  Go right `d`, write the carried bit `b` at the destination, walk back the fixed `d` cells, and
write `b` back at the source (an identity, since the source already holds `b`), ending at `sOut`. -/
def copyArm3 (s sOut d : ℕ) (b : Sym3) : TMachine3 :=
  moveRightN3 s d ++ unmark3 (s + d) (s + d + 1) b ++ moveLeftN3 (s + d + 1) d ++ unmark3 (s + 2 * d + 1) sOut b

/-- **The copy-lineage run (PROVED).**  With the source bit `tp[p] = b` and `p`, `p+d` in bounds: head returns to `p`,
the destination cell `p+d` holds `b`, everything else unchanged. -/
theorem copyArm3_run (s sOut d p : ℕ) (b : Sym3) (tp : List Sym3) (hb : tp.getD p Sym3.O = b)
    (hd : 1 ≤ d) (hp : p < tp.length) (hpd : p + d < tp.length) :
    ∃ N, reachIn (toNTM3 (copyArm3 s sOut d b)) N (s, p, tp) (sOut, p, writeAt3 tp (p + d) b) := by
  have hlen1 : (writeAt3 tp (p + d) b).length = tp.length := writeAt3_length_eq tp (p + d) b hpd
  have r1 := moveRightN3_run s d p tp (by omega)
  have r2 := unmark3_run (s + d) (s + d + 1) b (p + d) tp
  have r3 := moveLeftN3_run (s + d + 1) d (p + d) (writeAt3 tp (p + d) b) (by omega) (by rw [hlen1]; exact hpd)
  rw [show p + d - d = p from by omega, show s + d + 1 + d = s + 2 * d + 1 from by omega] at r3
  have r4 := unmark3_run (s + 2 * d + 1) sOut b p (writeAt3 tp (p + d) b)
  have hfix : writeAt3 (writeAt3 tp (p + d) b) p b = writeAt3 tp (p + d) b := by
    have hp1 : (writeAt3 tp (p + d) b).getD p Sym3.O = b := by rw [writeAt3_getD, if_neg (by omega)]; exact hb
    have hplen : p < (writeAt3 tp (p + d) b).length := by rw [hlen1]; exact hp
    have hid := writeAt3_id_of_lt (writeAt3 tp (p + d) b) p hplen
    rwa [hp1] at hid
  rw [hfix] at r4
  have s12 := reachIn_seq3 (moveRightN3 s d) (unmark3 (s + d) (s + d + 1) b) d 1 _ _ _ r1 r2
  have s123 := reachIn_seq3 (moveRightN3 s d ++ unmark3 (s + d) (s + d + 1) b)
    (moveLeftN3 (s + d + 1) d) (d + 1) d _ _ _ s12 r3
  have s1234 := reachIn_seq3 (moveRightN3 s d ++ unmark3 (s + d) (s + d + 1) b ++ moveLeftN3 (s + d + 1) d)
    (unmark3 (s + 2 * d + 1) sOut b) (d + 1 + d) 1 _ _ _ s123 r4
  exact ⟨d + 1 + d + 1, s1234⟩

/-- **The single-cell copy-at-distance.**  Read the source bit, then in the matching lineage copy it to the destination
`d` cells away and return. -/
def copyBitAtDist3 (s sOut d : ℕ) : TMachine3 :=
  readCarry3 s (s + 1) (s + 2 * d + 3) ++ copyArm3 (s + 1) sOut d Sym3.O ++ copyArm3 (s + 2 * d + 3) sOut d Sym3.I

/-- **The single-cell copy run (PROVED).**  Copies the source bit `tp[p]` into cell `p+d`; the head returns to `p` and the
source is unchanged: `∃ N, reachIn N (s, p, tp) (sOut, p, writeAt3 tp (p+d) (tp.getD p O))`. -/
theorem copyBitAtDist3_run (s sOut d p : ℕ) (tp : List Sym3)
    (hbit : tp.getD p Sym3.O = Sym3.O ∨ tp.getD p Sym3.O = Sym3.I)
    (hd : 1 ≤ d) (hp : p < tp.length) (hpd : p + d < tp.length) :
    ∃ N, reachIn (toNTM3 (copyBitAtDist3 s sOut d)) N (s, p, tp)
      (sOut, p, writeAt3 tp (p + d) (tp.getD p Sym3.O)) := by
  rcases hbit with hb | hb
  · -- source bit O: the O-lineage copies
    have hrc := readCarry3_run_O s (s + 1) (s + 2 * d + 3) p tp
      (by rw [show readSym3 (s, p, tp) = tp.getD p Sym3.O from rfl, hb]) hp
    obtain ⟨N, harm⟩ := copyArm3_run (s + 1) sOut d p Sym3.O tp hb hd hp hpd
    rw [hb]
    have s1 := reachIn_seq3 (readCarry3 s (s + 1) (s + 2 * d + 3)) (copyArm3 (s + 1) sOut d Sym3.O)
      1 N _ _ _ hrc harm
    exact ⟨1 + N, reachIn_append_left3 _ (copyArm3 (s + 2 * d + 3) sOut d Sym3.I) (1 + N) _ _ s1⟩
  · -- source bit I: the I-lineage copies
    have hrc := readCarry3_run_I s (s + 1) (s + 2 * d + 3) p tp
      (by rw [show readSym3 (s, p, tp) = tp.getD p Sym3.O from rfl, hb]) hp
    obtain ⟨N, harm⟩ := copyArm3_run (s + 2 * d + 3) sOut d p Sym3.I tp hb hd hp hpd
    rw [hb]
    have hrcL := reachIn_append_left3 (readCarry3 s (s + 1) (s + 2 * d + 3)) (copyArm3 (s + 1) sOut d Sym3.O)
      1 _ _ hrc
    have hrcL2 := reachIn_append_left3 (readCarry3 s (s + 1) (s + 2 * d + 3) ++ copyArm3 (s + 1) sOut d Sym3.O)
      (copyArm3 (s + 2 * d + 3) sOut d Sym3.I) 1 _ _ hrcL
    have harmL := reachIn_append_right3 (readCarry3 s (s + 1) (s + 2 * d + 3) ++ copyArm3 (s + 1) sOut d Sym3.O)
      (copyArm3 (s + 2 * d + 3) sOut d Sym3.I) N _ _ harm
    exact ⟨1 + N, (reachIn_add (toNTM3 (copyBitAtDist3 s sOut d)) 1 N _ _).mpr ⟨_, hrcL2, harmL⟩⟩

/-!
**The single-cell copy, proved.**  `copyBitAtDist3` reads a source bit and writes it to a destination cell at arbitrary
distance, marker-free (the fixed-`d` return needs no seek), leaving the source and head untouched — the foundational brick
of the apply phase, mirroring the single-bit compare.  Next: loop it over a whole unary field (the new-state copy), then
the symbol write and head move, then assemble `apply3` — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CopyBit

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CopyBit.copyBitAtDist3_run
