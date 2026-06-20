import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3BitCompare

/-!
# Entry 417 — universal-TM-table build: the distant-cell fetch `fetchBitFromDist3` (proved)

The apply phase must bring values *from* the matched rule and the simulated tape *into* the configuration — e.g. refresh
the cached current symbol from `tape[headPtr]`, or copy the rule's write symbol into the cache.  All of these are
"**read a distant cell and write its value here**": the apply-side analogue of the matcher's `probe3` (entry 403), which
also reaches a distant cell but only *compares* it.

This brick is that fetch.  It anchors the local cell with a marker (`markCarry3`, ignoring the local cell's old value
since it will be overwritten), walks right `d` to the source cell (`moveRightN3`), reads it (`testBit3` against `O`), and
in each lineage walks back to the anchor distance-independently and writes the read value there (`probeTail3` with `O`
resp. `I`).  Net effect: cell `p` receives the value of cell `p+d`; the source `p+d` is unchanged.

## What is proved (clean axioms, no `sorry`)

* **`fetchArm3 s sOut d`** / **`fetchArm3_run`** (PROVED) — with the anchor `M` already at `p`: reads `p+d` (a bit) and
  walks back writing it at `p`: `∃ N, reachIn N (s, p, tp) (sOut, p, writeAt3 tp p (tp.getD (p+d) O))`.
* **`fetchBitFromDist3 s sOut d`** / **`fetchBitFromDist3_run`** (PROVED) — `markCarry3 s (s+1) (s+1) 0 ++ fetchArm3 (s+1)
  sOut d`: lays its own anchor, then fetches.  `∃ N, reachIn N (s, p, tp) (sOut, p, writeAt3 tp p (tp.getD (p+d) O))` —
  cell `p ← tp[p+d]`, source unchanged.

## Honest scope

This is the **distant-cell fetch** — the apply's data-inflow primitive, the read-far/write-near mirror of the
compare-side probe.  It does **not** yet drive the data-dependent navigation to `tape[headPtr]`, nor assemble `apply3`.
Building those fragment by fragment is the genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰`
or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Fetch

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn reachIn_add)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 readSym3 toNTM3 writeAt3 writeAt3_getD)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MarkCarry (markCarry3 markCarry3_run_O markCarry3_run_I)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MoveN (moveRightN3 moveRightN3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3TestBit (testBit3 testBit3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ProbeTail (probeTail3 probeTail3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3WriteWrite (writeAt3_writeAt3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_append_left3 reachIn_append_right3)

/-- Length is preserved by an in-bounds write. -/
private theorem writeAt3_length_eq (tp : List Sym3) (p : ℕ) (w : Sym3) (hp : p < tp.length) :
    (writeAt3 tp p w).length = tp.length := by
  simp only [writeAt3, List.length_set, List.length_append, List.length_replicate]
  omega

/-- **The fetch arm (after the anchor is laid).**  Walk out `d`, read the cell, walk back and write the read value at the
anchor.  Like `probe3` but the two tails write the *read* value (`O` / `I`) instead of restoring a carried constant. -/
def fetchArm3 (s sOut d : ℕ) : TMachine3 :=
  moveRightN3 s d ++ testBit3 (s + d) (s + d + 1) (s + d + 2) Sym3.O ++
    probeTail3 (s + d + 1) (s + d + 3) (s + d + 4) sOut Sym3.O ++
    probeTail3 (s + d + 2) (s + d + 5) (s + d + 6) sOut Sym3.I

/-- **The fetch-arm run (PROVED).**  With the anchor `M` at `p`, no marker in `(p, p+d]`, `p+d` in bounds and a bit there,
the head returns to `p` carrying `tp[p+d]`'s value into the cell `p`. -/
theorem fetchArm3_run (s sOut p d : ℕ) (tp : List Sym3)
    (hmark : tp.getD p Sym3.O = Sym3.M) (hno : ∀ k, 0 < k → k ≤ d → tp.getD (p + k) Sym3.O ≠ Sym3.M)
    (hbound : p + d < tp.length) (hfar : tp.getD (p + d) Sym3.O = Sym3.O ∨ tp.getD (p + d) Sym3.O = Sym3.I) :
    ∃ N, reachIn (toNTM3 (fetchArm3 s sOut d)) N (s, p, tp) (sOut, p, writeAt3 tp p (tp.getD (p + d) Sym3.O)) := by
  set A := moveRightN3 s d with hA
  set B := testBit3 (s + d) (s + d + 1) (s + d + 2) Sym3.O with hB
  set C := probeTail3 (s + d + 1) (s + d + 3) (s + d + 4) sOut Sym3.O with hC
  set D := probeTail3 (s + d + 2) (s + d + 5) (s + d + 6) sOut Sym3.I with hD
  have rA := moveRightN3_run s d p tp (by omega)
  have rA1 := reachIn_append_left3 A B d _ _ rA
  have rA2 := reachIn_append_left3 (A ++ B) C d _ _ rA1
  have rA3 := reachIn_append_left3 (A ++ B ++ C) D d _ _ rA2
  have rB := testBit3_run (s + d) (s + d + 1) (s + d + 2) (p + d) tp Sym3.O (by omega)
  rw [show readSym3 (s + d, p + d, tp) = tp.getD (p + d) Sym3.O from rfl] at rB
  have rB1 := reachIn_append_right3 A B 1 _ _ rB
  have rB2 := reachIn_append_left3 (A ++ B) C 1 _ _ rB1
  have rB3 := reachIn_append_left3 (A ++ B ++ C) D 1 _ _ rB2
  by_cases hcond : tp.getD (p + d) Sym3.O = Sym3.O
  · rw [if_pos hcond] at rB3
    rw [hcond]
    obtain ⟨Nc, hc⟩ := probeTail3_run (s + d + 1) (s + d + 3) (s + d + 4) sOut p d Sym3.O tp hmark hno hbound
    have hc1 := reachIn_append_right3 (A ++ B) C Nc _ _ hc
    have hc2 := reachIn_append_left3 (A ++ B ++ C) D Nc _ _ hc1
    have step1 := (reachIn_add (toNTM3 (A ++ B ++ C ++ D)) d 1 _ _).mpr ⟨_, rA3, rB3⟩
    exact ⟨d + 1 + Nc, (reachIn_add (toNTM3 (A ++ B ++ C ++ D)) (d + 1) Nc _ _).mpr ⟨_, step1, hc2⟩⟩
  · rw [if_neg hcond] at rB3
    have hI : tp.getD (p + d) Sym3.O = Sym3.I := hfar.resolve_left hcond
    rw [hI]
    obtain ⟨Nd, hd⟩ := probeTail3_run (s + d + 2) (s + d + 5) (s + d + 6) sOut p d Sym3.I tp hmark hno hbound
    have hd1 := reachIn_append_right3 (A ++ B ++ C) D Nd _ _ hd
    have step1 := (reachIn_add (toNTM3 (A ++ B ++ C ++ D)) d 1 _ _).mpr ⟨_, rA3, rB3⟩
    exact ⟨d + 1 + Nd, (reachIn_add (toNTM3 (A ++ B ++ C ++ D)) (d + 1) Nd _ _).mpr ⟨_, step1, hd1⟩⟩

/-- **The self-contained distant-cell fetch.**  Lay the anchor (`markCarry3`, both lineages to the same state since the
local value is discarded), then fetch. -/
def fetchBitFromDist3 (s sOut d : ℕ) : TMachine3 :=
  markCarry3 s (s + 1) (s + 1) 0 ++ fetchArm3 (s + 1) sOut d

/-- **The distant-cell fetch run (PROVED).**  Cell `p` receives the value of cell `p+d`; the source `p+d` is unchanged. -/
theorem fetchBitFromDist3_run (s sOut p d : ℕ) (tp : List Sym3)
    (hbit : tp.getD p Sym3.O = Sym3.O ∨ tp.getD p Sym3.O = Sym3.I) (hd : 1 ≤ d)
    (hno : ∀ k, 0 < k → k ≤ d → tp.getD (p + k) Sym3.O ≠ Sym3.M) (hbound : p + d < tp.length)
    (hfar : tp.getD (p + d) Sym3.O = Sym3.O ∨ tp.getD (p + d) Sym3.O = Sym3.I) :
    ∃ N, reachIn (toNTM3 (fetchBitFromDist3 s sOut d)) N (s, p, tp)
      (sOut, p, writeAt3 tp p (tp.getD (p + d) Sym3.O)) := by
  have hmc : reachIn (toNTM3 (markCarry3 s (s + 1) (s + 1) 0)) 1 (s, p, tp) (s + 1, p, writeAt3 tp p Sym3.M) := by
    rcases hbit with hb | hb
    · exact markCarry3_run_O s (s + 1) (s + 1) 0 p tp (by rw [show readSym3 (s, p, tp) = tp.getD p Sym3.O from rfl, hb])
    · exact markCarry3_run_I s (s + 1) (s + 1) 0 p tp (by rw [show readSym3 (s, p, tp) = tp.getD p Sym3.O from rfl, hb])
  have hmark' : (writeAt3 tp p Sym3.M).getD p Sym3.O = Sym3.M := by rw [writeAt3_getD]; simp
  have hno' : ∀ k, 0 < k → k ≤ d → (writeAt3 tp p Sym3.M).getD (p + k) Sym3.O ≠ Sym3.M := by
    intro k hk0 hkd; rw [writeAt3_getD, if_neg (by omega)]; exact hno k hk0 hkd
  have hbound' : p + d < (writeAt3 tp p Sym3.M).length := by
    rw [writeAt3_length_eq tp p Sym3.M (by omega)]; exact hbound
  have hfar' : (writeAt3 tp p Sym3.M).getD (p + d) Sym3.O = Sym3.O ∨
      (writeAt3 tp p Sym3.M).getD (p + d) Sym3.O = Sym3.I := by rw [writeAt3_getD, if_neg (by omega)]; exact hfar
  obtain ⟨N, hfa⟩ := fetchArm3_run (s + 1) sOut p d (writeAt3 tp p Sym3.M) hmark' hno' hbound' hfar'
  have hcollapse : writeAt3 (writeAt3 tp p Sym3.M) p ((writeAt3 tp p Sym3.M).getD (p + d) Sym3.O)
      = writeAt3 tp p (tp.getD (p + d) Sym3.O) := by
    rw [show (writeAt3 tp p Sym3.M).getD (p + d) Sym3.O = tp.getD (p + d) Sym3.O from by
      rw [writeAt3_getD, if_neg (by omega)], writeAt3_writeAt3]
  rw [hcollapse] at hfa
  have h1 := reachIn_append_left3 (markCarry3 s (s + 1) (s + 1) 0) (fetchArm3 (s + 1) sOut d) 1 _ _ hmc
  have h2 := reachIn_append_right3 (markCarry3 s (s + 1) (s + 1) 0) (fetchArm3 (s + 1) sOut d) N _ _ hfa
  exact ⟨1 + N, (reachIn_add (toNTM3 (markCarry3 s (s + 1) (s + 1) 0 ++ fetchArm3 (s + 1) sOut d)) 1 N _ _).mpr
    ⟨_, h1, h2⟩⟩

/-!
**The distant-cell fetch, proved.**  `fetchBitFromDist3` reads a cell at arbitrary distance and writes its value at the
anchor — the apply's read-far/write-near primitive, mirroring the compare-side probe.  Next: drive the data-dependent walk
to `tape[headPtr]` (the cache refresh), and assemble `apply3` — fragment by verified fragment, not faked.  Not a
separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Fetch

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Fetch.fetchBitFromDist3_run
