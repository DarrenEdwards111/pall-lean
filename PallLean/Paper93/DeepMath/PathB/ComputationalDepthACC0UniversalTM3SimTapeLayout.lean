import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3EncTrans

/-!
# Entry 460 — universal-TM-table build: the simulated-tape region `simTapeRegion` (proved)

The simulated-tape region of the assembly layout `φ`: the abstract TM tape (a `List Bool`) encoded as `Sym3` bits with the
head marker `M` inserted just before the head cell — the marker-right-of-current-cell representation the apply phases use
(entries 419–438).  For tape `tp` and head position `h`, the region is `(tp.take h).map boolToSym3 ++ M :: (tp.drop h).map
boolToSym3`: the marker sits at index `h`, the current cell (the head's symbol) at `h+1`, and every other cell is a bit.

This brick proves exactly the apply-side invariants: the head marker at `h`, the current cell a bit, and no other marker.

## What is proved (clean axioms, no `sorry`)

* **`simTapeRegion tp h`** — the encoded simulated tape with the head marker.
* **`simTapeRegion_marker`** (PROVED) — `h ≤ tp.length → (simTapeRegion tp h).getD h O = M`.
* **`simTapeRegion_current`** (PROVED) — `h ≤ tp.length → (simTapeRegion tp h).getD (h+1) O = O ∨ = I` (current cell a bit).
* **`simTapeRegion_clean`** (PROVED) — `h ≤ tp.length → j ≠ h → (simTapeRegion tp h).getD j O ≠ M` (no other marker).

## Honest scope

This is the **simulated-tape region** of `φ` with its apply-side invariants.  It does **not** yet stitch config + rule
table + sim-tape into the full `φ`, nor define `U` / prove `EmitsEncodedStepEx3` (the large but obstruction-free remaining
assembly, per entry 456).  Building the rest fragment by fragment is the genuine remaining construction, **not faked**.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3SimTapeLayout

open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3EncTrans (boolToSym3)

/-- **The simulated-tape region.**  The abstract tape encoded as bits with the head marker `M` before the head cell. -/
def simTapeRegion (tp : List Bool) (h : ℕ) : List Sym3 :=
  (tp.take h).map boolToSym3 ++ Sym3.M :: (tp.drop h).map boolToSym3

/-- **A bit-encoded cell reads `O` or `I` (PROVED).** -/
theorem mapBool_getElem?_bit (l : List Bool) (j : ℕ) :
    ((List.map boolToSym3 l)[j]?).getD Sym3.O = Sym3.O ∨ ((List.map boolToSym3 l)[j]?).getD Sym3.O = Sym3.I := by
  rw [List.getElem?_map]
  rcases l[j]? with _ | b
  · left; rfl
  · cases b <;> simp [boolToSym3]

private theorem take_map_length (tp : List Bool) (h : ℕ) (hh : h ≤ tp.length) :
    ((tp.take h).map boolToSym3).length = h := by
  rw [List.length_map, List.length_take]; omega

/-- **The head marker is at `h` (PROVED).** -/
theorem simTapeRegion_marker (tp : List Bool) (h : ℕ) (hh : h ≤ tp.length) :
    (simTapeRegion tp h).getD h Sym3.O = Sym3.M := by
  have hlen := take_map_length tp h hh
  rw [simTapeRegion, List.getD_eq_getElem?_getD, List.getElem?_append_right hlen.le, hlen, Nat.sub_self]
  rfl

/-- **The current cell is a bit (PROVED).** -/
theorem simTapeRegion_current (tp : List Bool) (h : ℕ) (hh : h ≤ tp.length) :
    (simTapeRegion tp h).getD (h + 1) Sym3.O = Sym3.O ∨ (simTapeRegion tp h).getD (h + 1) Sym3.O = Sym3.I := by
  have hlen := take_map_length tp h hh
  rw [simTapeRegion, List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hlen]; omega), hlen,
    show h + 1 - h = 1 from by omega, List.getElem?_cons_succ]
  exact mapBool_getElem?_bit (tp.drop h) 0

/-- **No marker except at `h` (PROVED).** -/
theorem simTapeRegion_clean (tp : List Bool) (h j : ℕ) (hh : h ≤ tp.length) (hj : j ≠ h) :
    (simTapeRegion tp h).getD j Sym3.O ≠ Sym3.M := by
  have hlen := take_map_length tp h hh
  rcases Nat.lt_or_ge j h with hlt | hge
  · rw [simTapeRegion, List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hlen]; omega)]
    rcases mapBool_getElem?_bit (tp.take h) j with hb | hb <;> rw [hb] <;> decide
  · rw [simTapeRegion, List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hlen]; omega), hlen,
      show j - h = (j - h - 1) + 1 from by omega, List.getElem?_cons_succ]
    rcases mapBool_getElem?_bit (tp.drop h) (j - h - 1) with hb | hb <;> rw [hb] <;> decide

/-!
**The simulated-tape region, proved.**  `simTapeRegion` encodes the TM tape with the head marker, and its invariants are
exactly the apply-side preconditions (head marker at `h`, current cell a bit, no other marker).  Next: stitch config + rule
table + sim-tape into the full `φ`, then assemble `U` toward `EmitsEncodedStepEx3` — fragment by verified fragment, not
faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3SimTapeLayout

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3SimTapeLayout.simTapeRegion_marker
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3SimTapeLayout.simTapeRegion_clean
