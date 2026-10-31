import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3FullLayout
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3SimTapeLayout

/-!
# Entry 462 — universal-TM-table build: the head marker at the full-tape offset `fullTape3_head_*` (proved)

The apply-side stitching: with the simulated-tape region (`simTapeRegion`, entry 460) placed as the trailing region of the
full tape (`fullTape3`, entry 461), the head marker `M` sits at the full-tape offset `(cfgHead ++ recordsTape3 rules).length
+ h`, and the current cell at `+ h + 1` is a bit.  This connects the local sim-tape invariants (460) to their absolute
positions on the stitched tape, so the apply phases can locate the head.

## What is proved (clean axioms, no `sorry`)

* **`fullTape3_head_marker`** (PROVED) — `h ≤ simTp.length → (fullTape3 a cs rules (simTapeRegion simTp h)).getD
  ((cfgHead a cs ++ recordsTape3 rules).length + h) O = M`.
* **`fullTape3_head_current`** (PROVED) — the current cell at `… + h + 1` reads `O` or `I`.

## Honest scope

This places the head marker / current cell at their full-tape offsets.  It does **not** yet prove the config+rule region is
marker-free at full offsets (the matcher's windowed cleanliness), nor define the bit-decoding `φ` / `U` /
`EmitsEncodedStepEx3` (the large but obstruction-free remaining assembly, per entry 456).  Building the rest fragment by
fragment is the genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3FullHead

open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3RecordsLayout (recordsTape3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3SimTapeLayout (simTapeRegion simTapeRegion_marker simTapeRegion_current)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3FullLayout (fullTape3 cfgHead fullTape3_eq_cfgHead)

/-- **The head marker at the full-tape offset (PROVED).** -/
theorem fullTape3_head_marker (a : ℕ) (cs : Bool) (rules : List (ℕ × Bool)) (simTp : List Bool) (h : ℕ)
    (hh : h ≤ simTp.length) :
    (fullTape3 a cs rules (simTapeRegion simTp h)).getD ((cfgHead a cs ++ recordsTape3 rules).length + h) Sym3.O
      = Sym3.M := by
  rw [fullTape3_eq_cfgHead, ← List.append_assoc, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left, ← List.getD_eq_getElem?_getD]
  exact simTapeRegion_marker simTp h hh

/-- **The current cell at the full-tape offset is a bit (PROVED).** -/
theorem fullTape3_head_current (a : ℕ) (cs : Bool) (rules : List (ℕ × Bool)) (simTp : List Bool) (h : ℕ)
    (hh : h ≤ simTp.length) :
    (fullTape3 a cs rules (simTapeRegion simTp h)).getD ((cfgHead a cs ++ recordsTape3 rules).length + h + 1) Sym3.O
        = Sym3.O ∨
    (fullTape3 a cs rules (simTapeRegion simTp h)).getD ((cfgHead a cs ++ recordsTape3 rules).length + h + 1) Sym3.O
        = Sym3.I := by
  rw [fullTape3_eq_cfgHead, ← List.append_assoc, show (cfgHead a cs ++ recordsTape3 rules).length + h + 1
        = (cfgHead a cs ++ recordsTape3 rules).length + (h + 1) from by omega,
    List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    ← List.getD_eq_getElem?_getD]
  exact simTapeRegion_current simTp h hh

/-!
**The head marker at the full-tape offset, proved.**  The sim-tape's head marker and current cell are located at their
absolute positions on the stitched tape, connecting the local invariants (460) to the apply phases.  Next: the config+rule
region's full-offset cleanliness (windowed for the matcher), the bit-decoding `φ`, and `U` toward `EmitsEncodedStepEx3` —
fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3FullHead

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3FullHead.fullTape3_head_marker
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3FullHead.fullTape3_head_current
