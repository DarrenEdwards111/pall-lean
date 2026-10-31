import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3CopyBit
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3SeekR

/-!
# Entry 420 — universal-TM-table build: read the current symbol at the marker `readHeadSym3` (proved)

Under the marker-on-current-cell head representation (entry 419) the simulated head is a marker `M`; the current symbol is
the cell **right after** `M`.  This brick is the bridge that reconnects the rest of the machinery to that representation:
**read the current symbol** by finding the marker and inspecting the following cell.

It is distance-independent: seek right to the marker (`seekMarkRight`, entry 388), step onto the current cell, and branch
the control state on its value (`readCarry3`, entry 411).  The result leaves the head on the current cell and routes to
`sO`/`sI` according to the current symbol, the tape untouched — so the matcher / apply can obtain the simulated read symbol
without a fixed-offset cache.

## What is proved (clean axioms, no `sorry`)

* **`readHeadSym3 s sO sI`** — `seekMarkRight s (s+1) (s+2) ++ moveRight3 (s+1) (s+3) ++ readCarry3 (s+3) sO sI`.
* **`readHeadSym3_run`** (PROVED) — with the marker at `h+d` (no marker in `[h, h+d)`), `h+d`/`h+d+1` in bounds, and the
  current cell `h+d+1` a bit: `∃ N, reachIn N (s, h, tp) ((if tp.getD (h+d+1) O = O then sO else sI), h+d+1, tp)` — the
  head ends on the current cell, control routed on the current symbol, tape identical.

## Honest scope

This is the **read-current-symbol-at-marker** bridge.  It does **not** yet rework the matcher to use it, nor assemble
`apply3`.  Building those fragment by fragment is the genuine remaining construction, **not faked**.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ReadHead

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 readSym3 toNTM3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3SeekR (seekMarkRight seekMarkRight_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Move (moveRight3 moveRight3_run_eq)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CopyBit (readCarry3 readCarry3_run_O readCarry3_run_I)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_seq3)

/-- **Read the current symbol at the head marker.**  Seek right to `M`, step onto the current cell, branch on its value. -/
def readHeadSym3 (s sO sI : ℕ) : TMachine3 :=
  seekMarkRight s (s + 1) (s + 2) ++ moveRight3 (s + 1) (s + 3) ++ readCarry3 (s + 3) sO sI

/-- **The read-current-symbol run (PROVED).**  Routes to `sO`/`sI` by the current symbol `tp[h+d+1]`, head on the current
cell, tape identical. -/
theorem readHeadSym3_run (s sO sI d h : ℕ) (tp : List Sym3)
    (hmark : tp.getD (h + d) Sym3.O = Sym3.M) (hclear : ∀ k, k < d → tp.getD (h + k) Sym3.O ≠ Sym3.M)
    (hbound : h + d < tp.length) (hbound2 : h + d + 1 < tp.length)
    (hcur : tp.getD (h + d + 1) Sym3.O = Sym3.O ∨ tp.getD (h + d + 1) Sym3.O = Sym3.I) :
    ∃ N, reachIn (toNTM3 (readHeadSym3 s sO sI)) N (s, h, tp)
      ((if tp.getD (h + d + 1) Sym3.O = Sym3.O then sO else sI), h + d + 1, tp) := by
  obtain ⟨N1, hseek⟩ := seekMarkRight_run s (s + 1) (s + 2) tp d h hmark hclear hbound
  have hmr := moveRight3_run_eq (s + 1) (s + 3) (h + d) tp hbound
  have s1 := reachIn_seq3 (seekMarkRight s (s + 1) (s + 2)) (moveRight3 (s + 1) (s + 3)) N1 1 _ _ _ hseek hmr
  rcases hcur with hb | hb
  · rw [if_pos hb]
    have hrc := readCarry3_run_O (s + 3) sO sI (h + d + 1) tp
      (by rw [show readSym3 (s + 3, h + d + 1, tp) = tp.getD (h + d + 1) Sym3.O from rfl, hb]) hbound2
    exact ⟨N1 + 1 + 1, reachIn_seq3 (seekMarkRight s (s + 1) (s + 2) ++ moveRight3 (s + 1) (s + 3))
      (readCarry3 (s + 3) sO sI) (N1 + 1) 1 _ _ _ s1 hrc⟩
  · rw [if_neg (by rw [hb]; decide)]
    have hrc := readCarry3_run_I (s + 3) sO sI (h + d + 1) tp
      (by rw [show readSym3 (s + 3, h + d + 1, tp) = tp.getD (h + d + 1) Sym3.O from rfl, hb]) hbound2
    exact ⟨N1 + 1 + 1, reachIn_seq3 (seekMarkRight s (s + 1) (s + 2) ++ moveRight3 (s + 1) (s + 3))
      (readCarry3 (s + 3) sO sI) (N1 + 1) 1 _ _ _ s1 hrc⟩

/-!
**Read the current symbol at the marker, proved.**  `readHeadSym3` obtains the simulated read symbol distance-independently
from the head marker, routing the control state on it — the bridge from the marker head representation back to the matcher
and apply.  Next: rework the matcher's current-symbol read to use this, and assemble `apply3` — fragment by verified
fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ReadHead

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ReadHead.readHeadSym3_run
