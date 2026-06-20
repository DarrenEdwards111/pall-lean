import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3CopyBit
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3Mark
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3TapeShiftRight

/-!
# Entry 453 — universal-TM-table build: the right-to-left shift machine `copyFieldRight3` (proved)

The machine realising the rightward tape shift (entry 452).  A right shift must copy **high-to-low**, so this machine
starts at the high cell, copies it rightward by `d` (`copyBitAtDist3`, entry 411), steps left (`moveLeft3`, entry 386), and
repeats.  Its run produces exactly `copyBlockRight` (entry 452), so together they are the complete rightward tape-shift
primitive (the dual of `copyFieldLeft3` + entry 451).

## What is proved (clean axioms, no `sorry`)

* **`copyFieldRight3 s sDone d n`** — the high-to-low copy loop: copy the current cell rightward by `d`, step left, recurse.
* **`copyFieldRight3_run`** (PROVED) — `1 ≤ d`, the block `c … c+n` all bits, `c+n+d < tp.length`: `∃ N, reachIn N (s,
  c+n, tp) (sDone, c, copyBlockRight tp c d n)` — starting at the high cell `c+n`, the block is shifted right by `d`, the
  head ending at `c`.

## Honest scope

This is the **right-to-left shift machine** realising `copyBlockRight`.  It does **not** assemble the state-growth update
nor `EmitsEncodedStep3`.  Building the rest fragment by fragment is the genuine remaining construction, **not faked**.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ShiftRightMachine

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 toNTM3 writeAt3 writeAt3_getD)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CopyBit (copyBitAtDist3 copyBitAtDist3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Mark (moveLeft3 moveLeft3_run_eq)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3TapeShiftRight (copyBlockRight)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_seq3)

/-- In-bounds write preserves length. -/
private theorem writeAt3_length_eq (tp : List Sym3) (q : ℕ) (v : Sym3) (hq : q < tp.length) :
    (writeAt3 tp q v).length = tp.length := by
  simp only [writeAt3, List.length_set, List.length_append, List.length_replicate]; omega

/-- **The right-to-left shift loop.**  Copy the current cell rightward by `d`, step left, recurse. -/
def copyFieldRight3 (s sDone d : ℕ) : ℕ → TMachine3
  | 0 => copyBitAtDist3 s sDone d
  | (n + 1) =>
      copyBitAtDist3 s (s + 4 * d + 5) d ++ moveLeft3 (s + 4 * d + 5) (s + 4 * d + 6)
        ++ copyFieldRight3 (s + 4 * d + 6) sDone d n

/-- **The right-to-left shift run (PROVED).**  Shifts the block `c … c+n` right by `d`, producing `copyBlockRight tp c d n`,
head ending at `c`. -/
theorem copyFieldRight3_run (sDone d : ℕ) (hd : 1 ≤ d) :
    ∀ (n s c : ℕ) (tp : List Sym3), (∀ i, i ≤ n → tp.getD (c + i) Sym3.O = Sym3.O ∨ tp.getD (c + i) Sym3.O = Sym3.I) →
      c + n + d < tp.length →
      ∃ N, reachIn (toNTM3 (copyFieldRight3 s sDone d n)) N (s, c + n, tp) (sDone, c, copyBlockRight tp c d n) := by
  intro n
  induction n with
  | zero =>
      intro s c tp hbit hbnd
      obtain ⟨N, h⟩ := copyBitAtDist3_run s sDone d c tp (by simpa using hbit 0 (by omega)) hd (by omega) (by omega)
      exact ⟨N, h⟩
  | succ n ih =>
      intro s c tp hbit hbnd
      obtain ⟨N1, h1⟩ := copyBitAtDist3_run s (s + 4 * d + 5) d (c + (n + 1)) tp
        (by simpa using hbit (n + 1) (by omega)) hd (by omega) (by omega)
      set tp' := writeAt3 tp (c + (n + 1) + d) (tp.getD (c + (n + 1)) Sym3.O) with htp'
      have hlen : tp'.length = tp.length := writeAt3_length_eq tp (c + (n + 1) + d) _ (by omega)
      have hml := moveLeft3_run_eq (s + 4 * d + 5) (s + 4 * d + 6) (c + (n + 1)) tp' (by rw [hlen]; omega)
      rw [show c + (n + 1) - 1 = c + n from by omega] at hml
      have hbit' : ∀ i, i ≤ n → tp'.getD (c + i) Sym3.O = Sym3.O ∨ tp'.getD (c + i) Sym3.O = Sym3.I := by
        intro i hi
        rw [htp', writeAt3_getD, if_neg (by omega)]
        exact hbit i (by omega)
      obtain ⟨N2, h2⟩ := ih (s + 4 * d + 6) c tp' hbit' (by rw [hlen]; omega)
      have s1 := reachIn_seq3 (copyBitAtDist3 s (s + 4 * d + 5) d) (moveLeft3 (s + 4 * d + 5) (s + 4 * d + 6))
        N1 1 _ _ _ h1 hml
      exact ⟨N1 + 1 + N2, reachIn_seq3 (copyBitAtDist3 s (s + 4 * d + 5) d ++ moveLeft3 (s + 4 * d + 5) (s + 4 * d + 6))
        (copyFieldRight3 (s + 4 * d + 6) sDone d n) (N1 + 1) N2 _ _ _ s1 h2⟩

/-!
**The right-to-left shift machine, proved.**  `copyFieldRight3` realises `copyBlockRight` — together with entry 452 this is
the complete rightward tape-shift primitive (the dual of `copyFieldLeft3` + 451).  Next: the state-update-with-shift
(handling both growth and shrink), and the matcher↔lookup correspondence toward `EmitsEncodedStep3` — fragment by verified
fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ShiftRightMachine

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ShiftRightMachine.copyFieldRight3_run
