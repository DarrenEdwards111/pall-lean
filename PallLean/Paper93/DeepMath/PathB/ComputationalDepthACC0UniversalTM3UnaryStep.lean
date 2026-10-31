import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3Scan
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3Mark
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3Unmark
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3Compose

/-!
# Entry 416 — universal-TM-table build: the unary head-pointer step `unaryInc3` / `unaryDec3` (proved)

Per the chosen configuration layout, the simulated head position is an explicit **unary field** and a head *move* updates it
by `±1`.  This brick builds and proves that update.

A unary field `n` ones (cells `h … h+n-1`) then an `O` separator (cell `h+n`), padded on the right by reserved blank (`O`)
cells, is incremented/decremented by a single cell flip:

* **increment** `n → n+1`: flip the separator cell `h+n` from `O` to `I` (the already-blank cell `h+n+1` becomes the new
  separator);
* **decrement** `n → n-1`: flip the last one `h+n-1` from `I` to `O` (the old separator cell `h+n` stays blank).

The machine scans the field to its end (`scanNatFrom3`), walks left to the target cell (`moveLeft3`), and writes
(`unmark3`).

## What is proved (clean axioms, no `sorry`)

* **`unaryInc3 s s'`** / **`unaryInc3_run`** (PROVED) — `∃ N, reachIn N (s, h, tp) (s', h+n, writeAt3 tp (h+n) I)`.
* **`unaryDec3 s s'`** / **`unaryDec3_run`** (PROVED) — for `n ≥ 1`: `∃ N, reachIn N (s, h, tp) (s', h+n-1, writeAt3 tp
  (h+n-1) O)`.
* **`unaryInc3_field` / `unaryDec3_field`** (PROVED) — the content corollaries confirming the result is a unary field of
  length `n+1` resp. `n-1` (given the right cell is reserved blank).

## Honest scope

This is the **unary head-pointer ±1 step**.  It does **not** yet refresh the cached current symbol after a move, nor
assemble `apply3`.  Building those fragment by fragment is the genuine remaining construction, **not faked**.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3UnaryStep

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 toNTM3 writeAt3 writeAt3_getD)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Scan (scanNatFrom3 scanNatFrom3_run_eq)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Mark (moveLeft3 moveLeft3_run_eq)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Unmark (unmark3 unmark3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_seq3)

/-- **The unary increment.**  Scan to the field separator, step left onto it, write `I`. -/
def unaryInc3 (s s' : ℕ) : TMachine3 :=
  scanNatFrom3 s (s + 1) ++ moveLeft3 (s + 1) (s + 2) ++ unmark3 (s + 2) s' Sym3.I

/-- **The unary increment run (PROVED).**  Flips the separator `h+n` to `I` (so the field becomes `n+1`), head left at
`h+n`. -/
theorem unaryInc3_run (s s' n h : ℕ) (tp : List Sym3)
    (htrue : ∀ i, i < n → tp.getD (h + i) Sym3.O = Sym3.I) (hfalse : tp.getD (h + n) Sym3.O = Sym3.O)
    (hbound : h + n + 1 < tp.length) :
    ∃ N, reachIn (toNTM3 (unaryInc3 s s')) N (s, h, tp) (s', h + n, writeAt3 tp (h + n) Sym3.I) := by
  have r1 := scanNatFrom3_run_eq s (s + 1) n h tp htrue hfalse (by omega)
  have r2 := moveLeft3_run_eq (s + 1) (s + 2) (h + n + 1) tp hbound
  rw [show h + n + 1 - 1 = h + n from by omega] at r2
  have r3 := unmark3_run (s + 2) s' Sym3.I (h + n) tp
  have s12 := reachIn_seq3 (scanNatFrom3 s (s + 1)) (moveLeft3 (s + 1) (s + 2)) (n + 1) 1 _ _ _ r1 r2
  have s123 := reachIn_seq3 (scanNatFrom3 s (s + 1) ++ moveLeft3 (s + 1) (s + 2)) (unmark3 (s + 2) s' Sym3.I)
    (n + 1 + 1) 1 _ _ _ s12 r3
  exact ⟨n + 1 + 1 + 1, s123⟩

/-- **The incremented field is a unary field of length `n+1` (PROVED).**  Given the next cell is reserved blank. -/
theorem unaryInc3_field (n h : ℕ) (tp : List Sym3)
    (htrue : ∀ i, i < n → tp.getD (h + i) Sym3.O = Sym3.I) (hfalse2 : tp.getD (h + n + 1) Sym3.O = Sym3.O) :
    (∀ i, i < n + 1 → (writeAt3 tp (h + n) Sym3.I).getD (h + i) Sym3.O = Sym3.I)
    ∧ (writeAt3 tp (h + n) Sym3.I).getD (h + (n + 1)) Sym3.O = Sym3.O := by
  refine ⟨fun i hi => ?_, ?_⟩
  · rcases Nat.lt_or_ge i n with hlt | hge
    · rw [writeAt3_getD, if_neg (by omega)]; exact htrue i hlt
    · rw [writeAt3_getD, if_pos (by omega)]
  · rw [writeAt3_getD, if_neg (by omega), show h + (n + 1) = h + n + 1 from by omega]; exact hfalse2

/-- **The unary decrement.**  Scan to the separator, step left twice onto the last one, write `O`. -/
def unaryDec3 (s s' : ℕ) : TMachine3 :=
  scanNatFrom3 s (s + 1) ++ moveLeft3 (s + 1) (s + 2) ++ moveLeft3 (s + 2) (s + 3) ++ unmark3 (s + 3) s' Sym3.O

/-- **The unary decrement run (PROVED).**  For `n ≥ 1`, flips the last one `h+n-1` to `O` (so the field becomes `n-1`),
head left at `h+n-1`. -/
theorem unaryDec3_run (s s' n h : ℕ) (tp : List Sym3) (hn : 1 ≤ n)
    (htrue : ∀ i, i < n → tp.getD (h + i) Sym3.O = Sym3.I) (hfalse : tp.getD (h + n) Sym3.O = Sym3.O)
    (hbound : h + n + 1 < tp.length) :
    ∃ N, reachIn (toNTM3 (unaryDec3 s s')) N (s, h, tp) (s', h + n - 1, writeAt3 tp (h + n - 1) Sym3.O) := by
  have r1 := scanNatFrom3_run_eq s (s + 1) n h tp htrue hfalse (by omega)
  have r2 := moveLeft3_run_eq (s + 1) (s + 2) (h + n + 1) tp hbound
  rw [show h + n + 1 - 1 = h + n from by omega] at r2
  have r3 := moveLeft3_run_eq (s + 2) (s + 3) (h + n) tp (by omega)
  have r4 := unmark3_run (s + 3) s' Sym3.O (h + n - 1) tp
  have s12 := reachIn_seq3 (scanNatFrom3 s (s + 1)) (moveLeft3 (s + 1) (s + 2)) (n + 1) 1 _ _ _ r1 r2
  have s123 := reachIn_seq3 (scanNatFrom3 s (s + 1) ++ moveLeft3 (s + 1) (s + 2)) (moveLeft3 (s + 2) (s + 3))
    (n + 1 + 1) 1 _ _ _ s12 r3
  have s1234 := reachIn_seq3 (scanNatFrom3 s (s + 1) ++ moveLeft3 (s + 1) (s + 2) ++ moveLeft3 (s + 2) (s + 3))
    (unmark3 (s + 3) s' Sym3.O) (n + 1 + 1 + 1) 1 _ _ _ s123 r4
  exact ⟨n + 1 + 1 + 1 + 1, s1234⟩

/-- **The decremented field is a unary field of length `n-1` (PROVED).** -/
theorem unaryDec3_field (n h : ℕ) (tp : List Sym3) (hn : 1 ≤ n)
    (htrue : ∀ i, i < n → tp.getD (h + i) Sym3.O = Sym3.I) :
    (∀ i, i < n - 1 → (writeAt3 tp (h + n - 1) Sym3.O).getD (h + i) Sym3.O = Sym3.I)
    ∧ (writeAt3 tp (h + n - 1) Sym3.O).getD (h + (n - 1)) Sym3.O = Sym3.O := by
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [writeAt3_getD, if_neg (by omega)]; exact htrue i (by omega)
  · rw [writeAt3_getD, if_pos (by omega)]

/-!
**The unary head-pointer step, proved.**  `unaryInc3` / `unaryDec3` update the explicit unary head-position field by `±1`
with a single cell flip after a field scan — the simulated head move at the pointer level.  Next: refresh the cached
current symbol from the simulated tape at the new head, and assemble `apply3` — fragment by verified fragment, not faked.
Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3UnaryStep

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3UnaryStep.unaryInc3_run
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3UnaryStep.unaryDec3_run
