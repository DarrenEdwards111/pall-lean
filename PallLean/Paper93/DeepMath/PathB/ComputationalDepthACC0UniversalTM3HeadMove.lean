import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3CopyBitLeft

/-!
# Entry 419 — universal-TM-table build: the marker-on-current-cell head move `headMoveRight3` / `headMoveLeft3` (proved)

We switch the simulated-head representation to a **marker on the current cell** (the marker `M` marks the head position
on the simulated tape).  The decisive advantage over the explicit unary head-pointer (entries 416/418) is that a head
*move* is now **local** — a swap of the marker with its neighbouring symbol — so it needs **no data-dependent walk**.

Even better, the move reuses the already-proven single-cell copies.  A right move from `M` at `p`:

1. step onto the neighbour `p+1` (`moveRight3`);
2. carry the neighbour's symbol `c = tp[p+1]` one cell left, onto the old marker cell `p` (`copyBitAtDistLeft3` at
   distance `1`) — leaving `p ← c` and `p+1` still `c`;
3. write `M` at `p+1` (`unmark3`).

Net: `p ← c`, `p+1 ← M`; the marker has moved one cell right and the non-`M` cell sequence is preserved.  The left move is
the mirror (`moveLeft3`, `copyBitAtDist3` at distance `1`, write `M` at `p-1`).

## What is proved (clean axioms, no `sorry`)

* **`headMoveRight3 s sOut`** / **`headMoveRight3_run`** (PROVED) — with `tp[p+1] ∈ {O,I}` and `p+1 < tp.length`:
  `∃ N, reachIn N (s, p, tp) (sOut, p+1, writeAt3 (writeAt3 tp p (tp.getD (p+1) O)) (p+1) M)`.
* **`headMoveLeft3 s sOut`** / **`headMoveLeft3_run`** (PROVED) — with `tp[p-1] ∈ {O,I}`, `1 ≤ p`, `p < tp.length`:
  `∃ N, reachIn N (s, p, tp) (sOut, p-1, writeAt3 (writeAt3 tp p (tp.getD (p-1) O)) (p-1) M)`.

## Honest scope

This **switches the head representation** and proves the local head moves — no data-dependent addressing needed.  It does
**not** yet rework the matcher to read the current symbol at the marker, nor assemble `apply3`.  Building those fragment by
fragment is the genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3HeadMove

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 toNTM3 writeAt3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Move (moveRight3 moveRight3_run_eq)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Mark (moveLeft3 moveLeft3_run_eq)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Unmark (unmark3 unmark3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CopyBit (copyBitAtDist3 copyBitAtDist3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CopyBitLeft (copyBitAtDistLeft3 copyBitAtDistLeft3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_seq3)

/-- **The right head move.**  Step onto the neighbour, carry its symbol left over the old marker, then mark the neighbour. -/
def headMoveRight3 (s sOut : ℕ) : TMachine3 :=
  moveRight3 s (s + 1) ++ copyBitAtDistLeft3 (s + 1) (s + 10) 1 ++ unmark3 (s + 10) sOut Sym3.M

/-- **The right head-move run (PROVED).**  The marker moves from `p` to `p+1`; cell `p` receives the neighbour's symbol. -/
theorem headMoveRight3_run (s sOut p : ℕ) (tp : List Sym3)
    (hc : tp.getD (p + 1) Sym3.O = Sym3.O ∨ tp.getD (p + 1) Sym3.O = Sym3.I) (hbnd : p + 1 < tp.length) :
    ∃ N, reachIn (toNTM3 (headMoveRight3 s sOut)) N (s, p, tp)
      (sOut, p + 1, writeAt3 (writeAt3 tp p (tp.getD (p + 1) Sym3.O)) (p + 1) Sym3.M) := by
  have hmr := moveRight3_run_eq s (s + 1) p tp (by omega)
  obtain ⟨N, hcp⟩ := copyBitAtDistLeft3_run (s + 1) (s + 10) 1 (p + 1) tp hc (by norm_num) (by omega) (by omega)
  rw [show p + 1 - 1 = p from by omega] at hcp
  have hun := unmark3_run (s + 10) sOut Sym3.M (p + 1) (writeAt3 tp p (tp.getD (p + 1) Sym3.O))
  have s1 := reachIn_seq3 (moveRight3 s (s + 1)) (copyBitAtDistLeft3 (s + 1) (s + 10) 1) 1 N _ _ _ hmr hcp
  exact ⟨1 + N + 1, reachIn_seq3 (moveRight3 s (s + 1) ++ copyBitAtDistLeft3 (s + 1) (s + 10) 1)
    (unmark3 (s + 10) sOut Sym3.M) (1 + N) 1 _ _ _ s1 hun⟩

/-- **The left head move.**  Step onto the neighbour, carry its symbol right over the old marker, then mark the neighbour. -/
def headMoveLeft3 (s sOut : ℕ) : TMachine3 :=
  moveLeft3 s (s + 1) ++ copyBitAtDist3 (s + 1) (s + 10) 1 ++ unmark3 (s + 10) sOut Sym3.M

/-- **The left head-move run (PROVED).**  The marker moves from `p` to `p-1`; cell `p` receives the neighbour's symbol. -/
theorem headMoveLeft3_run (s sOut p : ℕ) (tp : List Sym3)
    (hc : tp.getD (p - 1) Sym3.O = Sym3.O ∨ tp.getD (p - 1) Sym3.O = Sym3.I) (hp : 1 ≤ p) (hbnd : p < tp.length) :
    ∃ N, reachIn (toNTM3 (headMoveLeft3 s sOut)) N (s, p, tp)
      (sOut, p - 1, writeAt3 (writeAt3 tp p (tp.getD (p - 1) Sym3.O)) (p - 1) Sym3.M) := by
  have hml := moveLeft3_run_eq s (s + 1) p tp (by omega)
  obtain ⟨N, hcp⟩ := copyBitAtDist3_run (s + 1) (s + 10) 1 (p - 1) tp hc (by norm_num) (by omega) (by omega)
  rw [show p - 1 + 1 = p from by omega] at hcp
  have hun := unmark3_run (s + 10) sOut Sym3.M (p - 1) (writeAt3 tp p (tp.getD (p - 1) Sym3.O))
  have s1 := reachIn_seq3 (moveLeft3 s (s + 1)) (copyBitAtDist3 (s + 1) (s + 10) 1) 1 N _ _ _ hml hcp
  exact ⟨1 + N + 1, reachIn_seq3 (moveLeft3 s (s + 1) ++ copyBitAtDist3 (s + 1) (s + 10) 1)
    (unmark3 (s + 10) sOut Sym3.M) (1 + N) 1 _ _ _ s1 hun⟩

/-!
**The marker-on-current-cell head moves, proved.**  `headMoveRight3` / `headMoveLeft3` move the head marker one cell by a
local symbol swap — no data-dependent walk — reusing the proven single-cell copies.  Next: rework the matcher to read the
current symbol at the marker, and assemble `apply3` — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3HeadMove

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3HeadMove.headMoveRight3_run
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3HeadMove.headMoveLeft3_run
