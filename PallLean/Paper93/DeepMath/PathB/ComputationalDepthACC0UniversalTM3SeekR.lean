import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3Seek

/-!
# Entry 388 — universal-TM-table build: the rightward seek-to-marker `seekMarkRight` (proved)

The mirror of `seekMarkLeft` (entry 387): a cyclic machine that walks **right** until it reaches the marker `M`, no
matter how far.  The marker comparison shuttles in both directions — mark one operand, walk right to the other, and
later seek back — so it needs both seeks.

## What is proved (clean axioms, no `sorry`)

* **`seekMarkRight s found cont`** — `branchMark3 s found cont ++ moveRight3 cont s` (cyclic: `cont` returns to the loop
  head `s`).
* **`seekMarkRight_run`** (PROVED) — if the marker is at `h+d` and the `d` cells `h … h+d-1` below it are non-marker,
  the machine drives from `(s, h, tp)` to `(found, h+d, tp)` (`∃` step count), tape identical — by induction on `d`.

## Honest scope

This is the **rightward seek**, completing the distance-agnostic seek pair.  It does **not** yet build the marker
two-pointer comparison, nor the rule-table loop.  Building those fragment by fragment is the genuine remaining
construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3SeekR

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn reachIn_add)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 readSym3 toNTM3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Move (moveRight3 moveRight3_run_eq)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Mark
  (branchMark3 branchMark3_run_mark branchMark3_run_notmark)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_append_left3 reachIn_append_right3)

/-- **The seek-to-marker (right) machine (cyclic).**  Loop head `s`: on the marker go to `found`; otherwise move one
cell right (`moveRight3 cont s`) and loop back. -/
def seekMarkRight (s found cont : ℕ) : TMachine3 :=
  branchMark3 s found cont ++ moveRight3 cont s

/-- **The rightward seek reaches the marker (PROVED).**  With the marker at `h+d` and the `d` cells below it
non-marker, the machine goes from `(s, h, tp)` to `(found, h+d, tp)`, tape identical. -/
theorem seekMarkRight_run (s found cont : ℕ) (tp : List Sym3) :
    ∀ (d h : ℕ), tp.getD (h + d) Sym3.O = Sym3.M → (∀ k, k < d → tp.getD (h + k) Sym3.O ≠ Sym3.M) →
      h + d < tp.length →
      ∃ N, reachIn (toNTM3 (seekMarkRight s found cont)) N (s, h, tp) (found, h + d, tp) := by
  intro d
  induction d with
  | zero =>
      intro h hmark _ hbound
      refine ⟨1, ?_⟩
      have hm := branchMark3_run_mark s found cont h tp (by simpa using hmark) (by omega)
      exact reachIn_append_left3 (branchMark3 s found cont) (moveRight3 cont s) 1 _ _ hm
  | succ d ih =>
      intro h hmark hclear hbound
      have hcell : readSym3 (s, h, tp) ≠ Sym3.M := by simpa using hclear 0 (Nat.succ_pos d)
      have hb1 := branchMark3_run_notmark s found cont h tp hcell (by omega)
      have lift1 := reachIn_append_left3 (branchMark3 s found cont) (moveRight3 cont s) 1 _ _ hb1
      have hb2 := moveRight3_run_eq cont s h tp (by omega)
      have lift2 := reachIn_append_right3 (branchMark3 s found cont) (moveRight3 cont s) 1 _ _ hb2
      have iter := (reachIn_add (toNTM3 (seekMarkRight s found cont)) 1 1 _ _).mpr
        ⟨(cont, h, tp), lift1, lift2⟩
      obtain ⟨N, hrec⟩ := ih (h + 1)
        (by have := hmark; simpa [show h + 1 + d = h + (d + 1) from by omega] using this)
        (fun k hk => by have := hclear (k + 1) (by omega); simpa [show h + (k + 1) = h + 1 + k from by omega] using this)
        (by omega)
      rw [show h + 1 + d = h + (d + 1) from by omega] at hrec
      refine ⟨(1 + 1) + N, ?_⟩
      exact (reachIn_add (toNTM3 (seekMarkRight s found cont)) (1 + 1) N _ _).mpr
        ⟨(s, h + 1, tp), iter, hrec⟩

/-!
**The rightward seek, proved.**  `seekMarkRight` walks right to the marker regardless of distance, completing the seek
pair (left/right).  Next: the marker two-pointer comparison (mark, shuttle, carry, seek back, compare), then the
rule-table loop — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3SeekR

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3SeekR.seekMarkRight_run
