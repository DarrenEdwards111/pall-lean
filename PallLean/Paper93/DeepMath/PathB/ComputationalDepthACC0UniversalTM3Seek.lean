import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3Mark

/-!
# Entry 387 — universal-TM-table build: the seek-to-marker loop `seekMarkLeft` (proved)

This brick assembles the marker branch (`branchMark3`) and the left shuttle (`moveLeft3`, entry 386) into the
**distance-agnostic seek**: a cyclic machine that walks left until it reaches the marker `M`, *no matter how far*.  The
loop head reads the cell; on the marker it exits to `found`; otherwise it moves one cell left and loops back.

This is the construction that makes the *varying gap* irrelevant — the universal machine lays a marker at one operand and
shuttles to the other, finding the anchor on the way back by seeking, without any fixed-distance assumption.

## What is proved (clean axioms, no `sorry`)

* **`seekMarkLeft s found cont`** — `branchMark3 s found cont ++ moveLeft3 cont s` (cyclic: `cont` returns to the loop
  head `s`).
* **`seekMarkLeft_run`** (PROVED) — if the marker is at position `p` and the `d` cells `p+1 … p+d` above it are all
  non-marker, the machine drives from the loop head `(s, p+d, tp)` to `(found, p, tp)` (`∃` step count), tape identical —
  by induction on the distance `d`.

## Honest scope

This is the **seek-to-marker loop**, the second cyclic loop pattern realised over the 3-symbol model.  It does **not**
yet build the marker two-pointer comparison, nor the rule-table loop.  Building those fragment by fragment is the genuine
remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Seek

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn reachIn_add)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 readSym3 toNTM3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Mark
  (branchMark3 branchMark3_run_mark branchMark3_run_notmark moveLeft3 moveLeft3_run_eq)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_append_left3 reachIn_append_right3)

/-- **The seek-to-marker (left) machine (cyclic).**  Loop head `s`: on the marker go to `found`; otherwise move one cell
left (`moveLeft3 cont s`) and loop back to `s`. -/
def seekMarkLeft (s found cont : ℕ) : TMachine3 :=
  branchMark3 s found cont ++ moveLeft3 cont s

/-- **The seek reaches the marker (PROVED).**  With the marker at `p` and the `d` cells above it non-marker, the machine
goes from `(s, p+d, tp)` to `(found, p, tp)`, tape identical. -/
theorem seekMarkLeft_run (s found cont p : ℕ) (tp : List Sym3) (hmark : tp.getD p Sym3.O = Sym3.M) :
    ∀ d, (∀ k, 0 < k → k ≤ d → tp.getD (p + k) Sym3.O ≠ Sym3.M) → p + d < tp.length →
      ∃ N, reachIn (toNTM3 (seekMarkLeft s found cont)) N (s, p + d, tp) (found, p, tp) := by
  intro d
  induction d with
  | zero =>
      intro _ hbound
      refine ⟨1, ?_⟩
      have hm := branchMark3_run_mark s found cont p tp hmark (by omega)
      exact reachIn_append_left3 (branchMark3 s found cont) (moveLeft3 cont s) 1 _ _ hm
  | succ d ih =>
      intro hclear hbound
      have hcell : readSym3 (s, p + (d + 1), tp) ≠ Sym3.M := hclear (d + 1) (Nat.succ_pos d) (le_refl _)
      have hb1 := branchMark3_run_notmark s found cont (p + (d + 1)) tp hcell (by omega)
      have lift1 := reachIn_append_left3 (branchMark3 s found cont) (moveLeft3 cont s) 1 _ _ hb1
      have hb2 := moveLeft3_run_eq cont s (p + (d + 1)) tp (by omega)
      rw [show p + (d + 1) - 1 = p + d from by omega] at hb2
      have lift2 := reachIn_append_right3 (branchMark3 s found cont) (moveLeft3 cont s) 1 _ _ hb2
      have iter := (reachIn_add (toNTM3 (seekMarkLeft s found cont)) 1 1 _ _).mpr
        ⟨(cont, p + (d + 1), tp), lift1, lift2⟩
      obtain ⟨N, hrec⟩ := ih (fun k hk0 hkd => hclear k hk0 (by omega)) (by omega)
      refine ⟨(1 + 1) + N, ?_⟩
      exact (reachIn_add (toNTM3 (seekMarkLeft s found cont)) (1 + 1) N _ _).mpr
        ⟨(s, p + d, tp), iter, hrec⟩

/-!
**The seek-to-marker loop, proved.**  `seekMarkLeft` walks left to the marker regardless of distance, by induction on
the distance — the distance-agnostic anchor-find that makes the varying gap irrelevant.  Next: the rightward seek and
the marker two-pointer comparison, then the rule-table loop — fragment by verified fragment, not faked.  Not a
separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Seek

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Seek.seekMarkLeft_run
