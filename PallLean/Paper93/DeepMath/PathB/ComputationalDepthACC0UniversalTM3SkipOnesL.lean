import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3SkipOnes

/-!
# Entry 470 — generic scan loop: leftward unary-consume `skipOnesLeft` (proved)

The leftward mirror of `skipOnesRight` (entry 468): a fixed-state loop that walks **left** over `I`s until a non-`I` cell.
The marker two-pointer comparison the generic scan loop needs shuttles in both directions (consume forward, return back), so
it needs both unary-consume directions.

`skipOnesLeft s stop cont := branchOne3 s cont stop ++ moveLeft3 cont s` — a fixed 3-state machine with a back-edge.

## What is proved (clean axioms, no `sorry`)

* **`skipOnesLeft s stop cont`** — the leftward unary-consume loop.
* **`skipOnesLeft_run`** (PROVED) — with the cells `p+1 … p+d` all `I` and `p` non-`I`, the machine drives `(s, p+d, tp) →
  (stop, p, tp)` (`∃` step count), tape identical — by induction on `d`, machine fixed.

## Honest scope

This is the **leftward unary-consume** component.  It does **not** yet build the per-record key comparison, the table-end
test, the full scan loop, nor a fixed `U` / `EmitsEncodedStepEx3`.  Building those fragment by fragment is the genuine
remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3SkipOnesL

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn reachIn_add)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 readSym3 toNTM3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Mark (moveLeft3 moveLeft3_run_eq)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_append_left3 reachIn_append_right3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3SkipOnes (branchOne3 branchOne3_run_one branchOne3_run_stop)

/-- **The consume-unary-field (leftward) machine (cyclic).**  Loop head `s`: on `I` move one cell left and loop; on a
non-`I` cell go to `stop`. -/
def skipOnesLeft (s stop cont : ℕ) : TMachine3 :=
  branchOne3 s cont stop ++ moveLeft3 cont s

/-- **The leftward unary-consume loop reaches the delimiter (PROVED).** -/
theorem skipOnesLeft_run (s stop cont p : ℕ) (tp : List Sym3) (hstop : tp.getD p Sym3.O ≠ Sym3.I) :
    ∀ d, (∀ k, 0 < k → k ≤ d → tp.getD (p + k) Sym3.O = Sym3.I) → p + d < tp.length →
      ∃ N, reachIn (toNTM3 (skipOnesLeft s stop cont)) N (s, p + d, tp) (stop, p, tp) := by
  intro d
  induction d with
  | zero =>
      intro _ hbound
      refine ⟨1, ?_⟩
      have hb := branchOne3_run_stop s cont stop p tp (by simpa using hstop) (by omega)
      exact reachIn_append_left3 (branchOne3 s cont stop) (moveLeft3 cont s) 1 _ _ hb
  | succ d ih =>
      intro hones hbound
      have hcell : readSym3 (s, p + (d + 1), tp) = Sym3.I := by
        simpa using hones (d + 1) (Nat.succ_pos d) (le_refl _)
      have hb1 := branchOne3_run_one s cont stop (p + (d + 1)) tp hcell (by omega)
      have lift1 := reachIn_append_left3 (branchOne3 s cont stop) (moveLeft3 cont s) 1 _ _ hb1
      have hb2 := moveLeft3_run_eq cont s (p + (d + 1)) tp (by omega)
      rw [show p + (d + 1) - 1 = p + d from by omega] at hb2
      have lift2 := reachIn_append_right3 (branchOne3 s cont stop) (moveLeft3 cont s) 1 _ _ hb2
      have iter := (reachIn_add (toNTM3 (skipOnesLeft s stop cont)) 1 1 _ _).mpr
        ⟨(cont, p + (d + 1), tp), lift1, lift2⟩
      obtain ⟨N, hrec⟩ := ih (fun k hk0 hkd => hones k hk0 (by omega)) (by omega)
      refine ⟨(1 + 1) + N, ?_⟩
      exact (reachIn_add (toNTM3 (skipOnesLeft s stop cont)) (1 + 1) N _ _).mpr
        ⟨(s, p + d, tp), iter, hrec⟩

/-!
**The leftward unary-consume, proved.**  `skipOnesLeft` walks left past a unary field regardless of length, completing the
bidirectional unary-consume pair for the comparison shuttle.  Next: the per-record key comparison and the table-end test,
then the full fixed-size scan loop — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3SkipOnesL

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3SkipOnesL.skipOnesLeft_run
