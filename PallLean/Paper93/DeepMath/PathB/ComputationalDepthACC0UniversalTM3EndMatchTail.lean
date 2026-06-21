import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3MarkAdvance
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3SeekR

/-!
# Entry 489 — generic scan loop: the match-tail connector `endMatchTail` (proved)

The branching state-comparison loop reaches its match verdict by, *after* the config cursor has already hit its separator
(removed by the loop's config advance), seeking to the record cursor and advancing it onto its separator.  This brick is
that reusable connector — `endMatch` (entry 481) minus its leading config advance — stated generically over the tape so it
can attach after any config-end step.

`endMatchTail s skf skc rm rc matchSt := seekMarkRight s skf skc ++ markAdvance3 skf rm rc matchSt`.

## What is proved (clean axioms, no `sorry`)

* **`endMatchTail s skf skc rm rc matchSt`** — the match-tail machine.
* **`endMatchTail_run`** (PROVED) — head at `q`, record cursor `M` at `r ≥ q`, record separator `O` at `r+1`, the span
  `[q, r)` marker-free, in bounds: `∃ N, reachIn N (s, q, t) (matchSt, r+1, writeAt3 (writeAt3 t r I) (r+1) O)` — the record
  cursor removed (`r → I`), head on the separator.

## Honest scope

This is the **match-tail connector**.  It does **not** itself build the branching comparison loop, the full record
comparison, the scan-loop wiring, the generic apply, nor a fixed `U` / `EmitsEncodedStepEx3`.  Building those fragment by
fragment is the genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3EndMatchTail

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 writeAt3 toNTM3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_seq3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MarkAdvance (markAdvance3 markAdvance3_run_end)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3SeekR (seekMarkRight seekMarkRight_run)

/-- **The match-tail connector.**  Seek to the record cursor, then advance it onto its separator (→ `matchSt`). -/
def endMatchTail (s skf skc rm rc matchSt : ℕ) : TMachine3 :=
  seekMarkRight s skf skc ++ markAdvance3 skf rm rc matchSt

/-- **The match tail removes the record cursor and confirms match (PROVED).** -/
theorem endMatchTail_run (s skf skc rm rc matchSt : ℕ) (t : List Sym3) (q r : ℕ) (hq : q ≤ r)
    (hMrec : t.getD r Sym3.O = Sym3.M) (hRsep : t.getD (r + 1) Sym3.O = Sym3.O)
    (hclean : ∀ j, q ≤ j → j < r → t.getD j Sym3.O ≠ Sym3.M) (hbound : r + 1 < t.length) :
    ∃ N, reachIn (toNTM3 (endMatchTail s skf skc rm rc matchSt)) N
      (s, q, t) (matchSt, r + 1, writeAt3 (writeAt3 t r Sym3.I) (r + 1) Sym3.O) := by
  obtain ⟨N1, h1⟩ := seekMarkRight_run s skf skc t (r - q) q
    (by rw [show q + (r - q) = r from by omega]; exact hMrec)
    (fun k hk => hclean (q + k) (Nat.le_add_right q k) (by omega))
    (by rw [show q + (r - q) = r from by omega]; omega)
  rw [show q + (r - q) = r from by omega] at h1
  have h2 := markAdvance3_run_end skf rm rc matchSt r t hMrec hRsep
  exact ⟨N1 + 2, reachIn_seq3 (seekMarkRight s skf skc) (markAdvance3 skf rm rc matchSt) N1 2 _ _ _ h1 h2⟩

/-!
**The match-tail connector, proved.**  `endMatchTail` is the seek+advance tail that confirms a match after a config-end
step, stated generically — ready to attach to the branching comparison loop.  Next: the branching loop itself (tandem walk
with verdict exits), then the full record comparison and scan-loop wiring — fragment by verified fragment, not faked.  Not a
separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3EndMatchTail

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3EndMatchTail.endMatchTail_run
