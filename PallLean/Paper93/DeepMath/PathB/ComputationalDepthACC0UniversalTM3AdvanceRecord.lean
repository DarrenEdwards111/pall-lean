import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3SkipOnes

/-!
# Entry 469 — generic scan loop: record-advance `advanceRecord3` (proved)

The second fixed-state component of the generic rule-table scan loop (entry 468 began it).  A record is a unary `I`-field
of length `b`, the separator `O`, then a one-cell symbol — occupying `b+2` cells.  To move to the *next* record, a generic
loop consumes the unary field (`skipOnesRight`, 468), then steps past the separator and the symbol.

`advanceRecord3 s m1 m2 stop cont := skipOnesRight s m1 cont ++ moveRight3 m1 m2 ++ moveRight3 m2 stop` — a fixed-size
machine driving the head from one record start to the next, regardless of the field length.

## What is proved (clean axioms, no `sorry`)

* **`advanceRecord3 s m1 m2 stop cont`** — the record-advance machine.
* **`advanceRecord3_run`** (PROVED) — with `h … h+b-1` all `I`, `h+b = O` (the separator), and `h+b+1 < tp.length`: `∃ N,
  reachIn N (s, h, tp) (stop, h+b+2, tp)` — the head reaches the next record start, tape identical.

## Honest scope

This is the **record-advance** component.  It does **not** yet build the per-record key comparison, the table-end test,
the full scan loop, nor a fixed `U` / `EmitsEncodedStepEx3`.  Building those fragment by fragment is the genuine remaining
construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3AdvanceRecord

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 toNTM3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Move (moveRight3 moveRight3_run_eq)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_seq3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3SkipOnes (skipOnesRight skipOnesRight_run)

/-- **The record-advance machine.**  Consume the unary field, then step past the separator and the symbol. -/
def advanceRecord3 (s m1 m2 stop cont : ℕ) : TMachine3 :=
  skipOnesRight s m1 cont ++ moveRight3 m1 m2 ++ moveRight3 m2 stop

/-- **The record-advance reaches the next record start (PROVED).** -/
theorem advanceRecord3_run (s m1 m2 stop cont : ℕ) (tp : List Sym3) (b h : ℕ)
    (hones : ∀ k, k < b → tp.getD (h + k) Sym3.O = Sym3.I) (hsep : tp.getD (h + b) Sym3.O = Sym3.O)
    (hbound : h + b + 1 < tp.length) :
    ∃ N, reachIn (toNTM3 (advanceRecord3 s m1 m2 stop cont)) N (s, h, tp) (stop, h + b + 2, tp) := by
  obtain ⟨NA, hA⟩ := skipOnesRight_run s m1 cont tp b h hones (by rw [hsep]; decide) (by omega)
  have hB := moveRight3_run_eq m1 m2 (h + b) tp (by omega)
  have hC := moveRight3_run_eq m2 stop (h + b + 1) tp (by omega)
  have runAB := reachIn_seq3 (skipOnesRight s m1 cont) (moveRight3 m1 m2) NA 1 _ _ _ hA hB
  refine ⟨NA + 1 + 1, ?_⟩
  have hpos : h + b + 1 + 1 = h + b + 2 := by omega
  rw [hpos] at hC
  exact reachIn_seq3 (skipOnesRight s m1 cont ++ moveRight3 m1 m2) (moveRight3 m2 stop) (NA + 1) 1 _ _ _ runAB hC

/-!
**The record-advance, proved.**  `advanceRecord3` walks from one record start to the next regardless of the field length —
a fixed-state component of the generic scan loop.  Next: the per-record key comparison and the table-end test, then the
full fixed-size rule-table scan loop — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3AdvanceRecord

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3AdvanceRecord.advanceRecord3_run
