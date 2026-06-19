import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMCompareStep3

/-!
# Entry 379 — universal-TM-table build: the unary-field equality comparison `compareUnary` (proved, match direction)

This brick **loops** the three-way step `compareStep3` (entry 378) into a comparison of two whole unary fields.  The
machine is *cyclic*: the `cont` exit of `compareStep3` is followed by a `walkLeftK` return that lands back at the loop
head, so the body repeats once per `true`-pair; the `matchSt` exit (aligned separators) leaves the loop with "equal".

The cycle closes by choosing the loop head to be `sCont + m` — exactly where the return walk `walkLeftK m sCont` ends.
(State overlaps are harmless: `reachIn` is existential, so a witnessing path suffices.)

This is the first **data-dependent loop** of the build: the run is proved by induction on the common field length `L`.

## What is proved (clean axioms, no `sorry`)

* **`compareUnary m sT0 sF0 sCont matchSt noMatch`** — `compareStep3 m (sCont+m) sT0 sF0 sCont matchSt noMatch ++
  walkLeftK m sCont`.
* **`compareUnary_run_match`** (PROVED) — two *equal* unary fields of length `L` (region A at `j`, region B at `j+m`)
  drive the machine from the loop head `(sCont+m, j, tp)` to `(matchSt, j+L+m+1, tp)`, tape identical (`∃` step count).

## Honest scope

This is the **unary-field equality comparison, match direction** — the first cyclic, data-dependent loop, proved by
induction on the field length.  It does **not** yet prove the mismatch/length-difference directions, nor compose with
the symbol-bit compare into the full key comparison, nor the rule-table scan-and-match.  Building those fragment by
fragment is the genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompareUnary

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMachine toNTM)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn reachIn_add)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMWalkLeftK (walkLeftK)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompareStep3
  (compareStep3 compareStep3_run_cont compareStep3_run_match)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMWalkLeftKEq (walkLeftK_run_eq)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompose (reachIn_append_left reachIn_append_right)

/-- **The unary-field equality comparison machine (cyclic).**  Loop head `sCont+m`: compare one cell pair; on `cont`
the `walkLeftK m sCont` return lands back at `sCont+m` (next pair); on `matchSt` the loop ends "equal". -/
def compareUnary (m sT0 sF0 sCont matchSt noMatch : ℕ) : TMachine :=
  compareStep3 m (sCont + m) sT0 sF0 sCont matchSt noMatch ++ walkLeftK m sCont

/-- **Two equal unary fields drive the loop to `matchSt` (PROVED).**  Fields of common length `L` at offsets `j`
(region A) and `j+m` (region B): from the loop head, the machine reaches `matchSt` at head `j+L+m+1`, tape identical. -/
theorem compareUnary_run_match (m sT0 sF0 sCont matchSt noMatch : ℕ) :
    ∀ (L j : ℕ) (tp : List Bool),
      (∀ i, i < L → tp.getD (j + i) false = true) →
      (∀ i, i < L → tp.getD (j + m + i) false = true) →
      tp.getD (j + L) false = false → tp.getD (j + m + L) false = false →
      j + m + L + 1 < tp.length →
      ∃ N, reachIn (toNTM (compareUnary m sT0 sF0 sCont matchSt noMatch)) N
        (sCont + m, j, tp) (matchSt, j + L + m + 1, tp) := by
  intro L
  induction L with
  | zero =>
      intro j tp _ _ hsepA hsepB hbound
      have hstep := compareStep3_run_match m (sCont + m) sT0 sF0 sCont matchSt noMatch j tp hsepA hsepB (by omega)
      refine ⟨m + 2, ?_⟩
      -- exit head `j + 0 + m + 1` is defeq to `j + m + 1`
      exact reachIn_append_left (compareStep3 m (sCont + m) sT0 sF0 sCont matchSt noMatch)
        (walkLeftK m sCont) (m + 2) _ _ hstep
  | succ L ih =>
      intro j tp htrueA htrueB hsepA hsepB hbound
      -- one iteration: compare the (true,true) pair at j, then return
      have hcA : tp.getD (j + 0) false = true := by simpa using htrueA 0 (by omega)
      have hcB : tp.getD (j + m + 0) false = true := by simpa using htrueB 0 (by omega)
      have hcont := compareStep3_run_cont m (sCont + m) sT0 sF0 sCont matchSt noMatch j tp
        (by simpa using hcA) (by simpa using hcB) (by omega)
      have liftC := reachIn_append_left (compareStep3 m (sCont + m) sT0 sF0 sCont matchSt noMatch)
        (walkLeftK m sCont) (m + 2) _ _ hcont
      -- liftC : reachIn compareUnary (m+2) (sCont+m, j, tp) (sCont, j+m+1, tp)
      have hwalk := walkLeftK_run_eq m sCont (j + m + 1) tp (by omega)
      rw [show j + m + 1 - m = j + 1 from by omega] at hwalk
      have liftW := reachIn_append_right (compareStep3 m (sCont + m) sT0 sF0 sCont matchSt noMatch)
        (walkLeftK m sCont) m _ _ hwalk
      -- liftW : reachIn compareUnary m (sCont, j+m+1, tp) (sCont+m, j+1, tp)
      have iter := (reachIn_add (toNTM (compareUnary m sT0 sF0 sCont matchSt noMatch)) (m + 2) m _ _).mpr
        ⟨(sCont, j + m + 1, tp), liftC, liftW⟩
      -- iter : reachIn compareUnary (m+2+m) (sCont+m, j, tp) (sCont+m, j+1, tp)
      obtain ⟨N, hrec⟩ := ih (j + 1) tp
        (fun i hi => by have := htrueA (i + 1) (by omega); simpa [show j + (i + 1) = j + 1 + i from by omega] using this)
        (fun i hi => by have := htrueB (i + 1) (by omega); simpa [show j + m + (i + 1) = j + 1 + m + i from by omega] using this)
        (by have := hsepA; simpa [show j + (L + 1) = j + 1 + L from by omega] using this)
        (by have := hsepB; simpa [show j + m + (L + 1) = j + 1 + m + L from by omega] using this)
        (by omega)
      -- hrec : reachIn compareUnary N (sCont+m, j+1, tp) (matchSt, (j+1)+L+m+1, tp)
      refine ⟨(m + 2 + m) + N, ?_⟩
      have hcomp := (reachIn_add (toNTM (compareUnary m sT0 sF0 sCont matchSt noMatch)) (m + 2 + m) N _ _).mpr
        ⟨(sCont + m, j + 1, tp), iter, hrec⟩
      rw [show j + 1 + L + m + 1 = j + (L + 1) + m + 1 from by omega] at hcomp
      exact hcomp

/-!
**The unary-field equality comparison (match direction), proved.**  `compareUnary` is the first cyclic, data-dependent
loop of the build: two equal unary fields drive it to `matchSt`, by induction on the field length, the `cont` return
closing the cycle at `sCont+m`.  Next: the mismatch/length-difference directions, the full key comparison (state field
+ symbol bit), and the rule-table scan-and-match — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompareUnary

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompareUnary.compareUnary_run_match
