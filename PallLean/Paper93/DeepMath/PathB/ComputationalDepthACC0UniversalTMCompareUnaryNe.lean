import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMCompareUnary

/-!
# Entry 380 — universal-TM-table build: the unary comparison mismatch direction `compareUnary_run_ne` (proved)

Entry 379 proved that two *equal* unary fields drive `compareUnary` to `matchSt`.  This brick proves the complementary
*mismatch* outcome: if the two fields agree on a `true`-prefix of length `k` but the cells **differ** at position `k`
(a genuine disagreement — including the unequal-length case, where one field's separator meets the other's `true`),
the loop reaches `noMatch`.

Same cyclic structure as the match case (induction on the agreeing-prefix length `k`), but the base step is a
`compareStep3` *no-match* instead of a *match*.

## What is proved (clean axioms, no `sorry`)

* **`compareUnary_run_ne`** (PROVED) — if cells `j+i`, `j+m+i` are both `true` for `i < k` and `tp.getD (j+k) false ≠
  tp.getD (j+m+k) false`, then `∃ N, reachIn (toNTM (compareUnary m sT0 sF0 sCont matchSt noMatch)) N (sCont+m, j, tp)
  (noMatch, j+k+m+1, tp)`: the loop reaches `noMatch`, tape identical.

## Honest scope

This is the **mismatch direction** of the unary-field comparison, completing (with entry 379) its match/no-match
outcomes.  It does **not** yet compose with the symbol-bit compare into the full key comparison, nor the rule-table
scan-and-match.  Building those fragment by fragment is the genuine remaining construction, **not faked**.  Nothing here
is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompareUnaryNe

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (toNTM)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn reachIn_add)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMWalkLeftK (walkLeftK)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompareStep3
  (compareStep3 compareStep3_run_cont compareStep3_run_ne)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMWalkLeftKEq (walkLeftK_run_eq)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompareUnary (compareUnary)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompose (reachIn_append_left reachIn_append_right)

/-- **A prefix-agreeing mismatch drives the loop to `noMatch` (PROVED).**  If the two fields agree (both `true`) for
`i < k` and differ at position `k`, the comparison reaches `noMatch` at head `j+k+m+1`, tape identical. -/
theorem compareUnary_run_ne (m sT0 sF0 sCont matchSt noMatch : ℕ) :
    ∀ (k j : ℕ) (tp : List Bool),
      (∀ i, i < k → tp.getD (j + i) false = true) →
      (∀ i, i < k → tp.getD (j + m + i) false = true) →
      tp.getD (j + k) false ≠ tp.getD (j + m + k) false →
      j + m + k + 1 < tp.length →
      ∃ N, reachIn (toNTM (compareUnary m sT0 sF0 sCont matchSt noMatch)) N
        (sCont + m, j, tp) (noMatch, j + k + m + 1, tp) := by
  intro k
  induction k with
  | zero =>
      intro j tp _ _ hdiff hbound
      have hstep := compareStep3_run_ne m (sCont + m) sT0 sF0 sCont matchSt noMatch j tp (by simpa using hdiff) (by omega)
      refine ⟨m + 2, ?_⟩
      exact reachIn_append_left (compareStep3 m (sCont + m) sT0 sF0 sCont matchSt noMatch)
        (walkLeftK m sCont) (m + 2) _ _ hstep
  | succ k ih =>
      intro j tp htrueA htrueB hdiff hbound
      have hcA : tp.getD (j + 0) false = true := by simpa using htrueA 0 (by omega)
      have hcB : tp.getD (j + m + 0) false = true := by simpa using htrueB 0 (by omega)
      have hcont := compareStep3_run_cont m (sCont + m) sT0 sF0 sCont matchSt noMatch j tp
        (by simpa using hcA) (by simpa using hcB) (by omega)
      have liftC := reachIn_append_left (compareStep3 m (sCont + m) sT0 sF0 sCont matchSt noMatch)
        (walkLeftK m sCont) (m + 2) _ _ hcont
      have hwalk := walkLeftK_run_eq m sCont (j + m + 1) tp (by omega)
      rw [show j + m + 1 - m = j + 1 from by omega] at hwalk
      have liftW := reachIn_append_right (compareStep3 m (sCont + m) sT0 sF0 sCont matchSt noMatch)
        (walkLeftK m sCont) m _ _ hwalk
      have iter := (reachIn_add (toNTM (compareUnary m sT0 sF0 sCont matchSt noMatch)) (m + 2) m _ _).mpr
        ⟨(sCont, j + m + 1, tp), liftC, liftW⟩
      obtain ⟨N, hrec⟩ := ih (j + 1) tp
        (fun i hi => by have := htrueA (i + 1) (by omega); simpa [show j + (i + 1) = j + 1 + i from by omega] using this)
        (fun i hi => by have := htrueB (i + 1) (by omega); simpa [show j + m + (i + 1) = j + 1 + m + i from by omega] using this)
        (by have := hdiff; simpa [show j + (k + 1) = j + 1 + k from by omega,
          show j + m + (k + 1) = j + 1 + m + k from by omega] using this)
        (by omega)
      refine ⟨(m + 2 + m) + N, ?_⟩
      have hcomp := (reachIn_add (toNTM (compareUnary m sT0 sF0 sCont matchSt noMatch)) (m + 2 + m) N _ _).mpr
        ⟨(sCont + m, j + 1, tp), iter, hrec⟩
      rw [show j + 1 + k + m + 1 = j + (k + 1) + m + 1 from by omega] at hcomp
      exact hcomp

/-!
**The unary comparison mismatch direction, proved.**  With entry 379, `compareUnary` now decides equality of two unary
fields: `matchSt` on equal fields, `noMatch` on a prefix-agreeing disagreement (including unequal lengths).  Next: the
full key comparison (state field + symbol bit) and the rule-table scan-and-match — fragment by verified fragment, not
faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompareUnaryNe

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompareUnaryNe.compareUnary_run_ne
