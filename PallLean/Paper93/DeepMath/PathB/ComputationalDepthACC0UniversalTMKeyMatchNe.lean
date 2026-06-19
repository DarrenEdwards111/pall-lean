import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMKeyMatch

/-!
# Entry 382 — universal-TM-table build: the key match no-match directions (proved)

Entry 381 proved that a rule whose key *equals* the configuration's drives `keyMatch` to `fullMatch`.  This brick
proves the two ways a key *fails* to match, both reaching `noMatch`:

* **state fields differ** — `compareUnary` reaches `noMatch` directly (the appended symbol-compare phase, entered only at
  `matchSt`, is never run);
* **state fields equal but symbol bits differ** — `compareUnary` reaches `matchSt`, the head repositions, and the
  symbol comparison `compareDistant` reaches `noMatch`.

Together with entry 381 this makes `keyMatch` a complete per-rule decision: `fullMatch` iff the keys are equal,
`noMatch` otherwise.

## What is proved (clean axioms, no `sorry`)

* **`keyMatch_run_ne_state`** (PROVED) — state fields differ (agree on a `true`-prefix `k`, differ at `k`) ⇒ reaches
  `noMatch`, tape identical.
* **`keyMatch_run_ne_sym`** (PROVED) — state fields equal (length `L`) but symbol bits differ ⇒ reaches `noMatch`, tape
  identical.

## Honest scope

These complete the **per-rule key decision** (`fullMatch`/`noMatch`).  They do **not** yet assemble the rule-table
scan-and-match loop (iterating the key match over the rule list), nor the apply.  Building those fragment by fragment is
the genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMKeyMatchNe

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (toNTM)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMWalkLeftK (walkLeftK)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompareDistant (compareDistant)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompareUnary (compareUnary compareUnary_run_match)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompareUnaryNe (compareUnary_run_ne)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMWalkLeftKEq (walkLeftK_run_eq)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompareDistantEq (compareDistant_run_ne)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMKeyMatch (keyMatch)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompose (reachIn_seq reachIn_append_left)

/-- **State fields differ ⇒ `noMatch` (PROVED).**  `compareUnary` reaches `noMatch`; the appended symbol phase is never
entered. -/
theorem keyMatch_run_ne_state (m sT0 sF0 sCont matchSt noMatch bT0 bF0 fullMatch k j : ℕ) (tp : List Bool)
    (htrueA : ∀ i, i < k → tp.getD (j + i) false = true) (htrueB : ∀ i, i < k → tp.getD (j + m + i) false = true)
    (hdiff : tp.getD (j + k) false ≠ tp.getD (j + m + k) false) (hbound : j + m + k + 1 < tp.length) :
    ∃ N, reachIn (toNTM (keyMatch m sT0 sF0 sCont matchSt noMatch bT0 bF0 fullMatch)) N
      (sCont + m, j, tp) (noMatch, j + k + m + 1, tp) := by
  obtain ⟨N, run⟩ := compareUnary_run_ne m sT0 sF0 sCont matchSt noMatch k j tp htrueA htrueB hdiff hbound
  refine ⟨N, ?_⟩
  exact reachIn_append_left (compareUnary m sT0 sF0 sCont matchSt noMatch ++ walkLeftK m matchSt)
    (compareDistant m (matchSt + m) bT0 bF0 fullMatch noMatch) N _ _
    (reachIn_append_left (compareUnary m sT0 sF0 sCont matchSt noMatch) (walkLeftK m matchSt) N _ _ run)

/-- **State fields equal but symbol bits differ ⇒ `noMatch` (PROVED).** -/
theorem keyMatch_run_ne_sym (m sT0 sF0 sCont matchSt noMatch bT0 bF0 fullMatch L j : ℕ) (tp : List Bool)
    (htrueA : ∀ i, i < L → tp.getD (j + i) false = true) (htrueB : ∀ i, i < L → tp.getD (j + m + i) false = true)
    (hsepA : tp.getD (j + L) false = false) (hsepB : tp.getD (j + m + L) false = false)
    (hsymne : tp.getD (j + L + 1) false ≠ tp.getD ((j + L + 1) + m) false) (hbound : j + L + m + 1 < tp.length) :
    ∃ N, reachIn (toNTM (keyMatch m sT0 sF0 sCont matchSt noMatch bT0 bF0 fullMatch)) N
      (sCont + m, j, tp) (noMatch, (j + L + 1) + m + 1, tp) := by
  obtain ⟨N1, run1⟩ := compareUnary_run_match m sT0 sF0 sCont matchSt noMatch L j tp
    htrueA htrueB hsepA hsepB (by omega)
  have run2 := walkLeftK_run_eq m matchSt (j + L + m + 1) tp (by omega)
  rw [show j + L + m + 1 - m = j + L + 1 from by omega] at run2
  have run3 := compareDistant_run_ne m (matchSt + m) bT0 bF0 fullMatch noMatch (j + L + 1) tp hsymne (by omega)
  have c12 := reachIn_seq (compareUnary m sT0 sF0 sCont matchSt noMatch) (walkLeftK m matchSt)
    N1 m _ _ _ run1 run2
  have c123 := reachIn_seq (compareUnary m sT0 sF0 sCont matchSt noMatch ++ walkLeftK m matchSt)
    (compareDistant m (matchSt + m) bT0 bF0 fullMatch noMatch) (N1 + m) (m + 2) _ _ _ c12 run3
  exact ⟨_, c123⟩

/-!
**The key match no-match directions, proved.**  With entry 381, `keyMatch` is a complete per-rule decision: `fullMatch`
iff the rule's key equals the configuration's, `noMatch` otherwise (whether the state fields or the symbol bits
disagree).  Next: the rule-table scan-and-match loop (iterate the key match over the rule list, branching apply/next),
then the apply — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMKeyMatchNe

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMKeyMatchNe.keyMatch_run_ne_state
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMKeyMatchNe.keyMatch_run_ne_sym
