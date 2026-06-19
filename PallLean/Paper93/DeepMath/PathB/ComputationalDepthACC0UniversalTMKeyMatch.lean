import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMCompareUnaryNe

/-!
# Entry 381 — universal-TM-table build: the full key match `keyMatch` (proved, match direction)

A transition's *key* is `(state, readSym)`: a unary state field followed by a symbol bit (the `encodeTransBits` layout
is `encodeNatBits state ++ readSym :: …`).  Matching a rule against the configuration means: the two state fields are
equal **and** the two symbol bits agree.  This brick composes the unary-field equality `compareUnary` (entry 379) with
the symbol-bit comparison `compareDistant` (entry 375) into the full key match.

The composition exploits the layout: after `compareUnary` compares the config state field (at offset `j`) with the rule
state field (at offset `j+m`), it ends in `matchSt` with the head at `j+L+m+1` — exactly the rule's symbol position.
The config symbol sits `m` cells to the left, so a `walkLeftK m` return lands the head on the config symbol, and a
`compareDistant m` then compares the two symbols.

## What is proved (clean axioms, no `sorry`)

* **`keyMatch m sT0 sF0 sCont matchSt noMatch bT0 bF0 fullMatch`** — `compareUnary m sT0 sF0 sCont matchSt noMatch ++
  walkLeftK m matchSt ++ compareDistant m (matchSt+m) bT0 bF0 fullMatch noMatch`.
* **`keyMatch_run_match`** (PROVED) — if the two state fields (length `L`) are equal **and** the two symbol bits agree,
  the machine drives from the loop head to `fullMatch` (`∃` step count), tape identical.

## Honest scope

This is the **full key match, match direction** — state-field equality composed with symbol-bit equality.  It does
**not** yet handle the no-match directions of the key match, nor the rule-table scan-and-match loop (which iterates the
key match over the rule list), nor the apply.  Building those fragment by fragment is the genuine remaining
construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMKeyMatch

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMachine toNTM)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMWalkLeftK (walkLeftK)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompareDistant (compareDistant)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompareUnary (compareUnary compareUnary_run_match)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMWalkLeftKEq (walkLeftK_run_eq)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompareDistantEq (compareDistant_run_eq)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompose (reachIn_seq)

/-- **The full key match machine.**  Compare the state fields (`compareUnary`), reposition to the config symbol
(`walkLeftK m matchSt`), then compare the symbol bits (`compareDistant`); reach `fullMatch` iff both agree. -/
def keyMatch (m sT0 sF0 sCont matchSt noMatch bT0 bF0 fullMatch : ℕ) : TMachine :=
  compareUnary m sT0 sF0 sCont matchSt noMatch ++ walkLeftK m matchSt ++
    compareDistant m (matchSt + m) bT0 bF0 fullMatch noMatch

/-- **Equal state fields and equal symbol bits ⇒ `fullMatch` (PROVED).**  State fields of length `L` (config at `j`,
rule at `j+m`) equal, and config symbol `j+L+1` equal to rule symbol `j+L+1+m`: the machine reaches `fullMatch`, tape
identical. -/
theorem keyMatch_run_match (m sT0 sF0 sCont matchSt noMatch bT0 bF0 fullMatch L j : ℕ) (tp : List Bool)
    (htrueA : ∀ i, i < L → tp.getD (j + i) false = true) (htrueB : ∀ i, i < L → tp.getD (j + m + i) false = true)
    (hsepA : tp.getD (j + L) false = false) (hsepB : tp.getD (j + m + L) false = false)
    (hsym : tp.getD (j + L + 1) false = tp.getD ((j + L + 1) + m) false)
    (hbound : j + L + m + 1 < tp.length) :
    ∃ N, reachIn (toNTM (keyMatch m sT0 sF0 sCont matchSt noMatch bT0 bF0 fullMatch)) N
      (sCont + m, j, tp) (fullMatch, (j + L + 1) + m + 1, tp) := by
  obtain ⟨N1, run1⟩ := compareUnary_run_match m sT0 sF0 sCont matchSt noMatch L j tp
    htrueA htrueB hsepA hsepB (by omega)
  -- run1 : reachIn (compareUnary ...) N1 (sCont+m, j, tp) (matchSt, j+L+m+1, tp)
  have run2 := walkLeftK_run_eq m matchSt (j + L + m + 1) tp (by omega)
  rw [show j + L + m + 1 - m = j + L + 1 from by omega] at run2
  -- run2 : reachIn (walkLeftK m matchSt) m (matchSt, j+L+m+1, tp) (matchSt+m, j+L+1, tp)
  have run3 := compareDistant_run_eq m (matchSt + m) bT0 bF0 fullMatch noMatch (j + L + 1) tp hsym (by omega)
  -- run3 : reachIn (compareDistant ...) (m+2) (matchSt+m, j+L+1, tp) (fullMatch, (j+L+1)+m+1, tp)
  have c12 := reachIn_seq (compareUnary m sT0 sF0 sCont matchSt noMatch) (walkLeftK m matchSt)
    N1 m _ _ _ run1 run2
  have c123 := reachIn_seq (compareUnary m sT0 sF0 sCont matchSt noMatch ++ walkLeftK m matchSt)
    (compareDistant m (matchSt + m) bT0 bF0 fullMatch noMatch) (N1 + m) (m + 2) _ _ _ c12 run3
  exact ⟨_, c123⟩

/-!
**The full key match (match direction), proved.**  `keyMatch` composes state-field equality with symbol-bit equality,
exploiting the `encodeTransBits` layout (the head after the state compare lands exactly on the rule symbol).  Next: the
no-match directions, then the rule-table scan-and-match loop (iterating the key match over the rule list), then the
apply — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMKeyMatch

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMKeyMatch.keyMatch_run_match
