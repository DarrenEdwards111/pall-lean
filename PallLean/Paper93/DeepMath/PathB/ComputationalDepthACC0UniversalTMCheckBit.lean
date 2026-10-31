import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMBranch

/-!
# Entry 352 — universal-TM-table build: the expected-bit checker `checkBit` (proved)

`branchBit` (entry 351) inspects a cell and routes the control state, staying in place.  To *verify a known bit
pattern* — the core of comparing a rule's key against an expected value — we need to read a cell, **compare it to an
expected constant bit `b`**, advance past it, and route to a continue-state on a match or a fail-state on a mismatch.
That is `checkBit b s sCont sFail`.

Chaining `checkBit b₁ s₀ s₁ F ++ checkBit b₂ s₁ s₂ F ++ …` (all failures funnelled to a common `F`) verifies a fixed
bit pattern, reaching the final continue-state iff every bit matched — the mechanism the rule-table key match is built
from.

## What is proved (clean axioms, no `sorry`)

* **`checkBit b s sCont sFail`** — the machine `[((s,b),(sCont,b,→)), ((s,!b),(sFail,!b,→))]`: read the cell, write it
  back, move right, and go to `sCont` if it equalled `b`, else `sFail`.
* **`checkBit_step_match` / `checkBit_step_fail`** (PROVED) — the single-step behaviours: reading `b` advances to
  `sCont`, reading `!b` advances to `sFail`.
* **`checkBit_run_match` / `checkBit_run_fail`** (PROVED) — the one-step runs, preserving the tape: a cell equal to `b`
  reaches `(sCont, h+1, tp')`, a cell equal to `!b` reaches `(sFail, h+1, tp')`, with `tp'` agreeing with `tp`
  everywhere.

## Honest scope

This builds the **expected-bit checker** — read, compare-to-constant, advance, branch.  It does **not** yet chain
checkers into a full pattern match, nor compare two *tape* regions (the two-pointer key match), nor the rule-table loop,
nor the apply.  Building those fragment by fragment is the genuine remaining construction, **not faked**.  Nothing here
is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCheckBit

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM
  (TMachine Move concreteStep readSym applyTrans moveHead writeAt toNTM)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanNat (writeAt_getD_self)

/-- **The expected-bit checker.**  At state `s`: read the cell, write it back, move right, and go to `sCont` if the
cell equalled the expected bit `b`, else `sFail`. -/
def checkBit (b : Bool) (s sCont sFail : ℕ) : TMachine :=
  [((s, b), (sCont, b, (1 : Move))), ((s, !b), (sFail, !b, (1 : Move)))]

/-- **`checkBit` on a match (PROVED).**  At `(s, j, tp)` reading `b`, it advances to `(sCont, j+1, writeAt tp j b)`. -/
theorem checkBit_step_match (b : Bool) (s sCont sFail j : ℕ) (tp : List Bool) (h : tp.getD j false = b) :
    concreteStep (checkBit b s sCont sFail) (s, j, tp) (sCont, j + 1, writeAt tp j b) := by
  refine ⟨((s, b), (sCont, b, (1 : Move))), ?_, ?_, ?_⟩
  · simp [checkBit]
  · show (s, b) = ((s, j, tp).1, readSym (s, j, tp))
    simp only [readSym, h]
  · simp [applyTrans, moveHead]

/-- **`checkBit` on a mismatch (PROVED).**  At `(s, j, tp)` reading `!b`, it advances to `(sFail, j+1, writeAt tp j !b)`. -/
theorem checkBit_step_fail (b : Bool) (s sCont sFail j : ℕ) (tp : List Bool) (h : tp.getD j false = !b) :
    concreteStep (checkBit b s sCont sFail) (s, j, tp) (sFail, j + 1, writeAt tp j (!b)) := by
  refine ⟨((s, !b), (sFail, !b, (1 : Move))), ?_, ?_, ?_⟩
  · simp [checkBit]
  · show (s, !b) = ((s, j, tp).1, readSym (s, j, tp))
    simp only [readSym, h]
  · simp [applyTrans, moveHead]

/-- **The one-step check run on a match (PROVED).**  A cell equal to `b` at offset `h` advances to `(sCont, h+1, tp')`,
preserving the tape. -/
theorem checkBit_run_match (b : Bool) (s sCont sFail h : ℕ) (tp : List Bool) (hb : tp.getD h false = b) :
    ∃ tp', reachIn (toNTM (checkBit b s sCont sFail)) 1 (s, h, tp) (sCont, h + 1, tp') ∧
      ∀ q, tp'.getD q false = tp.getD q false := by
  refine ⟨writeAt tp h b, ⟨_, checkBit_step_match b s sCont sFail h tp hb, rfl⟩, ?_⟩
  intro q
  have hwb : (writeAt tp h b).getD q false = (writeAt tp h (tp.getD h false)).getD q false := by rw [hb]
  rw [hwb, writeAt_getD_self]

/-- **The one-step check run on a mismatch (PROVED).**  A cell equal to `!b` at offset `h` advances to
`(sFail, h+1, tp')`, preserving the tape. -/
theorem checkBit_run_fail (b : Bool) (s sCont sFail h : ℕ) (tp : List Bool) (hb : tp.getD h false = !b) :
    ∃ tp', reachIn (toNTM (checkBit b s sCont sFail)) 1 (s, h, tp) (sFail, h + 1, tp') ∧
      ∀ q, tp'.getD q false = tp.getD q false := by
  refine ⟨writeAt tp h (!b), ⟨_, checkBit_step_fail b s sCont sFail h tp hb, rfl⟩, ?_⟩
  intro q
  have hwb : (writeAt tp h (!b)).getD q false = (writeAt tp h (tp.getD h false)).getD q false := by rw [hb]
  rw [hwb, writeAt_getD_self]

/-!
**The expected-bit checker, proved.**  `checkBit b` reads a cell, compares it to the constant `b`, advances, and routes
to continue/fail — so a chain of checkers (failures funnelled to a common state) verifies a fixed bit pattern.  Next:
chain checkers into a pattern match, then the two-region key comparison and the rule-table scan-and-match loop, then the
apply — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCheckBit

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCheckBit.checkBit_step_match
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCheckBit.checkBit_run_match
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCheckBit.checkBit_run_fail
