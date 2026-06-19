import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMScanTrans

/-!
# Entry 351 — universal-TM-table build: the one-bit branch machine `branchBit` (proved)

Everything in the transition-table build so far (entries 344–350) only *advances* the head.  Locating the matching
rule in the encoded rule table requires a genuinely new capability: **branching** on what is read — going to one of two
states depending on the current symbol.  This brick builds that decision atom.

`branchBit s sTrue sFalse` inspects the current cell and, *without moving the head* (move = `2`, stay) and writing the
symbol back (so the tape is untouched), goes to `sTrue` if it read `true` and `sFalse` if it read `false`.  It is the
primitive from which equality tests and the rule-table scan-and-match are assembled.

## What is proved (clean axioms, no `sorry`)

* **`branchBit s sTrue sFalse`** — the machine `[((s,true),(sTrue,true,stay)), ((s,false),(sFalse,false,stay))]`.
* **`branchBit_step_true` / `branchBit_step_false`** (PROVED) — at `(s, j, tp)` reading `true` (resp. `false`), it steps
  to `(sTrue, j, …)` (resp. `(sFalse, j, …)`) — state branches, head unchanged.
* **`branchBit_run_true` / `branchBit_run_false`** (PROVED) — the one-step branch run, preserving the tape and the head
  position: reading `true` reaches `(sTrue, h, tp')`, reading `false` reaches `(sFalse, h, tp')`, with `tp'` agreeing
  with `tp` everywhere.

## Honest scope

This builds the **branch/decision atom** for the rule table — the first machine that does something other than scan
forward.  It does **not** yet assemble an equality test between two encoded fields, nor the rule-table scan-and-match
loop, nor the apply.  Building those fragment by fragment is the genuine remaining construction, **not faked**.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMBranch

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM
  (TMachine Move concreteStep readSym applyTrans moveHead writeAt toNTM)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanNat (writeAt_getD_self)

/-- **The one-bit branch machine.**  At state `s`: read the cell, write it back, *stay* (head unchanged), and go to
`sTrue` on `true` or `sFalse` on `false`. -/
def branchBit (s sTrue sFalse : ℕ) : TMachine :=
  [((s, true), (sTrue, true, (2 : Move))), ((s, false), (sFalse, false, (2 : Move)))]

/-- **`branchBit` on `true` (PROVED).**  At `(s, j, tp)` reading `true`, it steps to `(sTrue, j, writeAt tp j true)` —
state branches to `sTrue`, head unchanged. -/
theorem branchBit_step_true (s sTrue sFalse j : ℕ) (tp : List Bool) (h : tp.getD j false = true) :
    concreteStep (branchBit s sTrue sFalse) (s, j, tp) (sTrue, j, writeAt tp j true) := by
  refine ⟨((s, true), (sTrue, true, (2 : Move))), ?_, ?_, ?_⟩
  · simp [branchBit]
  · show (s, true) = ((s, j, tp).1, readSym (s, j, tp))
    simp only [readSym, h]
  · simp [applyTrans, moveHead]

/-- **`branchBit` on `false` (PROVED).**  At `(s, j, tp)` reading `false`, it steps to `(sFalse, j, writeAt tp j false)`
— state branches to `sFalse`, head unchanged. -/
theorem branchBit_step_false (s sTrue sFalse j : ℕ) (tp : List Bool) (h : tp.getD j false = false) :
    concreteStep (branchBit s sTrue sFalse) (s, j, tp) (sFalse, j, writeAt tp j false) := by
  refine ⟨((s, false), (sFalse, false, (2 : Move))), ?_, ?_, ?_⟩
  · simp [branchBit]
  · show (s, false) = ((s, j, tp).1, readSym (s, j, tp))
    simp only [readSym, h]
  · simp [applyTrans, moveHead]

/-- **The one-step branch run on `true` (PROVED).**  Reading `true` at offset `h`, `branchBit` reaches `(sTrue, h, tp')`
in one step, preserving the tape and the head. -/
theorem branchBit_run_true (s sTrue sFalse h : ℕ) (tp : List Bool) (hb : tp.getD h false = true) :
    ∃ tp', reachIn (toNTM (branchBit s sTrue sFalse)) 1 (s, h, tp) (sTrue, h, tp') ∧
      ∀ q, tp'.getD q false = tp.getD q false := by
  refine ⟨writeAt tp h true, ⟨_, branchBit_step_true s sTrue sFalse h tp hb, rfl⟩, ?_⟩
  intro q
  have hwb : (writeAt tp h true).getD q false = (writeAt tp h (tp.getD h false)).getD q false := by rw [hb]
  rw [hwb, writeAt_getD_self]

/-- **The one-step branch run on `false` (PROVED).**  Reading `false` at offset `h`, `branchBit` reaches
`(sFalse, h, tp')` in one step, preserving the tape and the head. -/
theorem branchBit_run_false (s sTrue sFalse h : ℕ) (tp : List Bool) (hb : tp.getD h false = false) :
    ∃ tp', reachIn (toNTM (branchBit s sTrue sFalse)) 1 (s, h, tp) (sFalse, h, tp') ∧
      ∀ q, tp'.getD q false = tp.getD q false := by
  refine ⟨writeAt tp h false, ⟨_, branchBit_step_false s sTrue sFalse h tp hb, rfl⟩, ?_⟩
  intro q
  have hwb : (writeAt tp h false).getD q false = (writeAt tp h (tp.getD h false)).getD q false := by rw [hb]
  rw [hwb, writeAt_getD_self]

/-!
**The branch atom, proved.**  `branchBit` is the first non-advancing machine — it inspects a cell and routes the
control state accordingly, leaving tape and head untouched.  Next: assemble an equality test between encoded fields from
these branches, then the rule-table scan-and-match loop, then the apply — fragment by verified fragment, not faked.  Not
a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMBranch

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMBranch.branchBit_step_true
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMBranch.branchBit_run_true
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMBranch.branchBit_run_false
