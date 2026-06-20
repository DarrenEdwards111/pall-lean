import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3ScanTable

/-!
# Entry 399 — universal-TM-table build: the fixed-symbol bit test `testBit3` (proved)

The scanner layer (entries 395–398) traverses the `Sym3`-encoded rule table list-preservingly.  The rule-loop must
additionally **match**: compare the configuration's key against each rule's key.  That comparison is *data against data*
— both operands are on the tape and unknown at table-build time — which is exactly the wall the 2-symbol Bool route hit.

The marker route's answer: `markCarry3` (entry 389) reads one config-key bit **into the control-state lineage** (`sO`
vs `sI`), lays the marker `M` as a returnable anchor, and the machine then shuttles to the rule-key location.  There the
comparison is no longer data-vs-data: the carried bit is fixed *by the state lineage*, so the cell need only be tested
against a **constant** symbol `w` known to that lineage.  This brick is that atom: a one-step test routing to `sEq` if
the head cell equals `w`, else `sNe`, leaving the tape identical.

## What is proved (clean axioms, no `sorry`)

* **`testBit3 s sEq sNe w`** — on each symbol, write it back, *stay*, and go to `sEq` if it equals `w`, else `sNe`.
* **`testBit3_run`** (PROVED) — `j < tp.length ⇒ reachIn (toNTM3 (testBit3 s sEq sNe w)) 1 (s, j, tp)
  ((if readSym3 (s,j,tp) = w then sEq else sNe), j, tp)`: one step, head fixed, tape identical, control routed on the
  equality of the head cell with the constant `w`.

## Honest scope

This is the **match atom** — a single-cell test against a constant, the comparison the carried-state lineage performs at
the distant operand.  It does **not** yet shuttle, nor compare a whole key, nor loop the match over the table, nor apply.
Building those fragment by fragment is the genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰`
or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3TestBit

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (Move moveHead)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym
  (Sym3 TMachine3 concreteStep3 readSym3 writeAt3 applyTrans3 toNTM3 writeAt3_id_of_lt)

/-- **The fixed-symbol bit test.**  On each symbol, write it back, *stay*, and route to `sEq` if it equals the constant
`w`, else `sNe`. -/
def testBit3 (s sEq sNe : ℕ) (w : Sym3) : TMachine3 :=
  [((s, Sym3.O), ((if Sym3.O = w then sEq else sNe), Sym3.O, (2 : Move))),
   ((s, Sym3.I), ((if Sym3.I = w then sEq else sNe), Sym3.I, (2 : Move))),
   ((s, Sym3.M), ((if Sym3.M = w then sEq else sNe), Sym3.M, (2 : Move)))]

/-- **The fixed-symbol bit test run (PROVED).**  One step, head fixed, tape identical, control routed on `head = w`. -/
theorem testBit3_run (s sEq sNe j : ℕ) (tp : List Sym3) (w : Sym3) (hbound : j < tp.length) :
    reachIn (toNTM3 (testBit3 s sEq sNe w)) 1 (s, j, tp)
      ((if readSym3 (s, j, tp) = w then sEq else sNe), j, tp) := by
  have hid : ∀ a : Sym3, readSym3 (s, j, tp) = a → writeAt3 tp j a = tp := by
    intro a ha; rw [← ha]; exact writeAt3_id_of_lt tp j hbound
  rcases h : readSym3 (s, j, tp) with _ | _ | _
  · refine ⟨((if Sym3.O = w then sEq else sNe), j, writeAt3 tp j Sym3.O), ?_, ?_⟩
    · exact ⟨((s, Sym3.O), ((if Sym3.O = w then sEq else sNe), Sym3.O, (2 : Move))), by simp [testBit3],
        by simp [h], by simp [applyTrans3, moveHead]⟩
    · show _ = _; rw [hid Sym3.O h]
  · refine ⟨((if Sym3.I = w then sEq else sNe), j, writeAt3 tp j Sym3.I), ?_, ?_⟩
    · exact ⟨((s, Sym3.I), ((if Sym3.I = w then sEq else sNe), Sym3.I, (2 : Move))), by simp [testBit3],
        by simp [h], by simp [applyTrans3, moveHead]⟩
    · show _ = _; rw [hid Sym3.I h]
  · refine ⟨((if Sym3.M = w then sEq else sNe), j, writeAt3 tp j Sym3.M), ?_, ?_⟩
    · exact ⟨((s, Sym3.M), ((if Sym3.M = w then sEq else sNe), Sym3.M, (2 : Move))), by simp [testBit3],
        by simp [h], by simp [applyTrans3, moveHead]⟩
    · show _ = _; rw [hid Sym3.M h]

/-!
**The match atom, proved.**  `testBit3` routes the control state on whether the head cell equals a constant symbol — the
test the carried-state lineage performs at the distant operand, leaving the tape identical.  Next: shuttle the head to
the rule-key location (`seekMarkRight`/`moveRight3`) and chain `markCarry3 → shuttle → testBit3 → restore` into a
distance-independent single-bit compare — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3TestBit

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3TestBit.testBit3_run
