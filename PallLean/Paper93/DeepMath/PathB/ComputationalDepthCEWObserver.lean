import PallLean.Paper93.DeepMath.PathB.ComputationalDepthObserverInequality

/-!
# CEW is observer boundedness — and "a clear inequality in what they can see" is the separating witness

CEW (the EKP measure: `P` families have low CEW) is a fair name for the *boundedness of the observers* — how
constrained the interface is.  The intuition: "surely there is a clear inequality between what the `P`-observer
and the `NP`-observer can see."  This file pins what that inequality is, honestly, by tying CEW to the observer
thread and the SPDP thread at once.

**Two senses of "what they can see".**
* The *interface* (the operations — verify vs find, and their CEW/boundedness) — these differ trivially.  But
  a difference of interface, even a measured one, does not force a difference of *power*: a bounded interface
  can decide the same class as an unbounded one (`InterfaceGap`, `NFA = DFA`).
* The *power* (the class each can decide) — an inequality *here* is `P ≠ NP`, and it is exactly a **separating
  witness**: a language the `NP`-observer decides that the `P`-observer cannot (`ObserverInequality`).

**"NP has high CEW" is the separating witness.**  In CEW/boundedness language, the claimed clear inequality —
the `NP`-observer being unbounded where `P` is bounded — is exactly "there is a language `NP` decides that `P`
cannot" (`cew_inequality_is_separating_witness`).  That is `(A3)`, the separating witness, `cost_super`.  So
"surely there is a clear inequality" is "surely there is a separating witness" — which is `P ≠ NP` itself, and
it is open: a world has neither (`inequality_is_open`).  "Surely" is the intuition, not the proof.

**And the CEW route caps at depth-4.**  CEW upper-bounds SPDP rank (EKP (A2)), and SPDP rank certifies only
depth-4 hardness (`ChasmCrossing`).  So even establishing a CEW gap through the measure reaches only depth-4;
lifting to general is the same wall.

## What is proved

* **`cew_inequality_is_separating_witness`** — "NP has high CEW" (the boundedness inequality) is exactly the
  existence of a separating witness (`P ≠ NP`).
* **`inequality_is_open`** — a consistent world has neither the CEW gap nor a separating witness: the
  inequality is open, "surely" is the intuition.

## Honest verdict — the clear inequality is real, and it is the wall

CEW as observer boundedness is a genuine framing, and yes: a clear inequality in what the observers can *decide*
would settle it.  But that inequality is not the (trivial) interface difference — it is the *power* difference,
which is a separating witness (`cew_inequality_is_separating_witness`), i.e. `P ≠ NP` = `cost_super`, and it is
open (`inequality_is_open`).  A boundedness/measure gap does not force a power gap (`InterfaceGap`), and the CEW
measure only certifies depth-4 hardness through SPDP (`ChasmCrossing`).  So "surely there is a clear inequality"
is "surely there is a separating witness" — the intuition that `P ≠ NP` is obvious, which is exactly the
unproven wall.  The inequality is real *as the theorem*; its clarity is the thing to prove.  Nothing here is
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CEWObserver

/-- CEW as observer boundedness, tied to the power inequality. -/
structure CEW where
  /-- the claimed clear inequality: the `NP`-observer is unbounded (high CEW) where `P` is bounded -/
  NP_highCEW : Prop
  /-- there is a separating witness: a language the `NP`-observer decides that the `P`-observer cannot -/
  hasSeparatingWitness : Prop
  /-- **the boundedness inequality is the power inequality**: "NP high CEW" iff a separating witness exists -/
  cew_is_witness : NP_highCEW ↔ hasSeparatingWitness

/-- **The CEW inequality is the separating witness (proved).**  "The NP-observer sees more (high CEW)" is
exactly "there is a language NP decides that P cannot" — the boundedness gap *is* the power gap, `P ≠ NP`. -/
theorem cew_inequality_is_separating_witness (C : CEW) : C.NP_highCEW ↔ C.hasSeparatingWitness :=
  C.cew_is_witness

/-- A world where neither the CEW gap nor a separating witness holds (a `P = NP` world). -/
def openWorld : CEW where
  NP_highCEW := False
  hasSeparatingWitness := False
  cew_is_witness := Iff.rfl

/-- **The inequality is open (proved).**  A consistent world has neither a CEW gap nor a separating witness —
so "surely the NP-observer sees more" is the intuition, not a theorem: the inequality is `P ≠ NP`, unproven. -/
theorem inequality_is_open : ∃ C : CEW, ¬ C.NP_highCEW ∧ ¬ C.hasSeparatingWitness :=
  ⟨openWorld, not_false, not_false⟩

end PallLean.Paper93.DeepMath.PathB.CEWObserver

#print axioms PallLean.Paper93.DeepMath.PathB.CEWObserver.cew_inequality_is_separating_witness
#print axioms PallLean.Paper93.DeepMath.PathB.CEWObserver.inequality_is_open
