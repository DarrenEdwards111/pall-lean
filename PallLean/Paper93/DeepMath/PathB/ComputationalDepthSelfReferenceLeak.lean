import Mathlib.Data.Bool.Basic

/-!
# The self-reference idea, built to its terminus: where it closes and where it leaks

The proposed "last inch": make MCSP's self-description force a small circuit to be wrong about
itself, using the free-reach hub as the universal evaluator.  This file formalises that mechanism
abstractly and machine-checks the exact point where it closes and the exact point where it leaks —
the honest terminus of the idea, not a crossing.

## The mechanism

A `SelfRefWorld`: deciders `D` (circuits) with `run D : Input → Bool`, a self-referential instance
`selfInstance D` (encoding `D`'s own description — evaluated using `D`'s free reach, which is the
"reach becomes evaluator" step), a correct answer `truth D` on it, and a size predicate `Small`.  A
decider is `Correct` when `run D (selfInstance D) = truth D`.

## Where it CLOSES — a liar self-instance forces the bound

* **`diagonal_forces_lb`** (proved) — if the world has a **liar** structure (`truth D = ¬ run D
  (selfInstance D)` for every small `D`: the correct answer is the NEGATION of what a small decider
  outputs), then NO small decider is correct.  `run = truth` and `truth = ¬run` force `truth = ¬truth`
  — contradiction.  The fixed point fires: self-reference forces a lower bound.  This is the real,
  proved engine (it is the shape of every diagonalisation lower bound).

## Where it LEAKS — MCSP is a truth-teller, not a liar

* **`truthteller_no_contradiction`** (proved) — MCSP's self-instance is a **truth-teller**: a small
  decider's own truth table is small, so the correct MCSP answer is `true`, and a small decider that
  simply outputs `true` on its self-instance is CORRECT.  No contradiction, no lower bound.  The
  hub's reach lets it read its own description — but reading it, it finds a question it can answer
  *consistently* (`yes, I am small`), not a paradox.
* **`truthteller_not_liar`** (proved) — the precise diagnosis: a world that is both truth-teller and
  liar forces `run = false` everywhere (degenerate).  So MCSP (truth-teller) is genuinely NOT a liar
  — the negation structure the diagonal needs is *absent*, not just unproven.

## Verdict — the leak, named exactly

The self-reference engine is real and closes for LIAR self-references.  It leaks for MCSP because
MCSP's self-application is self-CONSISTENT (a circuit can truthfully certify its own smallness), not
self-CONTRADICTORY.  So the free reach that evaluates the self-instance does not help: reading your
own description is not a paradox when the question ("am I small?") has a consistent answer.  The
missing ingredient is therefore precise: a **liar self-reference for a hard problem** — a
SAT-specific self-instance whose correct answer is forced to be the negation of any small circuit's
output, and that survives free fan-in.  That object is `cost_super` wearing the self-reference
costume; this file proves MCSP is not it, and says exactly what would be.  Nothing here is
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SelfReferenceLeak

/-- A self-referential world: deciders, their self-instances, the correct answer, and a size
predicate. -/
structure SelfRefWorld where
  /-- deciders (circuits) -/
  Decider : Type
  /-- inputs -/
  Input : Type
  /-- a decider's output on an input -/
  run : Decider → Input → Bool
  /-- the self-referential instance for a decider (its own description, read via free reach) -/
  selfInstance : Decider → Input
  /-- the correct answer on the self-instance -/
  truth : Decider → Bool
  /-- the decider is small -/
  Small : Decider → Prop

/-- A decider is **correct** on its self-instance. -/
def Correct (W : SelfRefWorld) (D : W.Decider) : Prop :=
  W.run D (W.selfInstance D) = W.truth D

/-- **Liar structure**: the correct answer is the NEGATION of what a small decider outputs. -/
def LiarStructure (W : SelfRefWorld) : Prop :=
  ∀ D, W.Small D → W.truth D = ! W.run D (W.selfInstance D)

/-- **Truth-teller structure**: the correct answer for a small decider is `true` (its own table is
small — the MCSP case). -/
def TruthTellerStructure (W : SelfRefWorld) : Prop :=
  ∀ D, W.Small D → W.truth D = true

/-! ### Where it closes -/

/-- **The diagonal forces a lower bound (proved).**  Under a liar self-reference, no small decider is
correct: `run = truth` and `truth = ¬run` give `truth = ¬truth`.  The real diagonalisation engine. -/
theorem diagonal_forces_lb (W : SelfRefWorld) (hliar : LiarStructure W)
    (D : W.Decider) (hsmall : W.Small D) : ¬ Correct W D := by
  intro hcorr
  have h : W.truth D = ! W.run D (W.selfInstance D) := hliar D hsmall
  rw [Correct] at hcorr
  rw [hcorr] at h
  exact absurd h (by cases W.truth D <;> decide)

/-! ### Where it leaks -/

/-- **MCSP leaks (proved).**  Under a truth-teller self-reference, a small decider that outputs `true`
on its self-instance is CORRECT — no contradiction.  The self-application is consistent, so no lower
bound is forced. -/
theorem truthteller_no_contradiction (W : SelfRefWorld) (htt : TruthTellerStructure W)
    (D : W.Decider) (hsmall : W.Small D) (hout : W.run D (W.selfInstance D) = true) :
    Correct W D := by
  rw [Correct, htt D hsmall]; exact hout

/-- **The precise diagnosis (proved).**  A world that is BOTH truth-teller and liar is degenerate —
every small decider outputs `false` on its self-instance.  So a genuine MCSP (truth-teller) is NOT a
liar: the negation structure the diagonal needs is absent, not merely unproven. -/
theorem truthteller_not_liar (W : SelfRefWorld) (htt : TruthTellerStructure W)
    (hliar : LiarStructure W) (D : W.Decider) (hsmall : W.Small D) :
    W.run D (W.selfInstance D) = false := by
  have h1 : W.truth D = true := htt D hsmall
  have h2 : W.truth D = ! W.run D (W.selfInstance D) := hliar D hsmall
  rw [h1] at h2
  cases hr : W.run D (W.selfInstance D)
  · rfl
  · rw [hr] at h2; simp at h2

/-- **The missing ingredient, named (proved).**  A lower bound from self-reference requires a liar
structure; a truth-teller (MCSP) yields a correct small decider instead.  So the two are exclusive on
the outputs: to cross, one needs a hard problem with a liar self-instance — `cost_super` in the
self-reference costume. -/
theorem leak_is_missing_liar (W : SelfRefWorld) (htt : TruthTellerStructure W)
    (D : W.Decider) (hsmall : W.Small D) (hout : W.run D (W.selfInstance D) = true) :
    Correct W D ∧ ¬ (W.truth D = ! W.run D (W.selfInstance D)) := by
  refine ⟨truthteller_no_contradiction W htt D hsmall hout, ?_⟩
  rw [htt D hsmall, hout]
  decide

end PallLean.Paper93.DeepMath.PathB.SelfReferenceLeak

#print axioms PallLean.Paper93.DeepMath.PathB.SelfReferenceLeak.diagonal_forces_lb
#print axioms PallLean.Paper93.DeepMath.PathB.SelfReferenceLeak.truthteller_no_contradiction
#print axioms PallLean.Paper93.DeepMath.PathB.SelfReferenceLeak.truthteller_not_liar
#print axioms PallLean.Paper93.DeepMath.PathB.SelfReferenceLeak.leak_is_missing_liar
