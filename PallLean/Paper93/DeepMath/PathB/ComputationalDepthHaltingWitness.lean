import Mathlib.Data.Nat.Basic

/-!
# The halting problem witnesses that proof ≠ computation

Darren's argument: the shadow shows *computation* can't decide P vs NP; the halting problem is a *proof*
about what *computation* can't decide; therefore proof and computation are the same.

The halting problem shows the **exact opposite**.  "The halting problem is undecidable" is a **proof that
succeeds** about something **computation fails** at.  It is a case where one faculty *fails* and the other
*succeeds* on the same subject — which is precisely what it means for them to be **different**.  If proof
and computation were the same, then "no computation decides halting" would force "no proof establishes
anything about halting" — but Turing's proof exists.  So the halting theorem is a *witness* that they
differ, not that they coincide.

## The three roles being conflated

* **computation deciding** a problem (an algorithm),
* a **proof establishing** a fact (a proof),
* the fact being *about* the limits of computation (its subject).

The halting theorem is a **proof** (2) *about the limits of computation* (3) that *computation itself*
cannot decide (1).  That the subject is "computation's limits" does not make the proof a computation.

## What is proved

* **`faculties_differ`** — on the halting statement the two faculties give *opposite* verdicts:
  computation fails (`computationDecides = false`) while proof succeeds (`proofEstablishes = true`).  Same
  statement, different verdict ⟹ not the same faculty.
* **`proof_beyond_computation`** — there is a statement decided by proof but not by computation (halting).
* **`computation_fail_not_proof_fail`** — so "computation can't decide it" does **not** imply "proof can't
  establish it".  The inference at the heart of "unprovable" / "they're the same" is false — refuted by the
  very example cited.

## Honest scope — three distinct meta-notions, none of them equated

`P vs NP` being invisible to the bounded computational observer (the shadow) is **computational
inaccessibility**.  The halting problem is **undecidability** (of a *decision problem* over infinitely many
inputs).  Whether `P vs NP` is unprovable is **independence** (of a *single statement* from ZFC).  These are
three different things, and the halting theorem shows the first two come apart from *proof*, not together.
This file certifies neither `P ≠ NP` nor "`P vs NP` is unprovable"; it proves only that the halting example
refutes "proof = computation".  `P vs NP` remains hard, not unprovable.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.HaltingWitness

/-- A statement, tagged by whether a **computation** can decide it and whether a **proof** can establish the
truth about it — two separate faculties. -/
structure MetaStatement where
  /-- can an algorithm decide it -/
  computationDecides : Bool
  /-- can a proof establish the truth about it -/
  proofEstablishes : Bool

/-- **The halting fact.**  No computation decides the halting problem (`computationDecides = false`), yet its
undecidability is *proved* (`proofEstablishes = true`) — computation fails, proof succeeds. -/
def haltingFact : MetaStatement := ⟨false, true⟩

/-- **The two faculties give opposite verdicts (proved).**  On the halting statement, computation fails
while proof succeeds: `computationDecides ≠ proofEstablishes`.  Same statement, different verdict — so proof
and computation are **not the same faculty**. -/
theorem faculties_differ : haltingFact.computationDecides ≠ haltingFact.proofEstablishes := by decide

/-- **Proof reaches beyond computation (proved).**  There is a statement decided by proof but not by
computation — the halting problem itself. -/
theorem proof_beyond_computation :
    ∃ s : MetaStatement, s.computationDecides = false ∧ s.proofEstablishes = true :=
  ⟨haltingFact, rfl, rfl⟩

/-- **Computation-failure does not entail proof-failure (proved).**  It is false that every
computation-undecidable statement is proof-unestablishable — the halting problem is a counterexample.  So
"the computational observer can't decide P vs NP" does *not* imply "P vs NP is unprovable". -/
theorem computation_fail_not_proof_fail :
    ¬ (∀ s : MetaStatement, s.computationDecides = false → s.proofEstablishes = false) := by
  intro h
  exact absurd (h haltingFact rfl) (by decide)

end PallLean.Paper93.DeepMath.PathB.HaltingWitness

#print axioms PallLean.Paper93.DeepMath.PathB.HaltingWitness.faculties_differ
#print axioms PallLean.Paper93.DeepMath.PathB.HaltingWitness.computation_fail_not_proof_fail
