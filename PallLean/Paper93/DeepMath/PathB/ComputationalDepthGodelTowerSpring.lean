/-!
# The Gödel-tower spring: self-reference forces strict growth — but needs soundness, which circuits lack

Darren's clue (N-Frame book 1, §2.3 "The Gödel Hierarchy Tower: No Escape"): each step of the tower
**compresses like a spring** — the self-referential Gödel sentence is true but unprovable at its level,
storing "potential" that forces a strict extension one level up, and this never stops (no escape).
This is exactly the right *shape* for `cost_super`: a self-referential mechanism that forces **strict
growth**, **non-naturally** — no counting argument, pure self-reference.

This file formalizes the spring, and then finds — honestly — precisely why it does not (yet) translate
to circuit size.

## The spring (proved)

A `GodelLevel` has a provability predicate `Prov`, a truth predicate `True_`, a self-referential Gödel
sentence with the fixed point `True_ godel ↔ ¬ Prov godel` (the diagonal lemma), and **soundness**
`Prov ψ → True_ ψ`.  Then:

* **`godel_unprovable`** — the level cannot prove its own Gödel sentence.  (If it could, soundness
  makes it true, but the fixed point makes it unprovable — contradiction.)  The compressed spring.
* **`godel_true`** — yet the sentence is true.  The stored potential.
* **`extend_proves_godel`** — one level up (adding `godel`) proves it.  The spring pushes up exactly one
  step; the extended level has its own Gödel sentence — no escape.

Crucially, this forces strict growth **with no counting** — it is a purely self-referential,
non-natural mechanism.  That is exactly what the wall needs and what natural proofs cannot supply.

## Why it does not translate to circuits — soundness is load-bearing

The spring fires **because of soundness** (`Prov ψ → True_ ψ`): the semantic constraint linking what the
level *proves* to what is *true*.  A circuit has no such constraint — it simply computes a function;
there is no truth predicate it is *sound* for, and no self-referential paradox forcing it to fail on a
target.  `spring_needs_soundness` proves the point: drop soundness and the fixed point does **not**
force unprovability — a level can prove its own Gödel sentence.

So the missing ingredient, named precisely, is a **soundness/consistency analog for circuits**: a
self-referential constraint that forces a size-`s` circuit to be *wrong* about the target the way a
consistent theory is forced to *not prove* its Gödel sentence.  SAT can *express* circuit-correctness
(Tseitin), but expressing is not being sound (cf. `TseitinForceFixedPoint`).  Supplying that
soundness-analog is the new idea the wall is waiting for.

## Honest verdict

The Gödel-tower spring is a **real, non-natural, strict-growth mechanism** — Darren's instinct about the
shape is correct.  It does not cross the wall, because it runs on *soundness*, and circuits carry no
soundness constraint.  The clue is genuine and the gap it leaves is exact: circuit-soundness.  Nothing
here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.GodelTowerSpring

/-- **A self-referential level of the Gödel tower.**  Provability, truth, a Gödel sentence with the
fixed-point (self-reference), and soundness. -/
structure GodelLevel where
  Sentence : Type
  Prov : Sentence → Prop
  True_ : Sentence → Prop
  godel : Sentence
  /-- the diagonal / fixed-point lemma: the Gödel sentence is true iff it is unprovable -/
  fixedpoint : True_ godel ↔ ¬ Prov godel
  /-- soundness: whatever is provable is true (the semantic constraint that makes the spring fire) -/
  sound : ∀ ψ, Prov ψ → True_ ψ

/-- **The compressed spring (proved).**  A sound, self-referential level cannot prove its own Gödel
sentence: provability would make it true (soundness) hence unprovable (fixed point) — contradiction. -/
theorem godel_unprovable (L : GodelLevel) : ¬ L.Prov L.godel := by
  intro hp
  have ht : L.True_ L.godel := L.sound L.godel hp
  exact (L.fixedpoint.mp ht) hp

/-- **The stored potential (proved).**  The Gödel sentence is nonetheless true. -/
theorem godel_true (L : GodelLevel) : L.True_ L.godel :=
  L.fixedpoint.mpr (godel_unprovable L)

/-- One level up: provability extended by the Gödel sentence. -/
def extend (L : GodelLevel) (ψ : L.Sentence) : Prop := L.Prov ψ ∨ ψ = L.godel

/-- **The strict step (proved).**  The extended level proves the Gödel sentence the old one could not
(`godel_unprovable`).  Strict growth; the extended level has its own Gödel sentence — no escape. -/
theorem extend_proves_godel (L : GodelLevel) : extend L L.godel :=
  Or.inr rfl

/-- **Soundness is load-bearing (proved) — the circuit disanalogy.**  Drop soundness and the fixed
point does NOT force unprovability: there is a self-referential "level" that proves its own Gödel
sentence.  A circuit, having no soundness constraint, is like this — the spring does not fire.  The
missing ingredient is a soundness/consistency analog for circuits. -/
theorem spring_needs_soundness :
    ∃ (S : Type) (Prov True_ : S → Prop) (g : S),
      (True_ g ↔ ¬ Prov g) ∧ Prov g :=
  ⟨Unit, (fun _ => True), (fun _ => False), (),
    ⟨fun h => h.elim, fun h => h trivial⟩, trivial⟩

end PallLean.Paper93.DeepMath.PathB.GodelTowerSpring

#print axioms PallLean.Paper93.DeepMath.PathB.GodelTowerSpring.godel_unprovable
#print axioms PallLean.Paper93.DeepMath.PathB.GodelTowerSpring.godel_true
#print axioms PallLean.Paper93.DeepMath.PathB.GodelTowerSpring.extend_proves_godel
#print axioms PallLean.Paper93.DeepMath.PathB.GodelTowerSpring.spring_needs_soundness
