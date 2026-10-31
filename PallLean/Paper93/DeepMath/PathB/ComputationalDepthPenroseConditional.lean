import Mathlib.Data.Nat.Basic

/-!
# "Seeing" a Gödel truth is a conditional proof, not hypercomputation

Darren, via Penrose/Lucas: the proof "relies on sharing" (computationally unachievable) unless P-class
observers have a *shadow of the hypercomputational* — as Penrose says we "see" the truth of a Gödel
sentence even where there is no proof.

This is a serious, famous argument — and it has a serious, standard answer (Feferman, Putnam, Davis): what
we actually "see" is a **conditional** — *if* the system `F` is consistent, *then* its Gödel sentence `G(F)`
is true — and that conditional `Con(F) → G(F)` is an **ordinary theorem**, provable, no hypercomputation.
The apparent "seeing truth without proof" is really: a provable conditional, applied to a consistency
*premise*.  Penrose's step needs `G(F)` *unconditionally*, which requires *knowing* `Con(F)` — and for a
system rich enough to capture human mathematics, we do **not** know that.  So no hypercomputation is
exhibited; the insight is a proof plus a premise.

## What is proved

* **`godel_insight_is_conditional`** — the insight is the conditional `Con → G` (Gödel: if consistent, the
  sentence is true) — a plain implication.
* **`seeing_is_ordinary_proof`** — "seeing `G` is true" is `conditional` applied to the consistency premise:
  `Con → G` with `Con` gives `G` by ordinary modus ponens.  No faculty beyond proof.
* **`seeing_requires_premise`** — the conditional *alone* does not yield `G`: there are `Con, G` with
  `(Con → G)` yet `¬G`.  So the "seeing" is not premise-free — it needs `Con`, which for rich `F` we lack.

## Honest scope — three points, and where it actually lands

1. **The "seeing" is conditional, not hypercomputational.**  `Con(F) → G(F)` is a theorem; the unconditional
   jump smuggles in `Con(F)`, a normal premise we do not have for rich `F`.  This is the standard refutation
   of Lucas–Penrose, and the argument is rejected by most logicians for exactly this reason.
2. **It is about Gödel sentences, not `P vs NP`.**  Even granting Penrose, it concerns *independent*
   statements.  `P vs NP` is a *concrete arithmetic* statement, not known independent, and unlikely to be —
   so the argument does not even apply to it.
3. **"The proof relies on sharing" is the quantify/instantiate confusion again.**  The proof reasons *about*
   whether circuits can share (`∀ C, …` — `cost_super`); it does not itself *perform* sharing.  Reasoning
   about sharing costs one `∀`; performing it is the (bounded) computation.  No hypercomputation, no
   "shadow" — a finite `∀` reaches the domain (`QuantifyNotInstantiate`).

Whether minds are hypercomputational is unsettled philosophy with no established evidence; the Gödel
argument does not establish it, and — decisively — none of it is *needed*: proving facts about unbounded
domains is what `∀` is for.  So `P vs NP` is **hard**, not gated behind a hypercomputational faculty.  This
file certifies neither `P ≠ NP` nor its unprovability.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.PenroseConditional

/-- A Gödel setup: a consistency statement `Con` for a system `F`, its Gödel sentence `G`, and the theorem
that *if* `F` is consistent *then* `G` is true.  The conditional is an ordinary provable implication. -/
structure GodelInsight where
  /-- `F` is consistent -/
  Con : Prop
  /-- the Gödel sentence of `F` -/
  G : Prop
  /-- Gödel's theorem: if `F` is consistent, its Gödel sentence is true -/
  conditional : Con → G

/-- **The insight is the conditional (proved).**  What we "see" is `Con → G` — a plain implication, an
ordinary theorem. -/
theorem godel_insight_is_conditional (I : GodelInsight) : I.Con → I.G := I.conditional

/-- **"Seeing `G`" is ordinary proof (proved).**  Given the consistency premise, `G` follows by modus ponens
on the provable conditional — no faculty beyond proof, no hypercomputation. -/
theorem seeing_is_ordinary_proof (I : GodelInsight) (hcon : I.Con) : I.G := I.conditional hcon

/-- **The conditional alone does not yield the truth (proved).**  There are `Con, G` with `(Con → G)` yet
`¬G` — so "seeing `G`" is not premise-free: it needs `Con`, which for a system rich enough to capture human
mathematics we do not know.  The unconditional Penrose step smuggles in that premise. -/
theorem seeing_requires_premise : ∃ (Con G : Prop), (Con → G) ∧ ¬ G :=
  ⟨False, False, fun h => h, fun h => h⟩

end PallLean.Paper93.DeepMath.PathB.PenroseConditional

#print axioms PallLean.Paper93.DeepMath.PathB.PenroseConditional.seeing_is_ordinary_proof
#print axioms PallLean.Paper93.DeepMath.PathB.PenroseConditional.seeing_requires_premise
