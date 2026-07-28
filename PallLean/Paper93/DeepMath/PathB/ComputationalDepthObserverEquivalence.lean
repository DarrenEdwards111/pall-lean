import PallLean.Paper93.DeepMath.PathB.ComputationalDepthInterfaceGap

/-!
# Capstone: P vs NP is exactly the question of whether the two observers see the same class

The observer thread's clean statement.  There are two observers:

* the **P-observer** — *verify*: it decides a language by checking, in polynomial time;
* the **NP-observer** — *find*: it decides a language by guessing/seeing a witness, verified in polynomial time.

The P-observer's power is contained in the NP-observer's (verifying is a special case of finding-then-verifying,
ignoring the witness): `p_subset_np`.  This file states, and machine-checks, that **P vs NP is precisely the
question of whether these two observers see the same class** — nothing more, nothing less.

**This is a restatement, not a proof.**  `observer_equivalence` proves `P = NP ↔ the observers see the same
class` — a faithful translation of the problem into observer language, true by the definitions.  It gives the
*question* with total precision; it does not give the *answer*.  Which way the equivalence resolves — whether
the find-observer's class collapses to the verify-observer's, or is strictly larger — is the open theorem, and
it is genuinely open: `InterfaceGap` shows the two observers *can* collapse (NFA = DFA) and *can* separate, so
the framing decides neither.

## What is proved

* **`Observers`** — the two observers (`verifyDecides`, `findDecides`) with `P ⊆ NP` (`p_subset_np`).
* **`SeeTheSame`** — the observers decide the same class: `∀ L, verify L ↔ find L`.
* **`PeqNP`** — `P = NP`: the find-observer's class collapses into the verify-observer's.
* **`observer_equivalence`** — the capstone: `P = NP ↔ the observers see the same class`.
* **`p_vs_np_is_the_observer_question`** — restated: resolving P vs NP is resolving whether the two observers
  see the same thing.

## Honest verdict — the mountain, named exactly

This is the cleanest true statement of P vs NP in observer language, and it is a *restatement*: `P = NP` is,
by the definitions, the assertion that the verify-observer and the find-observer see the same class
(`observer_equivalence`).  It crystallizes the correct framing — P vs NP asks "can the two observers see the
same thing?" — and it is machine-checked.  But naming the question is not answering it: whether the observers
collapse (`P = NP`) or the find-observer sees strictly more (`P ≠ NP`) is exactly the open theorem, consistent
both ways (`InterfaceGap`).  So the capstone names the mountain perfectly; climbing it is new mathematics.
Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ObserverEquivalence

/-- The two observers of P vs NP: the P-observer decides by *verifying*, the NP-observer by *finding*; the
P-observer's power sits inside the NP-observer's. -/
structure Observers where
  /-- the type of languages -/
  Lang : Type
  /-- the P-observer decides `L` (polynomial-time verify) -/
  verifyDecides : Lang → Prop
  /-- the NP-observer decides `L` (polynomial-time find/guess-and-verify) -/
  findDecides : Lang → Prop
  /-- `P ⊆ NP`: verifying is finding that ignores the witness -/
  p_subset_np : ∀ L, verifyDecides L → findDecides L

namespace Observers

variable (O : Observers)

/-- **The observers see the same class.**  The verify-observer and the find-observer decide exactly the same
languages. -/
def SeeTheSame : Prop := ∀ L, O.verifyDecides L ↔ O.findDecides L

/-- **`P = NP`.**  The find-observer's class collapses into the verify-observer's. -/
def PeqNP : Prop := ∀ L, O.findDecides L → O.verifyDecides L

/-- **The observer-equivalence capstone (proved).**  `P = NP` *is* the statement that the two observers see
the same class: `PeqNP ↔ SeeTheSame`.  A faithful restatement of P vs NP in observer language — true by the
definitions and `P ⊆ NP`. -/
theorem observer_equivalence : O.PeqNP ↔ O.SeeTheSame := by
  constructor
  · intro h L
    exact ⟨O.p_subset_np L, h L⟩
  · intro h L hfind
    exact (h L).mpr hfind

/-- **P vs NP is the observer question (proved).**  Resolving whether `P = NP` is exactly resolving whether the
two observers see the same class. -/
theorem p_vs_np_is_the_observer_question : (O.PeqNP ↔ O.SeeTheSame) ∧ (¬ O.PeqNP ↔ ¬ O.SeeTheSame) :=
  ⟨observer_equivalence O, not_congr (observer_equivalence O)⟩

end Observers

end PallLean.Paper93.DeepMath.PathB.ObserverEquivalence

#print axioms PallLean.Paper93.DeepMath.PathB.ObserverEquivalence.Observers.observer_equivalence
#print axioms PallLean.Paper93.DeepMath.PathB.ObserverEquivalence.Observers.p_vs_np_is_the_observer_question
