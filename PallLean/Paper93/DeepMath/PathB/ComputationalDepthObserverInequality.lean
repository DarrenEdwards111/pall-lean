import PallLean.Paper93.DeepMath.PathB.ComputationalDepthObserverEquivalence

/-!
# The wall is proving the interfaces unequal — and that means exhibiting the separating witness

`ObserverEquivalence` proved `P = NP ↔ the two observers see the same class`, so `P ≠ NP` is exactly *the
interfaces (their boundaries — the classes they decide) are unequal*.  This file unfolds what proving that
inequality concretely requires, and it lands on the session's one open object.

**Interfaces unequal = a separating witness (proved).**  Because the P-observer's class sits inside the
NP-observer's (`p_subset_np`), the only way the two boundaries can differ is a language the *find*-observer
decides but the *verify*-observer cannot.  So "the interfaces are unequal" is equivalent to "there exists a
separating witness — a language in `NP \ P`" (`interfaces_unequal_iff_separating_witness`).  Proving the
boundaries unequal is not an abstract "≠"; it is *producing a specific language* the find-observer sees and the
verify-observer provably cannot.

**That witness is the one open object.**  The separating witness, made explicit, is SAT (explicit, in NP);
"the verify-observer cannot decide it" is `SAT ∉ P` — a circuit lower bound, the incompressible object off Π★.
So `P ≠ NP ↔ ∃ separating witness` (`wall_is_separating_witness`) closes the loop between the observer thread
and the incompressibility thread: the interface inequality *is* the explicit hard object.

**Why "simply" is a restatement, not a simplification.**  Proving two classes *equal* is done by exhibiting a
simulation (as NFA → DFA by subset construction).  Proving them *unequal* requires a separating witness — and
an *explicit* witness of `NP \ P` is a circuit lower bound.  The inequality direction is the hard one; renaming
the wall "prove the interfaces unequal" states it exactly and lowers it not at all.

## What is proved

* **`interfaces_unequal_iff_separating_witness`** — `¬ SeeTheSame ↔ ∃ L, find L ∧ ¬ verify L`: the interfaces
  are unequal iff a separating witness (a language in `NP \ P`) exists.
* **`wall_is_separating_witness`** — `P ≠ NP ↔ ∃ separating witness`: proving the interfaces unequal *is*
  exhibiting the witness — the explicit hard object.

## Honest verdict — the wall named as an inequality, unfolded to the one object

Yes: the wall is proving the two perceptual interfaces' boundaries unequal — `P ≠ NP` is exactly `¬ SeeTheSame`.
And unfolded, that inequality *is* the existence of a separating witness (`interfaces_unequal_iff_separating_witness`,
`wall_is_separating_witness`): a specific language the find-observer decides that the verify-observer cannot —
which, made explicit, is `SAT ∉ P`, the incompressible object off Π★.  So "prove the interfaces unequal" is not
a lighter task than "prove `P ≠ NP`"; it is the same task, and it concretely demands producing the one open
object the whole session reduced to.  The observer inequality names the wall precisely and hands you back,
exactly, the explicit hard witness — which is the thing new mathematics must produce.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ObserverInequality

open PallLean.Paper93.DeepMath.PathB.ObserverEquivalence
open PallLean.Paper93.DeepMath.PathB.ObserverEquivalence.Observers

/-- **The interfaces are unequal iff a separating witness exists (proved).**  Since verifying implies finding
(`p_subset_np`), the boundaries differ exactly when some language is decided by the find-observer but not the
verify-observer — a witness in `NP \ P`. -/
theorem interfaces_unequal_iff_separating_witness (O : Observers) :
    ¬ O.SeeTheSame ↔ ∃ L, O.findDecides L ∧ ¬ O.verifyDecides L := by
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    exact h (fun L => ⟨O.p_subset_np L, hc L⟩)
  · rintro ⟨L, hfind, hnv⟩ hsame
    exact hnv ((hsame L).mpr hfind)

/-- **The wall is exhibiting the separating witness (proved).**  `P ≠ NP` is equivalent to the existence of a
separating witness — a language the find-observer decides that the verify-observer cannot.  Made explicit, that
witness is `SAT ∉ P`: the incompressible object off Π★, the session's one open object. -/
theorem wall_is_separating_witness (O : Observers) :
    ¬ O.PeqNP ↔ ∃ L, O.findDecides L ∧ ¬ O.verifyDecides L :=
  Iff.trans (not_congr (observer_equivalence O)) (interfaces_unequal_iff_separating_witness O)

end PallLean.Paper93.DeepMath.PathB.ObserverInequality

#print axioms PallLean.Paper93.DeepMath.PathB.ObserverInequality.interfaces_unequal_iff_separating_witness
#print axioms PallLean.Paper93.DeepMath.PathB.ObserverInequality.wall_is_separating_witness
