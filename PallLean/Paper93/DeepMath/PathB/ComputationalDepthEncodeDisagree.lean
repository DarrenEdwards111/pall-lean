import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSelfReferenceFeature

/-!
# Does SAT's self-encoding force disagreement over agreement? No — it is neutral; the wall is elsewhere

`SelfReferenceFeature` found the barrier-clearing vehicle (self-reference) and isolated the residual:
the encode ⟹ disagree step.  SAT is hard only if it encodes its solvers *and disagrees* with them at the
diagonal (is the diagonal), rather than being a fixed point that *agrees* with one.  This file asks what
forces disagreement — and the honest answer is that the self-encoding **does not**: it is symmetric
between agreement and disagreement.  What breaks the symmetry is a fact about the *solvers*, not the
encoding.

Write `sat : ℕ → Bool` for SAT (on encoded inputs) and `f : ℕ → ℕ → Bool` for the enumeration of solvers
(`f i` = the `i`-th solver).  SAT **disagrees** with solver `i` at the diagonal input `i` when
`sat i = !(f i i)`; solver `i` is **correct** there when `f i i = sat i`.

## What is proved

* **`disagree_iff_wrong`** — SAT disagrees with solver `i` **iff** that solver is *wrong* at `i`.
* **`disagrees_with_wrong_solver`** — SAT disagrees with every *incorrect* solver — for free.  Being
  correct, SAT differs from any solver that is wrong.
* **`agrees_with_correct_solver`** — SAT *agrees* with any *correct* solver: no disagreement there.
* **`full_disagreement_iff_all_wrong`** — SAT disagrees with *every* solver (is the diagonal, is hard)
  **iff** every solver is wrong — i.e. iff no correct solver exists.
* **`self_encoding_neutral`** — the self-encoding is symmetric: there are correct-at configurations and
  wrong-at configurations.  Nothing in "SAT encodes its solver" prefers disagreement.

## Honest verdict — the encoding is neutral; the wall is "no correct small solver"

The encode ⟹ disagree step is not forced by the self-encoding.  SAT disagrees with *wrong* solvers for
free (`disagrees_with_wrong_solver`) and *agrees* with *correct* ones (`agrees_with_correct_solver`); the
self-encoding is symmetric between the two (`self_encoding_neutral`).  What forces **full** disagreement —
SAT differing from *every* solver, i.e. SAT being the diagonal, i.e. SAT hard — is exactly that **every
solver is wrong** (`full_disagreement_iff_all_wrong`): no correct small solver exists.  That is `SAT ∉ P`
= `cost_super`.  So the symmetry is broken not by the self-encoding (the vehicle) but by the *absence of a
correct small solver* — precisely the soundness gap of the Gödel spring (`GodelSpringBridge`,
`GodelTowerSpring`): disagreement with *unsound* solvers is free, and the wall is that there is no *sound*
(correct) small solver.  Self-reference carries the argument to this exact point; the step that no small
solver is correct is the lower bound itself.  Right vehicle, and the remaining implication is `P ≠ NP`.
Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.EncodeDisagree

/-- SAT **disagrees** with solver `i` at the diagonal input `i`: `sat i = !(f i i)`.  `abbrev` so its
decidability is visible. -/
abbrev DisagreesAt (sat : ℕ → Bool) (f : ℕ → ℕ → Bool) (i : ℕ) : Prop := sat i = !(f i i)

/-- Solver `i` is **correct** at the diagonal input `i`: `f i i = sat i`. -/
abbrev CorrectAt (sat : ℕ → Bool) (f : ℕ → ℕ → Bool) (i : ℕ) : Prop := f i i = sat i

/-! ### Disagreement is exactly wrongness -/

/-- **SAT disagrees with solver `i` iff that solver is wrong at `i` (proved).**  For Booleans,
`sat i = !(f i i)` is equivalent to `f i i ≠ sat i`. -/
theorem disagree_iff_wrong (sat : ℕ → Bool) (f : ℕ → ℕ → Bool) (i : ℕ) :
    DisagreesAt sat f i ↔ ¬ CorrectAt sat f i := by
  show (sat i = !(f i i)) ↔ ¬ (f i i = sat i)
  cases sat i <;> cases f i i <;> decide

/-- **SAT disagrees with every wrong solver (proved) — for free.**  Being correct, SAT differs from any
solver that is wrong at the diagonal input.  This half needs no lower bound. -/
theorem disagrees_with_wrong_solver (sat : ℕ → Bool) (f : ℕ → ℕ → Bool) (i : ℕ)
    (h : ¬ CorrectAt sat f i) : DisagreesAt sat f i :=
  (disagree_iff_wrong sat f i).mpr h

/-- **SAT agrees with every correct solver (proved).**  If solver `i` is correct at `i`, SAT does not
disagree there — it is a fixed point of that solver.  So a correct small solver blocks the diagonal. -/
theorem agrees_with_correct_solver (sat : ℕ → Bool) (f : ℕ → ℕ → Bool) (i : ℕ)
    (h : CorrectAt sat f i) : ¬ DisagreesAt sat f i :=
  fun hd => (disagree_iff_wrong sat f i).mp hd h

/-! ### Full disagreement = no correct solver -/

/-- **SAT is the diagonal iff every solver is wrong (proved).**  SAT disagrees with *every* solver — is
the diagonal, is hard — exactly when no solver is correct at its own diagonal input.  That is `SAT ∉ P`. -/
theorem full_disagreement_iff_all_wrong (sat : ℕ → Bool) (f : ℕ → ℕ → Bool) :
    (∀ i, DisagreesAt sat f i) ↔ (∀ i, ¬ CorrectAt sat f i) := by
  constructor
  · intro h i; exact (disagree_iff_wrong sat f i).mp (h i)
  · intro h i; exact (disagree_iff_wrong sat f i).mpr (h i)

/-! ### The self-encoding is neutral -/

/-- **The self-encoding is symmetric between agreement and disagreement (proved).**  There are
configurations where a solver is correct at `i` and configurations where it is wrong — nothing in "SAT
encodes its solver" prefers disagreement.  The symmetry is broken only by which case holds for SAT's
actual small solvers, i.e. by whether a correct one exists — `cost_super`. -/
theorem self_encoding_neutral :
    (∃ (sat : ℕ → Bool) (f : ℕ → ℕ → Bool) (i : ℕ), CorrectAt sat f i) ∧
    (∃ (sat : ℕ → Bool) (f : ℕ → ℕ → Bool) (i : ℕ), ¬ CorrectAt sat f i) := by
  refine ⟨⟨fun _ => true, fun _ _ => true, 0, ?_⟩, ⟨fun _ => true, fun _ _ => false, 0, ?_⟩⟩
  · decide
  · decide

end PallLean.Paper93.DeepMath.PathB.EncodeDisagree

#print axioms PallLean.Paper93.DeepMath.PathB.EncodeDisagree.disagree_iff_wrong
#print axioms PallLean.Paper93.DeepMath.PathB.EncodeDisagree.disagrees_with_wrong_solver
#print axioms PallLean.Paper93.DeepMath.PathB.EncodeDisagree.agrees_with_correct_solver
#print axioms PallLean.Paper93.DeepMath.PathB.EncodeDisagree.full_disagreement_iff_all_wrong
#print axioms PallLean.Paper93.DeepMath.PathB.EncodeDisagree.self_encoding_neutral
