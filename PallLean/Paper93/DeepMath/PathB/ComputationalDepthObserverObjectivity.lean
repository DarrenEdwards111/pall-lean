import Mathlib.Data.Nat.Basic

/-!
# The observers must agree — `cbudget(SAT)` is objective, not perspective-relative

Darren's final move: it's all about the perspective of the respective observer — hypercomputation outside
the P bubble, ordinary compute inside, the reading of "SAT is huge" set by which observer you are.

The two-observer picture is a beautiful *frame*, but it cannot make the answer observer-relative — and
this is the deep reason no observer/level/fuel trick closes the proof.  `cbudget(SAT)` is a **single
definite number** (the size of the smallest circuit for SAT).  It does not depend on who is looking.

* **`observers_cannot_both_be_right` (proved)** — a *single* value `cbudget(SAT)` cannot be both `≤ low`
  (the inside/P reading) and `≥ high` (the outside/SAT reading) when `low < high`.  So the two observers
  do **not** hold two valid perspectives on one thing — *at most one is correct*, and which one is a
  definite, observer-independent fact.

* **`separation_is_objective` (proved)** — the separation is exactly the objective inequality
  `high ≤ cbudget(SAT)`.  It mentions no observer, no level, no fuel.  Proving it is proving a fact about
  a number, not adopting a viewpoint.

## Why perspective can't resolve it

The inside observer reads *small* ⟺ SAT is easy ⟺ P = NP.  The outside observer reads *huge* ⟺ SAT is
hard ⟺ P ≠ NP.  These are contradictory claims about **one number**; perspective does not make both true,
it just names the two possible answers.  Hypercomputation "setting the reading" (`L_H`) is outside the
model and cannot fix an in-model number (`LevelSegregation`).

The only *legitimate* "perspective" is the choice of a complexity **measure** `μ` — and that is in-model,
not hypercomputational.  Different measures see different lower bounds (Khrapchenko `n²`, shrinkage `n³`);
the separation needs one that sees `2^d`.  That is the `ResistanceProof` obligation, and it is open.  It
is a search for the right *measure*, not the right *observer*.

**Honest scope.**  Proved: `cbudget(SAT)` is observer-independent, so the observers must agree and the
separation is an objective inequality.  Perspective frames the question; it does not answer it.  Nothing
here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ObserverObjectivity

/-- **The observers cannot both be right (proved).**  `cbudget(SAT)` is one number.  It cannot be both
`≤ low` (inside/P) and `≥ high` (outside/SAT) with `low < high`.  So the two "perspectives" are not both
valid views of one object — at most one is correct, objectively. -/
theorem observers_cannot_both_be_right (cbudgetSAT low high : ℕ) (hgap : low < high)
    (inside : cbudgetSAT ≤ low) (outside : high ≤ cbudgetSAT) : False := by
  omega

/-- **The separation is objective (proved).**  It is exactly the inequality `high ≤ cbudget(SAT)` — a
fact about a number, mentioning no observer, level, or fuel.  Given the P-side reading `cbudget(SAT) ≤
low` and a gap `low < high`, the outside reading `high ≤ cbudget(SAT)` is *false*: which observer is
right is definite, not a matter of viewpoint. -/
theorem separation_is_objective (cbudgetSAT low high : ℕ) (hgap : low < high)
    (inside : cbudgetSAT ≤ low) : ¬ (high ≤ cbudgetSAT) := by
  omega

end PallLean.Paper93.DeepMath.PathB.ObserverObjectivity

#print axioms PallLean.Paper93.DeepMath.PathB.ObserverObjectivity.observers_cannot_both_be_right
#print axioms PallLean.Paper93.DeepMath.PathB.ObserverObjectivity.separation_is_objective
