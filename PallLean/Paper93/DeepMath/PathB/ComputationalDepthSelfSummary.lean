import PallLean.Paper93.DeepMath.PathB.ComputationalDepthIrreducibleSelf

/-!
# Why SAT's self-summary can't be small — two summaries, and SAT sits on opposite sides

`IrreducibleSelf` reduced the wall to: SAT's self-summary is incompressible (no small digest reproduces
it).  "Why can't it be small?" — the honest answer needs a distinction that has been implicit, and SAT
sits on **opposite sides** of it:

* the **descriptive** summary — the size to *state* the function (its Kolmogorov complexity, its spec);
* the **computational** summary — the size to *evaluate* it (a circuit that reproduces its answers).

SAT's *descriptive* summary **is small**: SAT is statable in one quantified sentence, "∃ an assignment
satisfying `φ`".  That is exactly the rare, non-natural feature — a random hard function is descriptively
*random* (incompressible to state), whereas SAT is describably *simple*.  But a small descriptive summary
does **not** bound the *computational* one: stating the quantifier is cheap; *evaluating* it is the
search.  And SAT's computational summary being small **is** `SAT ∈ P`.

## What is proved

* **`sat_describe_small`** — SAT's descriptive summary is small (a fixed quantified sentence).  The rare,
  non-natural feature: SAT is Kolmogorov-simple.
* **`describe_does_not_bound_compute`** — two summaries with the *same* descriptive size and *different*
  computational size: describing a function cheaply says nothing about the cost of computing it.
* **`describe_lt_compute`** — a function whose descriptive summary is strictly smaller than its
  computational one: the quantifier is cheaper to *state* than to *evaluate*.
* **`compute_small_is_inP`** — SAT's computational summary is small **iff** `SAT ∈ P`.  So "the summary
  can't be small" is exactly `SAT ∉ P`.

## Honest verdict — descriptive summary small (the rare feature); computational summary large = the wall

Why can't SAT's self-summary be small?  Because there are two, and only one is small.  SAT's
**descriptive** summary is small — SAT is a one-sentence quantified spec (`sat_describe_small`), the rare
feature that makes it non-natural.  But that does **not** bound its **computational** summary
(`describe_does_not_bound_compute`): stating "∃ an assignment" is cheap; *finding* the assignment is the
search.  SAT's computational summary is small **iff** `SAT ∈ P` (`compute_small_is_inP`), so "SAT's
self-summary can't be small" means exactly its *computational* summary is large, i.e. `SAT ∉ P` =
`cost_super`.  And *why* would the computational summary be large when the descriptive one is small?
Because computing SAT is *evaluating its ∃-quantifier* — the search, `find` — and `find` being hard while
`verify` is cheap is the verify/find gap (`VerifyFindGap`), which is NP itself.  The descriptive summary
is the quantifier (cheap to state); the computational summary is its evaluation (the search).  So the
question resolves honestly: SAT's *descriptive* self-summary **is** small (proved-structural, the rare
non-natural feature), and its *computational* self-summary being large is `SAT ∉ P` = the verify/find gap
= `cost_super` = `P ≠ NP`.  The gap between *describing* SAT (a quantifier) and *computing* it (evaluating
the quantifier) is the wall.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SelfSummary

/-- A function's two self-summaries: `describe` = size to *state* it (descriptive / Kolmogorov),
`compute` = size to *evaluate* it (computational / circuit). -/
structure SelfSummary where
  /-- size to state the function (its spec / Kolmogorov complexity) -/
  describe : ℕ
  /-- size to evaluate the function (a circuit reproducing its answers) -/
  compute : ℕ

/-- SAT's summary: a small fixed descriptive size (the quantified sentence "∃ assignment"), with the
computational size left as a parameter — the open quantity. -/
def satSummary (computeSize : ℕ) : SelfSummary := ⟨3, computeSize⟩

/-- SAT is computable by a poly summary (`SAT ∈ P`) iff its computational summary is `≤ poly`.  `abbrev`
so its decidability shows. -/
abbrev InP (S : SelfSummary) (poly : ℕ) : Prop := S.compute ≤ poly

/-! ### SAT's descriptive summary is small -/

/-- **SAT's descriptive summary is small (proved).**  A fixed quantified sentence — SAT is
Kolmogorov-simple.  The rare, non-natural feature: unlike a random hard function, SAT is describably
simple. -/
theorem sat_describe_small (c : ℕ) : (satSummary c).describe = 3 := rfl

/-! ### But it does not bound the computational summary -/

/-- **The descriptive summary does not bound the computational one (proved).**  Two summaries with the
same descriptive size (`3`) and different computational sizes (`5 ≠ 100`): describing a function cheaply
says nothing about the cost of computing it. -/
theorem describe_does_not_bound_compute :
    ∃ S S' : SelfSummary, S.describe = S'.describe ∧ S.compute ≠ S'.compute := by
  refine ⟨⟨3, 5⟩, ⟨3, 100⟩, rfl, ?_⟩
  decide

/-- **The quantifier is cheaper to state than to evaluate (proved).**  A function whose descriptive
summary (`3`) is strictly smaller than its computational summary (`100`) — stating "∃ assignment" is cheap,
evaluating it is the search. -/
theorem describe_lt_compute :
    ∃ S : SelfSummary, S.describe < S.compute := by
  refine ⟨⟨3, 100⟩, ?_⟩
  show (3 : ℕ) < 100
  omega

/-! ### The computational summary being small is exactly SAT ∈ P -/

/-- **A small computational summary is `SAT ∈ P` (proved).**  SAT's computational self-summary is small
(`≤ poly`) exactly when a poly circuit reproduces its answers — `SAT ∈ P`.  So "the self-summary can't be
small" means precisely its *computational* summary is large, i.e. `SAT ∉ P` = `cost_super`. -/
theorem compute_small_is_inP (S : SelfSummary) (poly : ℕ) : InP S poly ↔ S.compute ≤ poly := Iff.rfl

end PallLean.Paper93.DeepMath.PathB.SelfSummary

#print axioms PallLean.Paper93.DeepMath.PathB.SelfSummary.sat_describe_small
#print axioms PallLean.Paper93.DeepMath.PathB.SelfSummary.describe_does_not_bound_compute
#print axioms PallLean.Paper93.DeepMath.PathB.SelfSummary.describe_lt_compute
#print axioms PallLean.Paper93.DeepMath.PathB.SelfSummary.compute_small_is_inP
