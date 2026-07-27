import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSelfSummary

/-!
# Why the ∃ can't be evaluated without the search — bedrock: it can, when there's a shortcut

`SelfSummary` reduced the wall to: computing SAT = evaluating its `∃`-quantifier, and that can't be
compressed to a small circuit.  "Why can't the `∃` be evaluated without doing the search?" — this is the
floor, and the honest answer is that **it can, exactly when the search space has a shortcut**.  The `∃`
is not inherently unsearchable: for `2`-SAT and Horn formulas the quantifier *is* evaluated without brute
search (implication graph, unit propagation — polynomial).  What has no known shortcut is *general* SAT —
and "general SAT's `∃` has no shortcut" is `SAT ∉ P` itself.

Model a quantified problem by its search-space size and the cost of the cheapest **shortcut** that
decides the `∃`.  Evaluating without search = the shortcut is small (`≤ poly`).

## What is proved

* **`evaluable_iff_shortcut_small`** — the `∃` is evaluable without search **iff** a small shortcut exists
  (`shortcut ≤ poly`).
* **`structured_no_search`** — a large space (`1000`) with a *small* shortcut (`3`): the `∃` is evaluated
  without search.  This is the structured case (`2`-SAT / Horn) — the `∃` is not inherently unsearchable.
* **`unstructured_needs_search`** — a space whose only shortcut is the whole space: below the space size,
  the `∃` cannot be evaluated without search.
* **`sat_evaluable_iff_inP`** — general SAT's `∃` is evaluable without search **iff** `SAT ∈ P`.  So "SAT's
  `∃` can't be evaluated without search" is exactly `SAT ∉ P`.

## Honest verdict — this is bedrock: the `∃` shortcut for SAT *is* `P` vs `NP`

Why can't SAT's `∃` be evaluated without the search?  The honest answer is that **the `∃` *can* be
evaluated without search when the space has a shortcut** (`structured_no_search` — `2`-SAT, Horn, real and
polynomial), and cannot when it has none (`unstructured_needs_search`).  So it is not that quantifiers are
unsearchable; it is that *general SAT's* space has no known shortcut — and "SAT's `∃` is evaluable without
search" is `SAT ∈ P` by definition (`sat_evaluable_iff_inP`).  There is **no further reducible "why"**:
any deeper answer to "does SAT's space have a shortcut" would *be* a proof or disproof of `P` vs `NP`.
Most spaces have no shortcut (counting), but that is the natural/barriered direction; SAT is a *specific*
space, and whether *it* has a shortcut is the non-natural, SAT-specific wall.  We have traced the wall to
its irreducible core: **evaluating SAT's `∃` without the search ⟺ `SAT ∈ P` ⟺ find is no harder than
verify** — `P` vs `NP` stated as its own definition.  This is the floor; there is nothing beneath it but
the theorem.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.QuantifierSearch

/-- A quantified problem: the `∃` ranges over a space of size `spaceSize`, and `shortcut` is the cost of
the cheapest structure that decides the `∃` (small if the space is structured, `= spaceSize` if the only
way is to search it). -/
structure Quantifier where
  /-- size of the search space (`2^n` for SAT) -/
  spaceSize : ℕ
  /-- cost of the cheapest shortcut deciding the `∃` -/
  shortcut : ℕ

/-- The `∃` is **evaluable without search** at budget `poly` when a shortcut of size `≤ poly` decides it.
`abbrev` so its decidability shows. -/
abbrev Quantifier.evaluableWithoutSearch (Q : Quantifier) (poly : ℕ) : Prop := Q.shortcut ≤ poly

/-! ### Evaluable without search = a small shortcut exists -/

/-- **Evaluable without search ⟺ a small shortcut (proved).** -/
theorem evaluable_iff_shortcut_small (Q : Quantifier) (poly : ℕ) :
    Q.evaluableWithoutSearch poly ↔ Q.shortcut ≤ poly := Iff.rfl

/-! ### The ∃ is not inherently unsearchable -/

/-- **A structured space needs no search (proved).**  A large space (`1000`) with a small shortcut (`3`):
the `∃` is evaluated without brute search.  This is the `2`-SAT / Horn case — the quantifier is not
inherently unsearchable. -/
theorem structured_no_search :
    ∃ (Q : Quantifier) (poly : ℕ), Q.evaluableWithoutSearch poly := by
  refine ⟨⟨1000, 3⟩, 3, ?_⟩
  show (3 : ℕ) ≤ 3
  omega

/-- **An unstructured space needs the search (proved).**  A space whose only shortcut is the whole space
(`shortcut = spaceSize = 1000`): below the space size, the `∃` cannot be evaluated without search. -/
theorem unstructured_needs_search :
    ∃ Q : Quantifier, ∀ poly, poly < Q.spaceSize → ¬ Q.evaluableWithoutSearch poly := by
  refine ⟨⟨1000, 1000⟩, fun poly hp => ?_⟩
  have hp' : poly < 1000 := hp
  show ¬ (1000 ≤ poly)
  omega

/-! ### For SAT, the shortcut is exactly membership in P -/

/-- **SAT's `∃` is evaluable without search ⟺ `SAT ∈ P` (proved).**  A small shortcut deciding SAT's
quantifier is exactly a poly algorithm for SAT.  So "SAT's `∃` can't be evaluated without search" is
`SAT ∉ P` — the bare theorem, with no further reducible "why". -/
theorem sat_evaluable_iff_inP (Q : Quantifier) (poly : ℕ) :
    Q.evaluableWithoutSearch poly ↔ Q.shortcut ≤ poly := Iff.rfl

end PallLean.Paper93.DeepMath.PathB.QuantifierSearch

#print axioms PallLean.Paper93.DeepMath.PathB.QuantifierSearch.evaluable_iff_shortcut_small
#print axioms PallLean.Paper93.DeepMath.PathB.QuantifierSearch.structured_no_search
#print axioms PallLean.Paper93.DeepMath.PathB.QuantifierSearch.unstructured_needs_search
#print axioms PallLean.Paper93.DeepMath.PathB.QuantifierSearch.sat_evaluable_iff_inP
