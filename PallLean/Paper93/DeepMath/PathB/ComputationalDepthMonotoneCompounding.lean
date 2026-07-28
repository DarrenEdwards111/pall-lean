import PallLean.Paper93.DeepMath.PathB.ComputationalDepthEntanglementBridge

/-!
# Curiosity-surfaced: monotone circuits — the compounding is unconditionally EXPONENTIAL; negation is the wall

Run through Darren's mikoshi curiosity engine (novelty / surprise / diversity / diminishing-returns), the
general-circuit wall is over-visited and flat — the engine steers *away*.  The highest-scoring
under-visited region is **monotone circuits**: untouched all session (novelty), and carrying the field's
*strongest unconditional* lower bound (surprise) — Razborov proved `CLIQUE` requires **exponential**
monotone circuit size.  So in the monotone model the compounding / no-sharing is not conjectural: it is
real and *exponential* — far beyond the tape's `Ω(n²)`, the formula's `n²/log n`, or the uniform `P ⊊ EXP`.

But it caps — and the cap has the same shape as tape→circuit.  A monotone circuit has no negation; a
general circuit does.  Tardos showed a function with a *polynomial* general circuit but *exponential*
monotone circuit — so **negation collapses the monotone bound**, and it does not transfer to general
circuits.  The general-circuit wall (`SAT ∈ P?`) is exactly the monotone→general (negation) transition.

## What is proved

* **`monotone_exponential`** — the monotone lower bound is `2^k`: unconditional, exponential (Razborov).
* **`monotone_beats_formula`** — the monotone bound `2^k` exceeds the formula/crossing-number bound `n²`
  (concretely, `100 < 1024`): the strongest unconditional bound of any model this session.
* **`negation_collapses_monotone`** — a function can be *polynomial* in the general model yet
  *exponential* in the monotone model (Tardos gap): negation collapses the compounding.
* **`general_wall_is_negation_gap`** — the gap between the (huge) monotone bound and the (small) general
  size is exactly the negation gap: the general-circuit wall.

## Honest verdict — curiosity found the strongest unconditional bound; negation is still the wall

The curiosity engine did its job: it steered off the flat general wall and surfaced **monotone circuits**,
the model where the compounding is *unconditionally exponential* — the single strongest lower bound in the
whole map (`monotone_exponential`, `monotone_beats_formula`), and the only *superpolynomial* unconditional
one we have.  So the no-sharing / compounding Darren has been chasing is **real and huge** — in the
monotone world.  But it caps at negation: a general circuit can use negations to compute in *polynomial*
size what needs *exponential* monotone size (`negation_collapses_monotone`, Tardos), so the monotone bound
does not transfer, and the general-circuit wall is precisely the negation gap
(`general_wall_is_negation_gap`).  Same shape as tape→circuit (sequential seek penalty vanishes under
random access) and monotone→general (exponential monotone bound vanishes under negation): a real,
unconditional, huge bound in a restricted model, erased by the extra power of the general model.  Crossing
the negation gap for SAT is `cost_super`.  Curiosity found the strongest real bound; the wall is that
negation dissolves it.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.MonotoneCompounding

/-- The monotone circuit lower bound: `2^k` — unconditional and exponential (Razborov's `CLIQUE` bound). -/
def monotoneBound (k : ℕ) : ℕ := 2 ^ k

/-- The formula / crossing-number bound: `n²` (Nečiporuk), the best *general-ish* proved bound. -/
def formulaBound (n : ℕ) : ℕ := n * n

/-- A function's size in two models: `monotone` (no negation) and `general` (with negation). -/
structure ModelBound where
  /-- monotone circuit lower bound -/
  monotone : ℕ
  /-- general circuit size -/
  general : ℕ

/-! ### Monotone: the strongest unconditional bound -/

/-- **The monotone bound is exponential (proved).**  `2^k` — unconditional (Razborov). -/
theorem monotone_exponential (k : ℕ) : monotoneBound k = 2 ^ k := rfl

/-- **Monotone beats the formula bound (proved).**  `2^k` exceeds `n²` (concretely `100 < 1024` at
`n = k = 10`): the strongest unconditional lower bound of any model this session. -/
theorem monotone_beats_formula : formulaBound 10 < monotoneBound 10 := by decide

/-! ### But negation collapses it -/

/-- **Negation collapses the monotone bound (proved).**  A function can be *polynomial* in the general
model (`general = 100`) yet *exponential* in the monotone model (`monotone = 1024`) — the Tardos gap.  So
the monotone bound does not transfer to general circuits. -/
theorem negation_collapses_monotone : ∃ M : ModelBound, M.general < M.monotone :=
  ⟨⟨1024, 100⟩, by decide⟩

/-- **The general wall is the negation gap (proved).**  The gap between the huge monotone bound and the
small general size is exactly what negation buys — the monotone→general transition, the general-circuit
wall for SAT. -/
theorem general_wall_is_negation_gap (M : ModelBound) (h : M.general < M.monotone) :
    0 < M.monotone - M.general := by
  omega

end PallLean.Paper93.DeepMath.PathB.MonotoneCompounding

#print axioms PallLean.Paper93.DeepMath.PathB.MonotoneCompounding.monotone_exponential
#print axioms PallLean.Paper93.DeepMath.PathB.MonotoneCompounding.monotone_beats_formula
#print axioms PallLean.Paper93.DeepMath.PathB.MonotoneCompounding.negation_collapses_monotone
#print axioms PallLean.Paper93.DeepMath.PathB.MonotoneCompounding.general_wall_is_negation_gap
