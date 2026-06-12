import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchCostLowerBound

/-!
# The framework's ceiling, as a theorem: the brute-force / full-boundary escape (proved)

Every lower bound in the debt arc has the shape `|P| ≤ 2^{B_0} + (boundary/switch action)`.  This file proves,
rather than merely asserts, **why the framework cannot reach `P ≠ NP`**: once the initial boundary reaches
`log₂|P|`, the bound is vacuous *and is actually achieved* by a brute-force observer that separates everything
in a single step with zero debt.  This is the honest guardrail — it formalizes the boundary escape that all the
restricted results fence off, so no result above can be mistaken for more than it is.

## Proved (clean axioms, no `sorry`)

* `tradeoff_vacuous_of_high_initial_boundary` — if `|P| ≤ 2^{B_0}` the tradeoff bound `|P| ≤ 2^{B_0} + rest`
  holds for *any* `rest`: it imposes **no constraint** on the boundary action or switch cost.  A high initial
  boundary makes the whole inequality content-free.
* `hypercube_brute_force_escape` — the escape is not merely a gap in the bound but is **realised**: there is a
  single view `(Fin n → Bool) → Fin (2^n)` (boundary `B_0 = n`) with `debtCount (hypercubeFool n) view = 0` —
  a brute-force observer that resolves the entire `2^n` witness geometry in one step, zero debt, zero time,
  zero switch cost.  So against full-boundary observers the framework forces **nothing**.

## Why this is the honest ceiling (not a defeat, a delimitation)

The debt framework gives genuine *time* lower bounds exactly when the boundary is **sub-`log|P|`** (sub-linear
width for the `2^n` geometry): there the action `2^{B_τ}` is small per step, so many steps are forced.  Once
the boundary reaches `log₂|P| ≈ n`, a single step has enough states to index every fooling-set element, debt
drops to `0` for free, and `2^{B_0} ≥ |P|` satisfies every bound trivially.  This is the brute-force decider —
it uses linear space and decides in one "macro-step".

So the boundary-vs-time/switch trade is **fundamental to the mechanism**, not a missing lemma: the fooling-set
debt `≥ |P| − 2^{B}` is informative only for `2^{B} < |P|`.  Closing `P ≠ NP` would require a lower bound that
*also* bites against full-boundary (linear-space) observers — i.e. ruling out the brute-force escape — which
is precisely the content the fooling-debt mechanism cannot supply, and which is the open all-decompositions
quantifier.  This theorem makes that boundary between provable-here and open-there a proved statement.
-/

namespace PallLean.Paper93.DeepMath.PathB.BoundaryDebt

open scoped BigOperators

variable {X : Type*} [DecidableEq X]

/-- **The bound is vacuous at high initial boundary (proved).**  If `|P| ≤ 2^{B_0}` then the tradeoff
inequality `|P| ≤ 2^{B_0} + rest` holds for any `rest` — it constrains neither the boundary action nor the
switch cost.  A high initial boundary makes the whole framework content-free. -/
theorem tradeoff_vacuous_of_high_initial_boundary (P : Finset X) (B0 rest : ℕ)
    (hbig : P.card ≤ 2 ^ B0) :
    P.card ≤ 2 ^ B0 + rest := by
  omega

/-- **The brute-force escape is realised (proved).**  There is a single view of boundary `n`
(`(Fin n → Bool) → Fin (2^n)`) that resolves the *entire* `2^n` hypercube witness geometry with **zero debt**:
a brute-force observer deciding in one step with no time and no switch cost.  Hence the framework forces no
positive lower bound against full-boundary (linear-space) observers. -/
theorem hypercube_brute_force_escape (n : ℕ) :
    ∃ view0 : (Fin n → Bool) → Fin (2 ^ n), debtCount (hypercubeFool n) view0 = 0 := by
  have hcard : Fintype.card (Fin n → Bool) = 2 ^ n := by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  refine ⟨fun x => Fintype.equivFinOfCardEq hcard x, correct_view_zero_debt _ _ ?_⟩
  intro p hp
  rw [hypercubeFool, Finset.mem_filter] at hp
  exact fun h => hp.2 ((Fintype.equivFinOfCardEq hcard).injective h)

end PallLean.Paper93.DeepMath.PathB.BoundaryDebt

#print axioms PallLean.Paper93.DeepMath.PathB.BoundaryDebt.tradeoff_vacuous_of_high_initial_boundary
#print axioms PallLean.Paper93.DeepMath.PathB.BoundaryDebt.hypercube_brute_force_escape
