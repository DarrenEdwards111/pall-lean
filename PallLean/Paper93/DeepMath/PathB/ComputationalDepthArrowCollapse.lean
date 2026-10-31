import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCircuitUniversality

/-!
# Attacking the arrow directly: the conjecture collapses to cost_super, and is not generic

With `Universality` now a proved theorem, attack the remaining arrow
`SelfReferenceForcesDoubling cbudget = Universality → WhatIsLeft cbudget` head-on.  Two findings,
both machine-checked.

**Finding 1 — the collapse.**  `conjecture_iff_cost_super`: since the hypothesis is a theorem, the
material implication is *logically equivalent* to its conclusion — the conjecture **is** `cost_super`,
no more and no less.  The self-reference route's remaining content, *as a statement*, is exactly the
wall.  What the route can still be is a proof **strategy** (derive the doubling *using* universality,
Kannan/Williams-style) — a material implication cannot carry "the proof must use the hypothesis", and
the formalization exposes that precisely.

**Finding 2 — the arrow is not generic.**  Its truth varies with the cost function:
`arrow_trivial_for_doubling` (for a doubling budget it holds trivially) and `arrow_false_for_flat`
(for a flat budget it is FALSE — with `Universality` true, the hypothesis cannot save it), hence
`arrow_not_generic`.  So **no argument uniform in `cbudget` can prove the conjecture**: any proof must
consume the actual definition of the SAT tower's cost (the real minimal `CGate` count).  This is where
the naive bootstrap breaks: universality is one true closed statement; from it plus *nothing about the
specific cost*, nothing follows — the flat cost is the counterexample.

## Honest scope — the break located, nothing faked

The direct attack neither proves nor refutes the doubling.  What it proves is *where the attack must
go*: the missing step is a fact about the **real** cost that a flat cost lacks — a diagonal/hierarchy
ingredient (something the real cost provably cannot do cheaply).  At Σ₂/NEXP altitude that ingredient
exists (Kannan, Williams); at `P` altitude it is `cost_super` itself.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ArrowCollapse

open PallLean.Paper93.DeepMath.PathB.CircuitUniversality
open PallLean.Paper93.DeepMath.PathB.WhatRemains

/-- **The collapse (proved).**  With `Universality` a theorem, the self-reference conjecture is
logically equivalent to bare `cost_super`: the route's remaining content, as a statement, is exactly
the wall.  Self-reference survives as a strategy, not a reduction. -/
theorem conjecture_iff_cost_super (cbudget : ℕ → ℕ) :
    SelfReferenceForcesDoubling cbudget ↔ WhatIsLeft cbudget :=
  ⟨fun h => h universality, fun h _ => h⟩

/-- **The arrow holds trivially for a doubling budget (proved).**  Nothing about SAT is used. -/
theorem arrow_trivial_for_doubling : SelfReferenceForcesDoubling (fun d => 2 ^ d) := by
  intro _ d
  show 2 * 2 ^ d ≤ 2 ^ (d + 1)
  rw [Nat.pow_succ]
  omega

/-- **The arrow is false for a flat budget (proved).**  `Universality` is true, so the hypothesis
cannot save the implication: with a flat cost, the doubling fails at depth `0`. -/
theorem arrow_false_for_flat : ¬ SelfReferenceForcesDoubling (fun _ => 1) := by
  intro h
  have h1 : 2 * 1 ≤ 1 := h universality 0
  omega

/-- **The arrow is not generic (proved).**  Its truth varies with the cost function, so no proof
uniform in `cbudget` exists: any proof of the conjecture must consume the actual definition of the
SAT tower's cost. -/
theorem arrow_not_generic :
    ¬ ∀ cbudget : ℕ → ℕ, SelfReferenceForcesDoubling cbudget :=
  fun h => arrow_false_for_flat (h _)

end PallLean.Paper93.DeepMath.PathB.ArrowCollapse

#print axioms PallLean.Paper93.DeepMath.PathB.ArrowCollapse.conjecture_iff_cost_super
#print axioms PallLean.Paper93.DeepMath.PathB.ArrowCollapse.arrow_false_for_flat
#print axioms PallLean.Paper93.DeepMath.PathB.ArrowCollapse.arrow_not_generic
