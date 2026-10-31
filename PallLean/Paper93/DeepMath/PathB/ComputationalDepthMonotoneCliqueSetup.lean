import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer10Monotone

/-!
# Monotone clique — SETUP for a from-scratch Razborov lower bound (NOT the lower bound)

Honest scoping: the repo has the monotone circuit **model** (`Layer10Monotone`: `MCircuit`, `eval`, `size`,
`monotone circuits compute only monotone functions`) but **no** monotone-circuit *size* lower bound.
Razborov's theorem — `k`-CLIQUE requires `n^{Ω(log n)}` monotone circuit size — is **not** in the repo, and
formalizing it is a large from-scratch effort (the *method of approximations*: legitimate approximator gates
closed under `∧`/`∨` with sunflower-plucking error control, applied to `CLIQUE` positive tests vs `COCLIQUE`
negative tests). This file is the **first, genuine, but elementary component**: the clique Boolean function
and its monotonicity. It is **setup**, explicitly *not* the lower bound.

## What is proved (clean axioms, no `sorry`)

* `cliqueFn` — the `k`-clique indicator on an `m`-vertex graph given by adjacency `adj : Fin m → Fin m → Bool`.
* `cliqueFn_monotone` — `cliqueFn` is monotone in the edge set (adding edges preserves cliques): the object
  lives in the monotone world, so a monotone circuit for it is not ruled out a priori.

## The target (NOT proved — the from-scratch content)

`RazborovCliqueTarget`: every `MCircuit` computing `cliqueFn` (under an edge encoding) has size `n^{Ω(log n)}`.
Roadmap: (1) approximator gates + the legitimate/approximate closure under `∧`,`∨`; (2) the sunflower lemma
for plucking (the repo's `ACC0SunflowerCellCount` sunflower machinery may seed this); (3) `CLIQUE`/`COCLIQUE`
test distributions and the error-accumulation count. This is the large multi-turn work; none of it is done.

## Honest scope

The monotone clique **function** and its monotonicity — real, elementary setup. The Razborov **size lower
bound** is unstarted and is a major from-scratch formalization. `AC⁰`/monotone tier; nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.MonotoneClique

/-- **The `k`-clique indicator.**  A graph on `m` vertices is given by its (symmetric) adjacency
`adj : Fin m → Fin m → Bool`; `cliqueFn m k adj` holds iff the graph contains a `k`-vertex clique. -/
def cliqueFn (m k : ℕ) (adj : Fin m → Fin m → Bool) : Prop :=
  ∃ S : Finset (Fin m), S.card = k ∧ ∀ i ∈ S, ∀ j ∈ S, i ≠ j → adj i j = true

/-- **`cliqueFn` is monotone in the edge set (proved).**  Adding edges (`adj i j = true ⇒ adj' i j = true`)
preserves every clique, so `cliqueFn m k adj → cliqueFn m k adj'`.  Hence `CLIQUE` is a monotone function —
the setting where a monotone-circuit lower bound is the honest target. -/
theorem cliqueFn_monotone (m k : ℕ) {adj adj' : Fin m → Fin m → Bool}
    (h : ∀ i j, adj i j = true → adj' i j = true) :
    cliqueFn m k adj → cliqueFn m k adj' := by
  rintro ⟨S, hcard, hedge⟩
  exact ⟨S, hcard, fun i hi j hj hij => h i j (hedge i hi j hj hij)⟩

/-- **A `k`-clique is witnessed by a `k`-subset all of whose distinct pairs are edges (proved, definitional).**
Records the witness shape the approximation method will test against. -/
theorem cliqueFn_iff (m k : ℕ) (adj : Fin m → Fin m → Bool) :
    cliqueFn m k adj ↔
      ∃ S : Finset (Fin m), S.card = k ∧ ∀ i ∈ S, ∀ j ∈ S, i ≠ j → adj i j = true :=
  Iff.rfl

end PallLean.Paper93.DeepMath.PathB.MonotoneClique

#print axioms PallLean.Paper93.DeepMath.PathB.MonotoneClique.cliqueFn_monotone
