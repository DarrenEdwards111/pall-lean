/-
  PallLean/Paper93/Direct/AdjacencyDerivs.lean

  Agent M7 of M (parallel) — Direct discharge of the per-derivative
  membership obligation for the adjacency factor in the concrete
  `concreteW`-derivative closure.

  ## Scope

  Paper §9 Lemma 31's spanning pipeline upgrades the per-factor
  ambient-membership statement

      (1 - X_i · X_j)  ∈  concreteW n hn4 σ .adjacency

  (supplied by Agent M6, `adjacency_factor_direct_mem`,
  `Paper93/Direct/AdjacencyDirect.lean`) to the per-derivative form

      iterDerivList S (1 - X_i · X_j)
          ∈  iterDerivSubmodule (concreteW n hn4 σ .adjacency) S

  consumed by the `allBoundedProfilePostSpan` pipeline.  The transport
  is the purely linear-algebraic closure statement supplied by Agent
  H4, `iterDerivList_mem_iterDerivSubmodule`
  (`Paper93/Spanning/DerivativeClosure.lean`, commit `8fba527`):

      f ∈ W  ⟹  iterDerivList S f ∈ iterDerivSubmodule W S.

  Specialised at `W := concreteW n hn4 σ .adjacency` and
  `f := 1 - X_i · X_j`, this upgrades M6's deliverable to the
  per-derivative membership form required downstream.

  ## Deliverable

    * `adjacency_iterDeriv_mem` — for every Turing-machine parameter
      tuple `(M, n, hn, htb, hns)` with `hn4 : n ≥ 4`, every pair of
      distinct indices `(i, j)` with `i ≠ j`, and every tape-variable
      index list `S : List (Fin n)`, there exists an embedding
      `σ : Fin 4 ↪ Fin n` along which the iterated partial derivative
      `iterDerivList S (1 - X_i · X_j)` lies in the iterated
      derivative-closure submodule
      `iterDerivSubmodule (concreteW n hn4 σ .adjacency) S`.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  Expected `#print axioms`:
      [propext, Classical.choice, Quot.sound]
-/
import PallLean.Paper93.Direct.AdjacencyDirect
import PallLean.Paper93.Spanning.DerivativeClosure
import PallLean.Paper93.Wiring.ConcreteW

namespace PallLean.Paper93.Direct

open MvPolynomial SPDP
open PallLean.Paper93
open PallLean.Paper93.Spanning
open PallLean.Paper93.Wiring
open SymmetricPowerBound (ConstraintType)

/-- **Agent M7: per-derivative membership for the adjacency factor in
the concrete `W_σ`-derivative closure.**

For every Turing-machine parameter tuple `(M, n, hn, htb, hns)` with
`hn4 : n ≥ 4`, every pair of distinct indices `(i, j)` with
`hij : i ≠ j`, and every tape-variable index list `S : List (Fin n)`,
there exists an embedding `σ : Fin 4 ↪ Fin n` along which the iterated
partial derivative `iterDerivList S (1 - X_i · X_j)` lies in the
iterated derivative-closure submodule
`iterDerivSubmodule (concreteW n hn4 σ .adjacency) S`.

The `hS` parameter is a placeholder for any downstream side condition
on `S` (e.g. a length bound); the result holds uniformly in `S` and
`hS` is not consumed by the proof.

The proof composes:

  * Agent M6's `adjacency_factor_direct_mem`
    (`Paper93/Direct/AdjacencyDirect.lean`) — supplies an embedding
    `σ : Fin 4 ↪ Fin n` with
    `(1 - X_i * X_j) ∈ concreteW n hn4 σ .adjacency`;

  * Agent H4's `iterDerivList_mem_iterDerivSubmodule`
    (`Paper93/Spanning/DerivativeClosure.lean`, commit `8fba527`) —
    transports per-factor membership `f ∈ W` to per-derivative
    membership `iterDerivList S f ∈ iterDerivSubmodule W S`.
-/
theorem adjacency_iterDeriv_mem
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (i j : Fin n) (hn4 : n ≥ 4) (S : List (Fin n))
    (hij : i ≠ j) (hS : True) :
    ∃ σ : Fin 4 ↪ Fin n,
      SPDP.iterDerivList S
          (1 - MvPolynomial.X i * MvPolynomial.X j :
              MvPolynomial (Fin n) ℚ)
        ∈ PallLean.Paper93.Spanning.iterDerivSubmodule
            (PallLean.Paper93.Wiring.concreteW n hn4 σ
                ConstraintType.adjacency) S := by
  -- Step 1 (M6): obtain the σ-witness together with the per-factor
  -- membership `(1 - X_i * X_j) ∈ concreteW n hn4 σ .adjacency`.
  obtain ⟨σ, hMem⟩ :=
    adjacency_factor_direct_mem M n hn htb hns i j hn4 hij
  refine ⟨σ, ?_⟩
  -- Silence unused-argument linter on the placeholder side condition.
  let _ := hS
  -- Step 2 (H4): transport per-factor membership to per-derivative
  -- membership via `iterDerivList_mem_iterDerivSubmodule` at
  -- `W := concreteW n hn4 σ .adjacency` and `f := 1 - X_i * X_j`.
  exact
    PallLean.Paper93.Spanning.iterDerivList_mem_iterDerivSubmodule
      (W := PallLean.Paper93.Wiring.concreteW n hn4 σ
              ConstraintType.adjacency)
      (f := (1 - MvPolynomial.X i * MvPolynomial.X j :
              MvPolynomial (Fin n) ℚ))
      hMem S

-- Suppress unused-variable lints on the cookLevinQ-shape parameters
-- and the placeholder `hS` side condition retained in the public
-- signature for downstream chain compatibility.
attribute [nolint unusedArguments] adjacency_iterDeriv_mem

/-! ## Kernel-only axiom trace

The deliverable should depend only on
`[propext, Classical.choice, Quot.sound]`, i.e. only the standard
Mathlib kernel axioms. No bespoke axiom is introduced; all content
routes through Agent M6 (`adjacency_factor_direct_mem`) composed with
Agent H4 (`iterDerivList_mem_iterDerivSubmodule`). -/

#print axioms adjacency_iterDeriv_mem

end PallLean.Paper93.Direct
