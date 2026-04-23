/-
  PallLean/Paper93/Direct/AdjacencyDirect.lean

  Agent M6 of M (parallel) — Direct discharge of the adjacency
  factor-in-`concreteW` membership obligation.

  ## Scope

  Agent J1 (commit `b36a8b1`) introduces the concrete per-type interface
  family

      concreteW n hn4 σ τ :=
          ambientPerTypeSpace perTypeInterfaceSpace n hn4 σ τ

  as a `Submodule ℚ (MvPolynomial (Fin n) ℚ)`.

  Agent H3 (commit `34e3af5`) proves

      adjacency_factor_mem_ambient_unconditional

  which delivers, for every Turing-machine parameter tuple
  `(M, n, hn, htb, hns)` with `hn4 : n ≥ 4` and every pair of
  distinct indices `(i, j) : Fin n × Fin n` with `i ≠ j`, an embedding
  `σ : Fin 4 ↪ Fin n` along which the compiled Cook-Levin adjacency
  factor `1 - X_i * X_j` lies in the ambient per-type space
  `ambientPerTypeSpace perTypeInterfaceSpace n hn4 σ .adjacency`.

  Since `concreteW n hn4 σ .adjacency` is, by J1's definition,
  *definitionally equal* to
  `ambientPerTypeSpace perTypeInterfaceSpace n hn4 σ .adjacency`,
  H3's theorem is exactly what is required to discharge the membership
  obligation stated against `concreteW`. This file performs that
  discharge, keeping the proof as a direct appeal to the two upstream
  pieces J1 and H3.

  ## What this file delivers

  * `adjacency_factor_direct_mem` —
    for every adjacency constraint factor `1 - X_i * X_j`, there exists
    an embedding `σ : Fin 4 ↪ Fin n` such that the factor lies in
    `concreteW n hn4 σ .adjacency`.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  Expected `#print axioms`:
      [propext, Classical.choice, Quot.sound]
-/
import PallLean.Paper93.Wiring.ConcreteW
import PallLean.Paper93.Spanning.DischargeOneMem

namespace PallLean.Paper93.Direct

open MvPolynomial
open PallLean.Paper93
open PallLean.Paper93.Wiring
open PallLean.Paper93.Spanning
open SymmetricPowerBound (ConstraintType)

/-- **Agent M6: direct adjacency factor membership in the concrete
`W_σ` family.**

For every Turing-machine parameter tuple `(M, n, hn, htb, hns)` with
`hn4 : n ≥ 4` and every pair of distinct indices `(i, j)` with
`i ≠ j`, there exists an embedding `σ : Fin 4 ↪ Fin n` along which the
compiled Cook-Levin adjacency factor `1 - X_i * X_j` lies in Agent J1's
concrete `W_σ` family at the adjacency constraint type,
`concreteW n hn4 σ .adjacency`.

The proof is a direct appeal to Agent H3's
`adjacency_factor_mem_ambient_unconditional` (commit `34e3af5`)
composed with Agent J1's definition
`concreteW n hn4 σ τ = ambientPerTypeSpace perTypeInterfaceSpace n hn4 σ τ`
(commit `b36a8b1`). -/
theorem adjacency_factor_direct_mem
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (i j : Fin n) (hn4 : n ≥ 4) (hij : i ≠ j) :
    ∃ σ : Fin 4 ↪ Fin n,
      (1 - MvPolynomial.X i * MvPolynomial.X j :
          MvPolynomial (Fin n) ℚ)
        ∈ PallLean.Paper93.Wiring.concreteW n hn4 σ
            ConstraintType.adjacency := by
  -- Agent J1's `concreteW` unfolds to H2's `ambientPerTypeSpace`
  -- specialised at H1's per-type source space, so H3's unconditional
  -- adjacency factor membership delivers exactly the required
  -- membership in `concreteW`.
  unfold PallLean.Paper93.Wiring.concreteW
  exact
    PallLean.Paper93.Spanning.adjacency_factor_mem_ambient_unconditional
      M n hn htb hns i j hn4 hij

-- Suppress unused-variable lints on the cookLevinQ-shape parameters
-- retained in the public signature for downstream chain compatibility.
attribute [nolint unusedArguments] adjacency_factor_direct_mem

/-! ## Kernel-only axiom trace

The deliverable should depend only on
`[propext, Classical.choice, Quot.sound]`, i.e. only the standard
Mathlib kernel axioms. No bespoke axiom is introduced. -/

#print axioms adjacency_factor_direct_mem

end PallLean.Paper93.Direct
