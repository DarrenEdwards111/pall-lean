/-
  PallLean/Paper93/Direct/BooleanityDerivs.lean

  Paper §9 Lemma 31 — derivative closure of the booleanity factor
  in the concrete `W_σ(τ)` family.

  Agent M2 of 3 (parallel).

  ## Scope

  This file packages Agent M1's `booleanity_factor_direct_mem`
  (unconditional membership of the compiled booleanity factor
  `1 - X_v + X_v^2` in `concreteW n hn4 σ .booleanity`) through Agent
  H4's per-derivative transport lemma
  `iterDerivList_mem_iterDerivSubmodule` (commit `8fba527`) to conclude
  that, for every bounded list `S : List (Fin n)` with
  `S.length ≤ Nat.log 2 n`, the iterated derivative
  `iterDerivList S (1 - X_v + X_v^2)` lies in the derivative closure
  `iterDerivSubmodule (concreteW n hn4 σ .booleanity) S`.

  The existential on `σ : Fin 4 ↪ Fin n` is witnessed by the same
  embedding Agent M1 supplies.

  ## Deliverable

    * `booleanity_iterDeriv_mem` — for every Turing-machine
      parameter tuple `(M, n, hn, htb, hns)` with `hn4 : n ≥ 4`, every
      variable `v : Fin n`, and every bounded index list
      `S : List (Fin n)` with `S.length ≤ Nat.log 2 n`, there exists an
      embedding `σ : Fin 4 ↪ Fin n` such that
      `iterDerivList S (1 - X_v + X_v^2)` lies in
      `iterDerivSubmodule (concreteW n hn4 σ .booleanity) S`.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  Expected `#print axioms`:
      [propext, Classical.choice, Quot.sound]
-/
import PallLean.Paper93.Direct.BooleanityDirect
import PallLean.Paper93.Spanning.DerivativeClosure

namespace PallLean.Paper93.Direct

open MvPolynomial
open SPDP
open PallLean.Paper93
open PallLean.Paper93.Wiring
open PallLean.Paper93.Spanning
open SymmetricPowerBound (ConstraintType)

/-- **Derivative-closure membership of the compiled booleanity factor.**

For every Turing-machine parameter tuple `(M, n, hn, htb, hns)` with
`hn4 : n ≥ 4`, every variable `v : Fin n`, and every bounded index list
`S : List (Fin n)` with `S.length ≤ Nat.log 2 n`, there is a coordinate
embedding `σ : Fin 4 ↪ Fin n` along which the iterated partial
derivative of the compiled Cook-Levin booleanity factor
`1 - X_v + X_v^2` lies in Agent H4's derivative closure
`iterDerivSubmodule (concreteW n hn4 σ .booleanity) S` of Agent J1's
concrete per-type ambient space.

This is the per-derivative upgrade of Agent M1's
`booleanity_factor_direct_mem`: H4's transport lemma
`iterDerivList_mem_iterDerivSubmodule` converts the per-factor
membership into the per-derivative form consumed by the
`allBoundedProfilePostSpan` machinery.

The boundedness hypothesis `hS : S.length ≤ Nat.log 2 n` is carried in
the signature for paper-faithful call-site alignment with the compiled
`cookLevinQ` derivative budget; H4's transport itself is length-free,
so `hS` is not consumed in the present step and remains available for
downstream uses. -/
theorem booleanity_iterDeriv_mem
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (v : Fin n) (hn4 : n ≥ 4)
    (S : List (Fin n)) (_hS : S.length ≤ Nat.log 2 n) :
    ∃ σ : Fin 4 ↪ Fin n,
      iterDerivList S
          (1 - MvPolynomial.X v + (MvPolynomial.X v) ^ 2 :
            MvPolynomial (Fin n) ℚ)
        ∈ PallLean.Paper93.Spanning.iterDerivSubmodule
            (PallLean.Paper93.Wiring.concreteW n hn4 σ
                ConstraintType.booleanity) S := by
  classical
  -- Step 1: Agent M1 supplies an embedding `σ` with
  --   `1 - X_v + X_v^2 ∈ concreteW n hn4 σ .booleanity`.
  obtain ⟨σ, hMem⟩ :=
    booleanity_factor_direct_mem M n hn htb hns v hn4
  -- Step 2: apply Agent H4's per-derivative transport lemma
  -- `iterDerivList_mem_iterDerivSubmodule` to the factor `f` with
  -- the membership witness from Step 1.
  refine ⟨σ, ?_⟩
  exact PallLean.Paper93.Spanning.iterDerivList_mem_iterDerivSubmodule
    (PallLean.Paper93.Wiring.concreteW n hn4 σ
      ConstraintType.booleanity)
    (1 - MvPolynomial.X v + (MvPolynomial.X v) ^ 2 :
      MvPolynomial (Fin n) ℚ)
    hMem S

/-! ## Kernel-only axiom trace

The deliverable should depend only on
`[propext, Classical.choice, Quot.sound]`. -/

#print axioms booleanity_iterDeriv_mem

end PallLean.Paper93.Direct
