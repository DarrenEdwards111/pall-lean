/-
  PallLean/Paper93/Direct/TransitionLeftDerivs.lean

  Paper §9 Lemma 31 — direct derivative-closure membership for the
  compiled Cook-Levin `transitionLeft` factor polynomial
  `transitionLeftAmbientFactor σ = X (σ 0) : MvPolynomial (Fin n) ℚ`.

  Agent M12 of M (parallel).

  ## Scope

  This file composes two upstream deliverables to produce the
  per-derivative form of the Cook-Levin `transitionLeft` factor
  membership consumed downstream by the per-profile spanning pipeline:

    * Agent M11's `transitionLeft_factor_direct_mem`
      (`PallLean/Paper93/Direct/TransitionLeftDirect.lean`) delivers,
      for any cookLevinQ-compilation parameter tuple
      `(M, n, hn, htb, hns, q, i, j)` with `hn4 : n ≥ 4`, a canonical
      embedding `σ : Fin 4 ↪ Fin n` with

          transitionLeftAmbientFactor σ
              ∈ concreteW n hn4 σ .transitionLeft,

      where `transitionLeftAmbientFactor σ = X (σ 0)` is the rename of
      Agent A's `transitionTemplate = X 0 : MvPolynomial (Fin 4) ℚ`
      along `σ`.

    * Agent H4's derivative closure
      (`PallLean/Paper93/Spanning/DerivativeClosure.lean`,
      commit `8fba527`) supplies `iterDerivSubmodule W S`, the ambient
      sub-module consisting of all iterated partial derivatives
      `iterDerivList S f` for `f ∈ W`, together with the transport
      lemma

          f ∈ W → iterDerivList S f ∈ iterDerivSubmodule W S.

  Composing M11 and H4 yields the Agent M12 deliverable: for every
  cookLevinQ-compilation parameter tuple with `hn4 : n ≥ 4`, every
  per-instance transitionLeft factor parameterisation `(q, i, j)`, and
  every derivative list `S : List (Fin n)`, there exists an embedding
  `σ : Fin 4 ↪ Fin n` with

      iterDerivList S (transitionLeftAmbientFactor σ)
          ∈ iterDerivSubmodule (concreteW n hn4 σ .transitionLeft) S.

  This mirrors Agent M2's `booleanity_iterDeriv_mem` and Agent M7's
  `adjacency_iterDeriv_mem` at the `transitionLeft` constraint type,
  and sits one step "lighter" than Agent M13's shift-composed variant
  `transitionLeft_shift_deriv_mem`, which multiplies by a bounded-degree
  shift and lifts the result into the shift closure.

  ## Deliverable

    * `transitionLeft_iterDeriv_mem` — the composed membership.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  Expected `#print axioms`:
      [propext, Classical.choice, Quot.sound]
-/
import PallLean.Paper93.Direct.TransitionLeftDirect
import PallLean.Paper93.Spanning.DerivativeClosure

namespace PallLean.Paper93.Direct

open MvPolynomial
open PallLean.Paper93
open PallLean.Paper93.Bridge
open PallLean.Paper93.Spanning
open PallLean.Paper93.Wiring
open SymmetricPowerBound (ConstraintType)

/-- **Agent M12 main theorem — transitionLeft iterated-derivative
membership.**

For every cookLevinQ-compilation parameter tuple
`(M, n, hn, htb, hns)` with `hn4 : n ≥ 4`, every per-instance
`transitionLeft`-factor parameterisation `(q, i, j)`, and every
derivative list `S : List (Fin n)`, there exists a canonical embedding
`σ : Fin 4 ↪ Fin n` along which

    iterDerivList S (transitionLeftAmbientFactor σ)

lies in the iterated derivative submodule of the concrete ambient
per-type space `concreteW n hn4 σ .transitionLeft`.

Here `transitionLeftAmbientFactor σ = X (σ 0) : MvPolynomial (Fin n) ℚ`
is Agent G3's ambient-level transitionLeft factor polynomial.

Proof recipe:
  (i)  Agent M11 (`transitionLeft_factor_direct_mem`) supplies a
       canonical embedding `σ` with
       `transitionLeftAmbientFactor σ ∈ concreteW n hn4 σ .transitionLeft`.
  (ii) Agent H4 (`iterDerivList_mem_iterDerivSubmodule`) transports
       this membership through `iterDerivList S _` into
       `iterDerivSubmodule (concreteW n hn4 σ .transitionLeft) S`.

The outer existential's witness is pinned to
`Classical.choose (transitionLeft_factor_direct_mem …)`, so the
iterated-derivative submodule literally agrees with the output of
step (i). This matches the pinning convention used in Agent M3's
`booleanity_shift_deriv_mem` and Agent M13's
`transitionLeft_shift_deriv_mem`.

The per-instance parameters `(q, i, j)` are retained in the public
signature for downstream chain compatibility with Agent M11
(`TransitionLeftDirect`). They are not used in the proof — the
transitionLeft factor polynomial at the ambient `Fin n` level depends
only on `σ` and the constraint type `.transitionLeft`, uniformly in
`(q, i, j)`. -/
theorem transitionLeft_iterDeriv_mem
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (q : Fin M.numStates) (i : Fin n) (j : Fin n) (hn4 : n ≥ 4)
    (S : List (Fin n)) :
    ∃ σ : Fin 4 ↪ Fin n,
      SPDP.iterDerivList S
          (transitionLeftAmbientFactor σ : MvPolynomial (Fin n) ℚ)
        ∈ PallLean.Paper93.Spanning.iterDerivSubmodule
            (concreteW n hn4
              (Classical.choose
                (transitionLeft_factor_direct_mem
                  M n hn htb hns q i j hn4))
              ConstraintType.transitionLeft) S := by
  classical
  -- Step 1 (Agent M11): pin σ to `Classical.choose` of the M11
  -- existential so that the outer submodule in the goal literally
  -- agrees with our witness.
  set σ : Fin 4 ↪ Fin n :=
      Classical.choose
        (transitionLeft_factor_direct_mem M n hn htb hns q i j hn4)
      with hσ_def
  have hfMem :
      (transitionLeftAmbientFactor σ : MvPolynomial (Fin n) ℚ)
        ∈ concreteW n hn4 σ ConstraintType.transitionLeft := by
    -- The `Classical.choose_spec` witness matches our pinned σ.
    have hspec :=
      Classical.choose_spec
        (transitionLeft_factor_direct_mem M n hn htb hns q i j hn4)
    simpa [σ, hσ_def] using hspec
  -- Step 2 (Agent H4): transport through `iterDerivList S _` into
  -- the iterated derivative submodule.
  have hDerivMem :
      SPDP.iterDerivList S
          (transitionLeftAmbientFactor σ : MvPolynomial (Fin n) ℚ)
        ∈ PallLean.Paper93.Spanning.iterDerivSubmodule
            (concreteW n hn4 σ ConstraintType.transitionLeft) S :=
    PallLean.Paper93.Spanning.iterDerivList_mem_iterDerivSubmodule
      (concreteW n hn4 σ ConstraintType.transitionLeft)
      (transitionLeftAmbientFactor σ) hfMem S
  -- Package the existential with the σ we fixed above.
  exact ⟨σ, hDerivMem⟩

-- Suppress unused-variable lints on the cookLevinQ-shape parameters
-- retained in the public signature for downstream chain compatibility.
attribute [nolint unusedArguments] transitionLeft_iterDeriv_mem

/-! ## Kernel-only axiom trace

The deliverable should depend only on
`[propext, Classical.choice, Quot.sound]`. -/

#print axioms transitionLeft_iterDeriv_mem

end PallLean.Paper93.Direct
