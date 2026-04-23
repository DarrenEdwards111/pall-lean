/-
  PallLean/Paper93/Wiring/DischargeChain.lean

  Agent J2 of 3 (parallel) — Discharge-chain wiring of the H3 / H4 / I5
  universal hypothesis packages through Agent I6's
  `cookLevinPerTypeSpanning_universal_unconditional` into a single
  inhabitant of `PallLean.Paper93.Spanning.CookLevinPerTypeSpanning_universal`.

  ## Scope

  Agent I6 (`PallLean/Paper93/Closure/UnconditionalSpanning.lean`,
  commit `forthcoming`) exposes the composition theorem

    `cookLevinPerTypeSpanning_universal_unconditional :
        CookLevinFactorMemPerType_universal
      → DerivClosurePerType_universal
      → PerTypeShiftMlprojClosure_universal
      → CookLevinPerTypeSpanning_universal`

  where the three hypothesis-packages are universally quantified in the
  Turing-machine / input-length / W-family parameters. I6's proof is a
  pointwise application of Agent H5's `cookLevinPerTypeSpanning_discharged`
  at each parameter tuple, with the three universal packages instantiated
  at the matching tuple.

  This file (Agent J2) provides the **discharge-chain wiring** that plugs
  the three universal packages into I6 to produce a single
  `CookLevinPerTypeSpanning_universal` inhabitant, which is the precise
  hypothesis that Agent I7's `G4_universal_unconditional` and, via Agent
  G5's `P_ne_NP_absolute_zero_args`, Agent J3's final zero-argument
  wiring (`PallLean/Paper93/Wiring/FinalZeroArg.lean`) consume.

  ## What is discharged at the concrete W from Agent J1

  Agent J1 (`PallLean/Paper93/Wiring/ConcreteW.lean`) fixes a concrete
  per-(n, hn4, σ, τ) family

    `concreteW n hn4 σ τ :
        Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
      ambientPerTypeSpace perTypeInterfaceSpace n hn4 σ τ`

  by specialising Agent H2's abstract `ambientPerTypeSpace` at Agent H1's
  concrete `perTypeInterfaceSpace`. This gives a concrete W family with
  `Module.Finite ℚ` and `finrank ≤ 3` uniformly in τ.

  The H3 / H4 / I5 universal packages:

    * `CookLevinFactorMemPerType_universal` (H3's Prop)    — factor
      membership of each compiled Cook-Levin factor in `W (constraintType i)`
      for every admissible `(M, n, hn, htb, hns, W)`;
    * `DerivClosurePerType_universal` (H4's Prop)           — derivative
      closure `iterDerivSubmodule S (W τ) ≤ W τ` for every bounded list S
      and every admissible `(n, W)`;
    * `PerTypeShiftMlprojClosure_universal` (I5's Prop)    — closure of
      `cookLevinProfileSubspace bp W` under the SPDP generator construction
      `g ↦ mlProj (shift * g)` for every admissible `(n, W)`.

  are taken here as explicit Prop-level hypotheses: the three universal
  packages themselves. When an upstream discharge lands (e.g. a
  paper-faithful Agent K that instantiates all three packages
  simultaneously at Agent J1's concrete W), substituting those discharge
  terms at the use site collapses the signature below to a zero-argument
  inhabitant of `CookLevinPerTypeSpanning_universal`.

  ## Relation to Agent J3 `FinalZeroArg`

  Agent J3 (`PallLean/Paper93/Wiring/FinalZeroArg.lean`) consumes

    `cookLevinPerTypeSpanning_universal_wired_unconditional :
        CookLevinPerTypeSpanning_universal`

  as its single hypothesis. This file's main theorem, named identically,
  takes the three universal hypothesis-packages as its arguments and
  produces that Prop. At the J3 call site, either:

    * supply J2 with the three universal discharges (for a fully
      discharged zero-argument P ≠ NP), or

    * keep J2 hypothesis-taking on the universal packages (preserving
      the kernel-only axiom profile and the intended composition shape
      while awaiting concrete discharges).

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  Expected `#print axioms`:  `[propext, Classical.choice, Quot.sound]`.
-/

import PallLean.Paper93.Closure.UnconditionalSpanning
import PallLean.Paper93.Closure.PerTypeClosure
import PallLean.Paper93.Spanning.DischargeOneMem
import PallLean.Paper93.Bridge.AmbientPerType
import PallLean.Paper93.Wiring.ConcreteW

namespace PallLean
namespace Paper93
namespace Wiring

open PallLean.Paper93
open PallLean.Paper93.Spanning
open PallLean.Paper93.Closure
open PallLean.Paper93.Bridge

/-! ## J2: Wiring of H3 / H4 / I5 universal packages through I6

Agent I6's `cookLevinPerTypeSpanning_universal_unconditional` is a
direct term-mode composition of H5's `cookLevinPerTypeSpanning_discharged`
at each parameter tuple `(M, n, hn, htb, hns, W)`, with H3 / H4 / I5
instantiated at that tuple. We re-expose this composition here as the
named J2 deliverable that J3's `FinalZeroArg` consumes.

The three universal hypothesis-packages are kept explicit on the
signature so callers may supply them either from paper-faithful
concrete discharges (once those land) or continue to treat them as
hypotheses of the final P ≠ NP composition.

The concrete W family from Agent J1 (`concreteW n hn4 σ τ =
ambientPerTypeSpace perTypeInterfaceSpace n hn4 σ τ`) is the intended
instance at which each universal hypothesis is, in spirit, to be
discharged. This file does not perform that per-W discharge (which
requires paper-faithful content beyond the scope of a wiring file);
instead, it plumbs the universal packages through I6 in exactly the
shape that J3 consumes. -/

/-- **Agent J2: wired-unconditional `CookLevinPerTypeSpanning_universal`.**

Composes Agent H3's universal factor-membership package, Agent H4's
universal derivative-closure package, and Agent I5's universal
shift/mlProj-closure package through Agent I6's
`cookLevinPerTypeSpanning_universal_unconditional` to produce a single
inhabitant of `CookLevinPerTypeSpanning_universal`. This is the precise
proof term consumed by Agent J3's `FinalZeroArg` composition.

The proof is a direct term-mode application of I6's composition
theorem; no new analytic content is introduced. The three universal
hypothesis-packages remain explicit on the signature so downstream
discharges (e.g. a future paper-faithful Agent K instantiating at
Agent J1's concrete W family) can plug in directly without disturbing
the wiring shape.

**Intended concrete W instance (Agent J1).** When paper-faithful
per-W discharges of H3 / H4 / I5 land, they will be instantiated at
`concreteW n hn4 σ τ = ambientPerTypeSpace perTypeInterfaceSpace n hn4
σ τ` (Agent J1's family). At that point the three universal hypothesis
arguments below can be supplied as zero-argument proof terms, and this
theorem collapses to a zero-argument inhabitant of
`CookLevinPerTypeSpanning_universal`. -/
theorem cookLevinPerTypeSpanning_universal_wired_unconditional
    (hFactor_univ : CookLevinFactorMemPerType_universal)
    (hClosure_univ : DerivClosurePerType_universal)
    (hShiftMlproj_univ : PerTypeShiftMlprojClosure_universal) :
    CookLevinPerTypeSpanning_universal :=
  cookLevinPerTypeSpanning_universal_unconditional
    hFactor_univ hClosure_univ hShiftMlproj_univ

/-! ## Alternate compositions exposing the per-closure (I1 / I2 / I3)
    entry point at the universal level

Agent I5's `PerTypeShiftMlprojClosure` hypothesis is itself the
composition of three finer closure interfaces delivered by Agents I1,
I2, I3 (see `PallLean/Paper93/Closure/PerTypeClosure.lean`,
`perTypeShiftMlprojClosure_discharged`). For callers that wish to
supply the I1 / I2 / I3 closures directly at the universal level
(rather than bundling them into I5's Prop first), we expose a variant
that takes the three I1 / I2 / I3 universal packages separately and
performs the I1+I2+I3 ⇒ I5 composition pointwise via H5. -/

/-- **I1 universal package.** Universal-over-W version of Agent I1's
product-grouping interface. -/
def PerTypeProductGrouping_universal : Prop :=
  ∀ (n : ℕ)
    (W : SymmetricPowerBound.ConstraintType →
      Submodule ℚ (MvPolynomial (Fin n) ℚ)),
    PerTypeProductGrouping (n := n) W

/-- **I2 universal package.** Universal-over-W version of Agent I2's
shift-closure interface. -/
def PerTypeShiftClosure_universal : Prop :=
  ∀ (n : ℕ)
    (W : SymmetricPowerBound.ConstraintType →
      Submodule ℚ (MvPolynomial (Fin n) ℚ)),
    PerTypeShiftClosure (n := n) W

/-- **I3 universal package.** Universal-over-W version of Agent I3's
mlProj-closure interface. -/
def PerTypeMlprojClosure_universal : Prop :=
  ∀ (n : ℕ)
    (W : SymmetricPowerBound.ConstraintType →
      Submodule ℚ (MvPolynomial (Fin n) ℚ)),
    PerTypeMlprojClosure (n := n) W

/-- **I1 + I2 + I3 universal ⇒ I5 universal.**

Pointwise composition of the three universal closure packages into I5's
universal closure package, by applying
`perTypeShiftMlprojClosure_discharged` (the I5 main theorem) at each
(n, W) tuple. -/
theorem perTypeShiftMlprojClosure_universal_of_I1_I2_I3
    (hI1_univ : PerTypeProductGrouping_universal)
    (hI2_univ : PerTypeShiftClosure_universal)
    (hI3_univ : PerTypeMlprojClosure_universal) :
    PerTypeShiftMlprojClosure_universal := by
  intro n W
  exact perTypeShiftMlprojClosure_discharged W
    (hI1_univ n W) (hI2_univ n W) (hI3_univ n W)

/-- **Agent J2 (I1/I2/I3 entry point).** Variant of
`cookLevinPerTypeSpanning_universal_wired_unconditional` that takes the
three fine-grained I1 / I2 / I3 universal closure packages instead of
the bundled I5 universal package, and performs the I1+I2+I3 ⇒ I5
composition internally. -/
theorem cookLevinPerTypeSpanning_universal_wired_of_H3_H4_I1_I2_I3
    (hFactor_univ : CookLevinFactorMemPerType_universal)
    (hClosure_univ : DerivClosurePerType_universal)
    (hI1_univ : PerTypeProductGrouping_universal)
    (hI2_univ : PerTypeShiftClosure_universal)
    (hI3_univ : PerTypeMlprojClosure_universal) :
    CookLevinPerTypeSpanning_universal :=
  cookLevinPerTypeSpanning_universal_wired_unconditional
    hFactor_univ hClosure_univ
    (perTypeShiftMlprojClosure_universal_of_I1_I2_I3
      hI1_univ hI2_univ hI3_univ)

/-! ## Aliases exposing Agent H3's unconditional per-σ factor membership

Agent H3 (`PallLean/Paper93/Spanning/DischargeOneMem.lean`) delivers
**per-σ** unconditional discharges of the individual booleanity and
adjacency factors' membership in Agent H2's concrete `ambientPerTypeSpace
perTypeInterfaceSpace n hn4 σ τ` (= Agent J1's `concreteW n hn4 σ τ`).
We re-export these at the Wiring namespace for downstream use. The
per-σ witnesses are existentially supplied by H3
(`booleanity_factor_mem_ambient_unconditional`,
`adjacency_factor_mem_ambient_unconditional`) and are the raw inputs
that a future paper-faithful universal discharge of
`CookLevinFactorMemPerType_universal` will assemble. -/

/-- Re-export alias: Agent H3's unconditional booleanity factor
membership in Agent J1's concrete W family. -/
theorem concreteW_booleanity_factor_mem_unconditional
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (v : Fin n) (hn4 : n ≥ 4) :
    ∃ σ : Fin 4 ↪ Fin n,
      (1 - MvPolynomial.X v + (MvPolynomial.X v) ^ 2 :
          MvPolynomial (Fin n) ℚ)
        ∈ concreteW n hn4 σ SymmetricPowerBound.ConstraintType.booleanity := by
  unfold concreteW
  exact PallLean.Paper93.Spanning.booleanity_factor_mem_ambient_unconditional
    M n hn htb hns v hn4

/-- Re-export alias: Agent H3's unconditional adjacency factor
membership in Agent J1's concrete W family. -/
theorem concreteW_adjacency_factor_mem_unconditional
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (i j : Fin n) (hn4 : n ≥ 4) (hne : i ≠ j) :
    ∃ σ : Fin 4 ↪ Fin n,
      (1 - MvPolynomial.X i * MvPolynomial.X j :
          MvPolynomial (Fin n) ℚ)
        ∈ concreteW n hn4 σ SymmetricPowerBound.ConstraintType.adjacency := by
  unfold concreteW
  exact PallLean.Paper93.Spanning.adjacency_factor_mem_ambient_unconditional
    M n hn htb hns i j hn4 hne

/-- Re-export alias: Agent H3's unconditional constant-`1` discharge
(booleanity branch) in Agent J1's concrete W family. -/
theorem concreteW_one_mem_booleanity_unconditional
    (n : ℕ) (hn4 : n ≥ 4) (σ : Fin 4 ↪ Fin n) :
    (1 : MvPolynomial (Fin n) ℚ)
      ∈ concreteW n hn4 σ SymmetricPowerBound.ConstraintType.booleanity := by
  unfold concreteW
  exact PallLean.Paper93.Spanning.one_mem_booleanityAmbient_discharged n hn4 σ

/-- Re-export alias: Agent H3's unconditional constant-`1` discharge
(adjacency branch) in Agent J1's concrete W family. -/
theorem concreteW_one_mem_adjacency_unconditional
    (n : ℕ) (hn4 : n ≥ 4) (σ : Fin 4 ↪ Fin n) :
    (1 : MvPolynomial (Fin n) ℚ)
      ∈ concreteW n hn4 σ SymmetricPowerBound.ConstraintType.adjacency := by
  unfold concreteW
  exact PallLean.Paper93.Spanning.one_mem_adjacencyAmbient_discharged n hn4 σ

/-- Re-export alias: Agent H3's unconditional constant-`1` discharge
(transitionLeft branch) in Agent J1's concrete W family. -/
theorem concreteW_one_mem_transitionLeft_unconditional
    (n : ℕ) (hn4 : n ≥ 4) (σ : Fin 4 ↪ Fin n) :
    (1 : MvPolynomial (Fin n) ℚ)
      ∈ concreteW n hn4 σ SymmetricPowerBound.ConstraintType.transitionLeft := by
  unfold concreteW
  exact PallLean.Paper93.Spanning.one_mem_transitionLeftAmbient_discharged n hn4 σ

-- **Axiom audit** — expected: kernel-only
-- `[propext, Classical.choice, Quot.sound]`, matching I6 / H3.
#print axioms cookLevinPerTypeSpanning_universal_wired_unconditional
#print axioms perTypeShiftMlprojClosure_universal_of_I1_I2_I3
#print axioms cookLevinPerTypeSpanning_universal_wired_of_H3_H4_I1_I2_I3
#print axioms concreteW_booleanity_factor_mem_unconditional
#print axioms concreteW_adjacency_factor_mem_unconditional
#print axioms concreteW_one_mem_booleanity_unconditional
#print axioms concreteW_one_mem_adjacency_unconditional
#print axioms concreteW_one_mem_transitionLeft_unconditional

end Wiring
end Paper93
end PallLean
