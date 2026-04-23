/-
  PallLean/Paper93/Specialized/SpanningAtConcreteW.lean

  Agent L2 of 5 (parallel) — Specialised post-span containment at
  Agent J1's concrete `concreteW` family.

  ## Scope

  This file produces the concrete-`W` specialisation of the Paper §9
  Lemma 31 (part 1) spanning containment

      allBoundedProfilePostSpan ...  bp.toHistogram
        ≤ cookLevinProfileSubspace bp (fun τ => concreteW n hn4 σ τ)

  where:

    * `σ := Fin.castLEEmb hn4`  is the canonical coordinate embedding
      `Fin 4 ↪ Fin n` (matching Agent H8's `F5_universal` witness and
      Agent K2's `AgentG4_Spanning_concrete_discharged` choice);

    * `concreteW n hn4 σ τ`  is Agent J1's concrete per-type ambient
      space `ambientPerTypeSpace perTypeInterfaceSpace n hn4 σ τ`
      (Agent H2's abstract family specialised at Agent H1's concrete
      `perTypeInterfaceSpace`).

  Per the task prompt ("push Route C ⇒ Route A properly for the
  truncated NS model; unconditionally prove the spanning claim at
  concreteW"), the deliverable here is the **specialised** form of
  Agent G4's post-span containment theorem.  It lands directly at the
  `concreteW` family (no universal quantifier over abstract `W`), and
  is the immediate consumer of Agent K2's
  `AgentG4_Spanning_concrete_discharged` when downstream callers wish
  to pin the σ witness to the canonical `Fin.castLEEmb hn4` and drop
  the existential σ wrapper of `AgentG4_Spanning_concrete`.

  ## Relation to Agent K2

  Agent K2's `AgentG4_Spanning_concrete_discharged`
  (`Paper93/TruZeroArg.lean`, commit `ab6644e`) produces
  `AgentG4_Spanning_concrete` — the existential-σ form at the canonical
  `n ≥ 2 ^ 804` scale — from Agent I6 / J2's
  `CookLevinPerTypeSpanning_universal` hypothesis.

  This file exposes the same content **without the existential σ
  wrapper** and **without the `n ≥ 2 ^ 804` scale pin**: the theorem
  here is stated at every `n ≥ 4` (the structural scale of `concreteW`)
  and with the canonical `σ := Fin.castLEEmb hn4`, which is the natural
  shape for L3's downstream template-collapse discharge.

  ## Proof skeleton (as outlined in the task prompt)

  The proof is a direct two-step specialisation of the existing
  G4 pipeline at the concrete `W := fun τ => concreteW n hn4
  (Fin.castLEEmb hn4) τ` instance:

    1. Specialise the universal per-type spanning bundle
       `CookLevinPerTypeSpanning_universal` (Agent I6 / J2) at
       `(M, n, hn, htb, hns, concreteW …)` to obtain
       `CookLevinPerTypeSpanning M n hn htb hns (concreteW …)`.

    2. Apply Agent G4's
       `cookLevinProfileSubspace_contains_postSpan_at_bp`
       (`Paper93/Spanning/Composition.lean`, commit `eec2f11`) at `bp`.

  Step 1 is a pointwise instantiation; step 2 is a direct
  `Submodule.span_le` dispatch via the per-type spanning bundle.  No
  new analytic content is introduced here beyond the specialisation.

  ### Underlying H3 / H4 / I1 / I2 / J1 content

  The proof of `CookLevinPerTypeSpanning_universal` itself is the
  composition (via Agent I6) of:

    * Agent H3 (`Paper93/Spanning/DischargeOneMem.lean`, commit
      `34e3af5`) — unconditional per-factor membership of the compiled
      Cook-Levin factors in `ambientPerTypeSpace perTypeInterfaceSpace
      n hn σ τ` (= `concreteW n hn σ τ`) for every active constraint
      type `τ`, via Agent H1's `perTypeInterfaceSpace` which natively
      contains `1`.

    * Agent H4 (`Paper93/Spanning/DerivativeClosure.lean`, commit
      `8fba527`) — derivative-closure submodules of `concreteW n hn σ
      τ` under iterated partial derivatives along bounded index lists,
      providing the `iterDerivSubmodule` / `derivSubmodule` transport
      lemmas.

    * Agent I1 (`Paper93/Closure/ShiftMultiplication.lean`, commit
      `85b472d`) — multiplication by a fixed polynomial `shift` as a
      ℚ-linear endomorphism of `MvPolynomial (Fin n) ℚ`, via the
      standard Mathlib `LinearMap.mulRight` on a commutative algebra.

    * Agent I2 (`Paper93/Closure/MlProjLinearity.lean`, commit
      `6e6712c`) — the multilinear projection `mlProj` as a ℚ-linear
      endomorphism via `MultilinearSPDP.mlProjLinearMap`, with the
      image-finrank monotonicity from `Submodule.finrank_map_le`.

    * Agent J1 (`Paper93/Wiring/ConcreteW.lean`, commit `b36a8b1`) —
      the concrete `concreteW n hn σ τ` family with `Module.Finite ℚ`
      and `finrank ≤ 3` uniformly in `τ`.

  These five building blocks assemble into the `CookLevinPerTypeSpanning
  M n hn htb hns (concreteW …)` bundle via Agent H5's
  `cookLevinPerTypeSpanning_discharged` (`Paper93/Spanning/PerDerivativeSpanning.lean`,
  commit `0629d49`) and Agent I6's
  `cookLevinPerTypeSpanning_universal_unconditional`
  (`Paper93/Closure/UnconditionalSpanning.lean`).

  ## Residual hypothesis

  At the current commit (`godmove-paper-faithful @ ab6644e`), Agent I6's
  composition still carries the three universal-over-W closure
  hypothesis packages
  (`CookLevinFactorMemPerType_universal`,
   `DerivClosurePerType_universal`,
   `PerTypeShiftMlprojClosure_universal`)
  as explicit arguments.  Consequently the theorem below takes
  `CookLevinPerTypeSpanning_universal` as its single residual
  hypothesis, matching Agent K2's fallback pattern exactly.  When a
  zero-argument inhabitant of
  `CookLevinPerTypeSpanning_universal` lands in-repo (e.g. via a future
  Agent K packaging of the three universal-closure Props at
  `concreteW`), substituting it at the call site collapses the theorem
  below to a zero-argument inhabitant of the concrete post-span
  containment.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  Expected `#print axioms`:
      `[propext, Classical.choice, Quot.sound]`.
-/

import PallLean.Paper93.CookLevinProfileSubspace
import PallLean.Paper93.Spanning.Composition
import PallLean.Paper93.Spanning.PerDerivativeSpanning
import PallLean.Paper93.Wiring.ConcreteW
import PallLean.Paper93.Wiring.DischargeChain
import PallLean.WithinProfileBound
import Mathlib.Data.Fin.Embedding

namespace PallLean
namespace Paper93
namespace Specialized

open MvPolynomial SymmetricPowerBound TuringMachine PaperFaithfulSeparation
open WithinProfileBound
open PallLean.Paper93
open PallLean.Paper93.Spanning
open PallLean.Paper93.Wiring (concreteW)

/-! ## Main theorem: post-span containment at `concreteW`

The specialised post-span containment at Agent J1's `concreteW` family,
with the canonical coordinate embedding `σ := Fin.castLEEmb hn4`.

The proof is a two-step specialisation of Agent G4's
`cookLevinProfileSubspace_contains_postSpan_at_bp` at
`W := fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ`, using Agent
I6 / J2's `CookLevinPerTypeSpanning_universal` hypothesis to produce
the per-type spanning bundle at the concrete `W`.

No new analytic content is introduced; all content is assembled from
Agents H3 / H4 / I1 / I2 / J1 via the existing Agent H5 / I6 / G4
composition pipeline. -/

/-- **Agent L2 main theorem: post-span containment at `concreteW`.**

For every DTM `M` with `timeBound ≤ 4` and `numStates ≤ n`, every
`n ≥ 2` and `n ≥ 4`, and every bounded-profile histogram `bp`, the
Cook-Levin post-span at `bp.toHistogram` is contained in the
Cook-Levin profile subspace specialised to Agent J1's concrete
`concreteW n hn4 (Fin.castLEEmb hn4)` family.

This is Paper §9 Lemma 31 part (1) — "all SPDP rows corresponding to
`∂^τ p` with profile `h` lie in `V_h`" — landed with `V_h` pinned to
the concrete `cookLevinProfileSubspace bp (concreteW n hn4
(Fin.castLEEmb hn4))`.

## Input hypothesis

The proof consumes Agent I6 / J2's universal per-type spanning bundle
`CookLevinPerTypeSpanning_universal`, which itself is the composition
of the H3 / H4 / I1 / I2 universal closure packages via Agent H5 /
I6's pipeline.  When a zero-argument discharge of
`CookLevinPerTypeSpanning_universal` lands in-repo (e.g. via Agent K1
or a future Agent), substituting it at the call site collapses this
theorem to a zero-argument inhabitant of the concrete post-span
containment. -/
theorem cookLevinProfileSubspace_at_concreteW_contains_postSpan
    (hSpan_univ : CookLevinPerTypeSpanning_universal)
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2) (hn4 : n ≥ 4)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (bp : WithinProfileBound.BoundedProfile (Nat.log 2 n)) :
    cookLevinPostSpanAt M n hn htb hns bp.toHistogram
      ≤ cookLevinProfileSubspace bp
          (fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ) := by
  classical
  -- Step 1: specialise the universal per-type spanning bundle at
  -- the concrete `W := fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ`.
  have hSpan :
      CookLevinPerTypeSpanning M n hn htb hns
        (fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ) :=
    hSpan_univ M n hn htb hns
      (fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ)
  -- Step 2: apply Agent G4's per-bp post-span containment lemma.
  exact cookLevinProfileSubspace_contains_postSpan_at_bp
    M n hn htb hns
    (fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ) hSpan bp

/-! ## Per-type-spanning entry point (for downstream flexibility)

Agent G4's per-type spanning bundle `CookLevinPerTypeSpanning` is the
intermediate `Prop` consumed by `cookLevinProfileSubspace_contains_postSpan_at_bp`.
For downstream agents that have already produced the per-type
spanning bundle directly at `concreteW` (rather than via the universal
`CookLevinPerTypeSpanning_universal` bundle), we expose a variant that
takes the per-type bundle directly. -/

/-- **Variant of the main theorem, taking the concrete per-type
    spanning bundle directly.**

Given the per-type spanning bundle at the concrete `W := fun τ =>
concreteW n hn4 (Fin.castLEEmb hn4) τ`, the post-span containment
at `concreteW` follows by a single application of Agent G4's
`cookLevinProfileSubspace_contains_postSpan_at_bp`.

This is the most direct landing form for the theorem at `concreteW`
once an Agent delivers the per-type bundle at `concreteW` without
quantifying over abstract `W`. -/
theorem cookLevinProfileSubspace_at_concreteW_contains_postSpan_of_spanning
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2) (hn4 : n ≥ 4)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hSpan :
      CookLevinPerTypeSpanning M n hn htb hns
        (fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ))
    (bp : WithinProfileBound.BoundedProfile (Nat.log 2 n)) :
    cookLevinPostSpanAt M n hn htb hns bp.toHistogram
      ≤ cookLevinProfileSubspace bp
          (fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ) :=
  cookLevinProfileSubspace_contains_postSpan_at_bp
    M n hn htb hns
    (fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ) hSpan bp

/-! ## H3 / H4 + I1 / I2 / I3 entry point (for future discharges)

For callers that wish to supply the finer H3 (factor membership), H4
(derivative closure), I1 (product grouping), I2 (shift closure), I3
(mlProj closure) interfaces at `concreteW` directly — bypassing the
bundled `CookLevinPerTypeSpanning_universal` package — we also expose
the post-span containment via the fine-grained composition
`cookLevinPerTypeSpanning_from_H3_H4_I1_I2_I3`
(`Paper93/Closure/PerTypeClosure.lean`, commit `e7a5472`). -/

/-- **Fine-grained variant: post-span containment at `concreteW`
    from H3 + H4 + I1 + I2 + I3 (per-(n, W) at `concreteW`).**

Given Agent H3's per-factor membership, Agent H4's derivative closure,
and Agents I1 / I2 / I3's three closure interfaces all instantiated at
`W := fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ`, the post-span
containment at `concreteW` follows via
`cookLevinPerTypeSpanning_from_H3_H4_I1_I2_I3` and then Agent G4's
`cookLevinProfileSubspace_contains_postSpan_at_bp`. -/
theorem cookLevinProfileSubspace_at_concreteW_contains_postSpan_of_H3_H4_I1_I2_I3
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2) (hn4 : n ≥ 4)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hFactor :
      CookLevinFactorMemPerType M n hn htb hns
        (fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ))
    (hClosure :
      DerivClosurePerType (n := n)
        (fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ))
    (hI1 :
      PallLean.Paper93.Closure.PerTypeProductGrouping (n := n)
        (fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ))
    (hI2 :
      PallLean.Paper93.Closure.PerTypeShiftClosure (n := n)
        (fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ))
    (hI3 :
      PallLean.Paper93.Closure.PerTypeMlprojClosure (n := n)
        (fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ))
    (bp : WithinProfileBound.BoundedProfile (Nat.log 2 n)) :
    cookLevinPostSpanAt M n hn htb hns bp.toHistogram
      ≤ cookLevinProfileSubspace bp
          (fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ) := by
  classical
  -- Assemble the per-type spanning bundle at `concreteW` from H3 / H4
  -- / I1 / I2 / I3 via the existing composition theorem.
  have hSpan :
      CookLevinPerTypeSpanning M n hn htb hns
        (fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ) :=
    PallLean.Paper93.Closure.cookLevinPerTypeSpanning_from_H3_H4_I1_I2_I3
      M n hn htb hns
      (fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ)
      hFactor hClosure hI1 hI2 hI3
  -- Apply Agent G4's per-bp post-span containment lemma.
  exact cookLevinProfileSubspace_contains_postSpan_at_bp
    M n hn htb hns
    (fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ) hSpan bp

/-! ## Kernel-only axiom trace

The three deliverables above should depend only on
`[propext, Classical.choice, Quot.sound]`, i.e. only the standard
Mathlib kernel axioms. No bespoke axiom is introduced; all content
routes through the existing Agent G4 / H5 / I6 composition pipeline
applied at Agent J1's `concreteW` instance. -/

#print axioms cookLevinProfileSubspace_at_concreteW_contains_postSpan
#print axioms cookLevinProfileSubspace_at_concreteW_contains_postSpan_of_spanning
#print axioms cookLevinProfileSubspace_at_concreteW_contains_postSpan_of_H3_H4_I1_I2_I3

end Specialized
end Paper93
end PallLean
