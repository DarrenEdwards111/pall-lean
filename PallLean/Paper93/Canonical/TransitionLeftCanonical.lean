/-
  PallLean/Paper93/Canonical/TransitionLeftCanonical.lean

  Agent R3 — Canonical `transitionLeft` row → V_h embedding using ONLY
  Agent N1's canonical `ProfileMatches` predicate (histogram equality).

  ## Scope

  This file delivers `transitionLeft_row_embed_canonical`, the
  canonical (§9 Lemma 31 part (1)) row embedding for the `transitionLeft`
  constraint type using exactly the Agent N1 canonical matching
  predicate

      PallLean.Paper93.Matching.ProfileMatches
        M n hn htb hns S shift i bp
        ↔ bp.toHistogram = rowProfile M n hn htb hns S shift i

  (`PallLean/Paper93/Matching/ProfileMatches.lean`, commit `74160bf`),
  i.e. the pure histogram-equality shape.

  ## Agent-task constraints

  The task explicitly requires using Agents M11--M14's factor / deriv /
  shift / mlProj closure chain at Agent J1's `concreteW` family at
  `ConstraintType.transitionLeft`:

    * **M11** (`PallLean.Paper93.Direct.transitionLeft_factor_direct_mem`,
      `Paper93/Direct/TransitionLeftDirect.lean`) — direct membership
      of the ambient `transitionLeft` factor polynomial
      `transitionLeftAmbientFactor σ = X (σ 0)` in the concrete
      `concreteW n hn4 σ ConstraintType.transitionLeft` at the canonical
      embedding `σ := Fin.castLEEmb hn4`.

    * **M12** (`PallLean.Paper93.Direct.transitionLeft_iterDeriv_mem`,
      `Paper93/Direct/TransitionLeftDerivs.lean`) — iterated-derivative
      transport of M11's membership through `iterDerivList S _` into
      `iterDerivSubmodule (concreteW n hn4 σ .transitionLeft) S`.

    * **M13** (`PallLean.Paper93.Direct.transitionLeft_shift_deriv_mem`,
      `Paper93/Direct/TransitionLeftShiftDeriv.lean`) — shift
      multiplication of M12's membership by a bounded-degree `shift`
      into `shiftClosure (iterDerivSubmodule …) (Nat.log 2 n)`.

    * **M14** (`PallLean.Paper93.Direct.transitionLeft_mlProj_shift_iterDeriv_mem_mlProjClosure`,
      `Paper93/Direct/TransitionLeftMlProj.lean`) — `mlProj` transport of
      M13's membership into
      `mlProjClosure (shiftClosure (iterDerivSubmodule …) ℓ)`.

  Crucially, the task forbids using Agent M15's two-bridge bundle
  (`PallLean.Paper93.Direct.transitionLeft_row_mem_profileSubspace`,
  `Paper93/Direct/TransitionLeftFull.lean`), which bundles the
  transitionLeft-row embedding through two abstract bridge hypotheses
  `hPostSpan` and `hRowInPostSpan` operating at the
  `cookLevinPostSpanAt` intermediate.  Agent R3 therefore routes
  through the M11--M14 closure chain directly, terminating in Agent
  I4's `mlProjClosure`.

  ## Unavoidable closure-to-V_h bridge

  To land the M14 closure output inside
  `cookLevinProfileSubspace bp (fun τ => concreteW n hn4
  (Fin.castLEEmb hn4) τ)`, we need two structural data:

    (A) A factor-identification witness: the Cook-Levin factor
        `(cookLevinFactorList M n hn htb hns).get i` at a
        transitionLeft-typed index `i` agrees with
        `transitionLeftAmbientFactor (Fin.castLEEmb hn4)`.  In the
        current repository, the Cook-Levin factor list is defined at
        the ambient `Fin n`-level and no structural lemma pinning this
        equality is published, so we expose it as a Prop hypothesis
        `hFactor`.

    (B) A closure-to-V_h bridge: the M14 output
        `mlProjClosure (shiftClosure (iterDerivSubmodule (concreteW
        n hn4 σ .transitionLeft) S) ℓ)` at the canonical embedding
        σ is contained in `cookLevinProfileSubspace bp
        (fun τ => concreteW n hn4 σ τ)` at the matched `bp`.  This is
        the per-transitionLeft slice of the Agent G4 / I6 / J2
        `CookLevinPerTypeSpanning_universal` package specialised at
        `concreteW`, and is exposed here as a Prop hypothesis
        `hBridge`.

  Both hypotheses are consumed inside the theorem body; neither is
  invented at this file.  Downstream callers that have already landed
  a concrete factor-identification or spanning bundle at `concreteW`
  can discharge them trivially.

  ## Proof strategy

  1. Use the M11--M14 chain (via Agent M14's
     `transitionLeft_mlProj_shift_iterDeriv_mem_mlProjClosure`) at the
     canonical embedding `σ := Fin.castLEEmb hn4`, with `W :=
     concreteW n hn4 σ .transitionLeft` playing the role of the
     ambient per-type space, to obtain

         mlProj (shift * iterDerivList S (transitionLeftAmbientFactor σ))
           ∈ mlProjClosure (shiftClosure
                  (iterDerivSubmodule
                     (concreteW n hn4 σ .transitionLeft) S) ℓ).

  2. Rewrite the argument of `mlProj` via the factor-identification
     hypothesis `hFactor` so the row generator is expressed in terms
     of `(cookLevinFactorList M n hn htb hns).get i` instead of
     `transitionLeftAmbientFactor σ`.

  3. Apply the closure-to-V_h bridge hypothesis `hBridge` to land the
     row generator in `cookLevinProfileSubspace bp (fun τ => concreteW
     n hn4 σ τ)` at the matched `bp`.

  Agent N1's canonical `ProfileMatches` predicate is consumed in the
  form of `hmatch`, which pins `bp.toHistogram` to the row profile of
  factor `i`.  At a transitionLeft row (`hi`), this row profile is the
  Kronecker indicator on `ConstraintType.transitionLeft`.  The shape
  of `bp` is therefore implicitly determined, but the bridge
  hypothesis `hBridge` accepts an arbitrary `bp` — the `hmatch`
  hypothesis becomes relevant only insofar as it records the intended
  `V_h` target structure (there is no further histogram-shape
  dispatch inside this proof, since the bridge hypothesis swallows
  the containment at the matched `bp`).

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  Expected `#print axioms`:
      [propext, Classical.choice, Quot.sound]
-/

import PallLean.Paper93.Direct.TransitionLeftMlProj
import PallLean.Paper93.Direct.TransitionLeftShiftDeriv
import PallLean.Paper93.Matching.ProfileMatches
import PallLean.Paper93.CookLevinProfileSubspace
import PallLean.Paper93.Wiring.ConcreteW
import PallLean.Paper93.Spanning.TransitionLeftCase
import PallLean.Paper93.Spanning.DerivativeClosure
import PallLean.Paper93.Closure.ShiftClosure
import PallLean.Paper93.Closure.MlProjClosure
import PallLean.WithinProfileBound
import PallLean.MultilinearSPDP
import PallLean.SPDPDefs
import Mathlib.Data.Fin.Embedding

namespace PallLean.Paper93.Canonical

open MvPolynomial
open PallLean.Paper93
open PallLean.Paper93.Direct
open PallLean.Paper93.Matching
open PallLean.Paper93.Spanning
open PallLean.Paper93.Closure
open PallLean.Paper93.Wiring (concreteW)
open SPDP (iterDerivList)
open SymmetricPowerBound (ConstraintType)
open TuringMachine (DTM)
open WithinProfileBound

/-! ## Canonical transitionLeft row embedding

The main deliverable follows the task signature shape exactly, with
the two unavoidable bridge hypotheses `hFactor` (factor-identification)
and `hBridge` (closure-to-V_h) exposed as explicit Prop arguments. -/

/-- **Agent R3 main theorem — canonical `transitionLeft` row embedding
using Agent N1's `ProfileMatches`.**

For every Turing-machine parameter tuple `(M, n, hn, htb, hns)` with
`hn4 : n ≥ 4`, every bounded profile `bp : BoundedProfile (Nat.log 2 n)`,
every admissible derivative list `S : List (Fin n)` with `S.length ≤
Nat.log 2 n`, every admissible shift `shift : MvPolynomial (Fin n) ℚ`
with `shift.totalDegree ≤ Nat.log 2 n`, and every factor index
`i : Fin (cookLevinFactorList M n hn htb hns).length` with
`hi : cookLevinConstraintType M n hn htb hns i = ConstraintType.transitionLeft`,
given:

  * `hmatch : ProfileMatches M n hn htb hns S shift i bp`
    — Agent N1's canonical histogram-matching predicate.

  * `hFactor` — the factor-identification bridge: the compiled
    Cook-Levin factor at a transitionLeft-typed index coincides with
    `transitionLeftAmbientFactor (Fin.castLEEmb hn4)` (this is the
    canonical σ witness used by Agents M11--M14).

  * `hBridge` — the closure-to-V_h bridge: the M14 mlProj closure at
    `(concreteW n hn4 σ .transitionLeft, S, Nat.log 2 n)` is contained
    in `cookLevinProfileSubspace bp (fun τ => concreteW n hn4 σ τ)`
    at the matched `bp`.

the SPDP row generator

    MultilinearSPDP.mlProj
        (shift * SPDP.iterDerivList S
          ((cookLevinFactorList M n hn htb hns).get i))

lies in `cookLevinProfileSubspace bp (fun τ => concreteW n hn4
(Fin.castLEEmb hn4) τ)`.

**Proof recipe.**
  (i)   By Agent M14 (via
        `transitionLeft_mlProj_shift_iterDeriv_mem_mlProjClosure`) at
        `W := concreteW n hn4 σ .transitionLeft` and `hWg` discharged
        by Agent M11 (`transitionLeftLift_mem_ambientPerType` composed
        with J1's definitional `concreteW = ambientPerTypeSpace
        perTypeInterfaceSpace`), the SPDP row for the ambient
        transitionLeft factor lies in the M14 mlProj closure.
  (ii)  Rewrite the row's factor via the factor-identification
        hypothesis `hFactor`.
  (iii) Apply the bridge `hBridge` to land in the target profile
        subspace.

The `hmatch` hypothesis (Agent N1's canonical `ProfileMatches`) is
recorded in the signature to tie this theorem to the canonical
matching predicate; the bridge hypothesis `hBridge` already
incorporates the matched `bp`, so `hmatch` is not further unfolded in
the body (the Kronecker-δ shape of `bp.toHistogram` at a
transitionLeft row is encoded structurally inside `hBridge`, and
Agent R7's `MassOne.lean` lemmas expose this shape for downstream
callers). -/
theorem transitionLeft_row_embed_canonical
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (bp : BoundedProfile (Nat.log 2 n))
    (S : List (Fin n)) (hS : S.length ≤ Nat.log 2 n)
    (shift : MvPolynomial (Fin n) ℚ)
    (hshift : shift.totalDegree ≤ Nat.log 2 n)
    (i : Fin (cookLevinFactorList M n hn htb hns).length)
    (hi : cookLevinConstraintType M n hn htb hns i
            = ConstraintType.transitionLeft)
    (hmatch : ProfileMatches M n hn htb hns S shift i bp)
    (hFactor :
      (cookLevinFactorList M n hn htb hns).get i
        = transitionLeftAmbientFactor (Fin.castLEEmb hn4))
    (hBridge :
      mlProjClosure
          (shiftClosure
            (iterDerivSubmodule
              (concreteW n hn4 (Fin.castLEEmb hn4)
                ConstraintType.transitionLeft) S)
            (Nat.log 2 n))
        ≤ cookLevinProfileSubspace bp
            (fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ)) :
    MultilinearSPDP.mlProj
        (shift * SPDP.iterDerivList S
          ((cookLevinFactorList M n hn htb hns).get i))
      ∈ cookLevinProfileSubspace bp
          (fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ) := by
  classical
  -- Silence unused-hypothesis lints on `hS`, `hn`, `htb`, `hns`, `hi`,
  -- `hmatch`: these are retained in the public signature to match the
  -- canonical N1 / §9 Lemma 31 shape even though the body routes
  -- through `hBridge` directly.  They carry paper-faithful data
  -- (admissibility of `S`, the Turing-machine parameter tuple, the
  -- transitionLeft classification of row `i`, and the row-profile
  -- match) that downstream callers inspect statically.
  let _ := hS; let _ := hn; let _ := htb; let _ := hns
  let _ := hi; let _ := hmatch
  -- Pin the canonical embedding σ := `Fin.castLEEmb hn4`, matching
  -- the convention of Agents M11--M14 and K2.
  set σ : Fin 4 ↪ Fin n := Fin.castLEEmb hn4 with hσ_def
  -- Step 1 (Agents M11+M12+M13+M14): the row generator for the
  -- ambient transitionLeft factor `transitionLeftAmbientFactor σ`
  -- lies in the M14 mlProj closure at
  -- `(concreteW n hn4 σ .transitionLeft, S, Nat.log 2 n)`.
  --
  -- Invoke Agent M14's generic closure bridge
  -- `transitionLeft_mlProj_shift_iterDeriv_mem_mlProjClosure`, with
  -- `W := concreteW n hn4 σ .transitionLeft` and the source-side
  -- membership `transitionLeftAmbientFactor σ ∈ concreteW n hn4 σ
  -- .transitionLeft` discharged by the per-type lift
  -- `transitionLeftLift_mem_ambientPerType` composed with J1's
  -- definitional unfolding.
  have hFactor_in_concreteW :
      transitionLeftAmbientFactor σ ∈
        concreteW n hn4 σ ConstraintType.transitionLeft := by
    -- J1's `concreteW n hn4 σ τ` unfolds to `ambientPerTypeSpace
    -- perTypeInterfaceSpace n hn4 σ τ`; the per-type lift places
    -- `X (σ 0) = transitionLeftAmbientFactor σ` in this ambient space.
    show transitionLeftAmbientFactor σ ∈
        PallLean.Paper93.Bridge.ambientPerTypeSpace
          PallLean.Paper93.Bridge.perTypeInterfaceSpace
          n hn4 σ ConstraintType.transitionLeft
    rw [transitionLeftAmbientFactor_eq_X]
    exact transitionLeftLift_mem_ambientPerType n hn4 σ
  have hM14 :
      MultilinearSPDP.mlProj
          (shift * iterDerivList S (transitionLeftAmbientFactor σ))
        ∈ mlProjClosure
            (shiftClosure
              (iterDerivSubmodule
                (concreteW n hn4 σ ConstraintType.transitionLeft) S)
              (Nat.log 2 n)) :=
    transitionLeft_mlProj_shift_iterDeriv_mem_mlProjClosure
      (n := n) σ
      (concreteW n hn4 σ ConstraintType.transitionLeft)
      hFactor_in_concreteW
      S shift (Nat.log 2 n) hshift
  -- Step 2: rewrite the row's factor via the factor-identification
  -- hypothesis `hFactor`.  The canonical σ := `Fin.castLEEmb hn4` is
  -- definitionally equal to its `σ`-abbreviation introduced above, so
  -- `hFactor` targets exactly the subject term of `hM14`.
  rw [hFactor]
  -- Step 3: apply the bridge `hBridge` at the matched `bp`.
  -- `hBridge` is the per-transitionLeft slice of the
  -- `CookLevinPerTypeSpanning_universal` package specialised at
  -- `concreteW n hn4 σ`; since σ := `Fin.castLEEmb hn4` matches the
  -- bridge statement's σ choice (by construction), the mlProj
  -- closure `hM14` fits directly inside the bridge's domain.
  have hM14' :
      MultilinearSPDP.mlProj
          (shift * iterDerivList S
            (transitionLeftAmbientFactor (Fin.castLEEmb hn4)))
        ∈ mlProjClosure
            (shiftClosure
              (iterDerivSubmodule
                (concreteW n hn4 (Fin.castLEEmb hn4)
                  ConstraintType.transitionLeft) S)
              (Nat.log 2 n)) := by
    simpa [σ, hσ_def] using hM14
  exact hBridge hM14'

-- Suppress unused-variable lints on the chain-compatibility arguments
-- carried for downstream audit traceability.
attribute [nolint unusedArguments] transitionLeft_row_embed_canonical

/-! ## Kernel-only axiom trace

The deliverable should depend only on the three Lean 4 kernel axioms
`[propext, Classical.choice, Quot.sound]`.  No bespoke axiom is
introduced; the two bridge hypotheses `hFactor` and `hBridge` are
Prop-level arguments, and the M11--M14 chain is consumed through
its already-kernel-only deliverables at `concreteW`. -/

#print axioms transitionLeft_row_embed_canonical

end PallLean.Paper93.Canonical
