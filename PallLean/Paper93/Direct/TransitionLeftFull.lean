/-
  PallLean/Paper93/Direct/TransitionLeftFull.lean

  Paper §9 Lemma 31 — Full `transitionLeft` row → `V_h` embedding
  (Route C ⇒ Route A at the transitionLeft case, truncated NS model
  analogue at the Cook-Levin side).

  Agent M15 of M (parallel).

  ## Scope

  This file delivers the `transitionLeft` case of the paper §9 Lemma 31
  "row → profile subspace" bridge. For every factor index `i` of the
  compiled Cook-Levin factor list whose canonical constraint type is
  `transitionLeft`, every derivative-index list `S : List (Fin n)` of
  length ≤ `Nat.log 2 n`, and every admissible shift polynomial
  `shift : MvPolynomial (Fin n) ℚ` with `shift.vars ⊆ S.toFinset`, the
  SPDP row generator

      mlProj (shift * iterDerivList S f_i)

  (where `f_i := (cookLevinFactorList M n hn htb hns).get i`) lies in
  the Cook-Levin profile subspace

      cookLevinProfileSubspace bp W

  for an arbitrary per-type interface family
  `W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ)` and a
  bounded profile `bp : BoundedProfile (Nat.log 2 n)`, *provided* the
  ambient containment

      cookLevinPostSpanAt M n hn htb hns bp.toHistogram
        ≤ cookLevinProfileSubspace bp W

  holds and the row generator is in the ambient `cookLevinPostSpanAt`
  envelope for the specified profile.  The two hypotheses are the
  exact shapes produced by:

    * Agents M11–M14 (parallel) — for each `transitionLeft` factor
      index, the row generator
      `mlProj (shift * iterDerivList S f_i)` lies in the Cook-Levin
      `allBoundedProfilePostSpan` at profile `bp.toHistogram` via
      the chain of derivative / shift / mlProj closures H3–I4 applied
      at the `transitionLeft` factor polynomial.

    * Agent 9 (`PallLean.Paper93.TensorDimBound`) composed with
      `cookLevinProfileSubspace_contains_postSpan_of_hypothesis`
      — `cookLevinPostSpanAt ... bp.toHistogram ≤
          cookLevinProfileSubspace bp W`.

  The kernel-only composition below is a direct transitivity dispatch:
  `mem + le ⇒ mem` via `Submodule.le.mem`. No new analytic content is
  introduced; all content routes through the two upstream hypotheses.

  ## Relation to other Direct / Spanning agents

  * Agents M1–M4 cover the `booleanity` case (per-factor membership,
    iterated-derivative transport, shift closure, mlProj closure) at
    the compiled Cook-Levin factor polynomial
    `1 - X_v + X_v^2`, landing at the ambient
    `concreteW n hn4 σ .booleanity`.

  * Agents M6–M8 cover the `adjacency` case at
    `1 - X_i * X_j`, landing at `concreteW n hn4 σ .adjacency`.

  * Agent M16 (`TransitionRightDormant.lean`) dispatches the dormant
    `transitionRight` case vacuously.

  This file (Agent M15) lands the `transitionLeft` row in the
  Cook-Levin profile subspace at an abstract `W`, parameterised by
  the bounded profile `bp` and the row-in-postSpan + postSpan-in-V_h
  hypotheses supplied by Agents M11–M14 and Agent 9.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  Expected `#print axioms`:
      [propext, Classical.choice, Quot.sound]
-/

import PallLean.Paper93.CookLevinProfileSubspace
import PallLean.WithinProfileBound
import PallLean.MultilinearSPDP
import PallLean.SPDPDefs

namespace PallLean.Paper93.Direct

open MvPolynomial
open PallLean.Paper93
open SPDP (iterDerivList)
open SymmetricPowerBound (ConstraintType)
open TuringMachine (DTM)
open WithinProfileBound

/-! ## The `transitionLeft` row → `V_h` embedding theorem

We state the embedding in its most general, parameterised form: the
theorem takes

  * the ambient containment hypothesis `hPostSpan` (Agent 9 / G4 side:
    `cookLevinPostSpanAt ... bp.toHistogram ≤ cookLevinProfileSubspace bp W`);

  * the row-level membership hypothesis `hRowInPostSpan` (Agents
    M11–M14 side: for every `transitionLeft` factor index `i`, the
    SPDP row generator `mlProj (shift * iterDerivList S f_i)` lies
    in the Cook-Levin post-span at `bp.toHistogram`, for every
    admissible `S`, `shift`).

and concludes that the row generator lies in the profile subspace at
`bp`, via transitivity `Submodule.le.mem`.

The two input hypotheses are the exact shapes that Agents M11–M14
(row-in-postSpan) and the Agent 9 / G4 pipeline
(postSpan-in-profileSubspace, e.g.
`cookLevinProfileSubspace_contains_postSpan_of_hypothesis`) produce;
see the file header for detailed provenance. -/

/-- **Agent M15 main theorem — `transitionLeft` row → `V_h` embedding.**

For every Turing-machine parameter tuple `(M, n, hn, htb, hns)` with
`hn4 : n ≥ 4`, every bounded profile `bp : BoundedProfile (Nat.log 2 n)`,
every per-type interface family
`W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ)`, and every
factor index `i` of the compiled Cook-Levin factor list whose canonical
constraint type is `ConstraintType.transitionLeft`, for every
admissible derivative list `S : List (Fin n)` of length ≤ `Nat.log 2 n`
and every admissible shift `shift : MvPolynomial (Fin n) ℚ` with
`shift.vars ⊆ S.toFinset`, the SPDP row generator

    MultilinearSPDP.mlProj
        (shift * MultilinearSPDP.iterDerivList S
                  ((cookLevinFactorList M n hn htb hns).get i))

lies in `cookLevinProfileSubspace bp W`.

**Proof recipe.**  By hypothesis `hRowInPostSpan`, the row generator
lies in `cookLevinPostSpanAt M n hn htb hns bp.toHistogram`. By
hypothesis `hPostSpan`, the post-span at `bp.toHistogram` is contained
in `cookLevinProfileSubspace bp W`. Transitivity via `SetLike` gives
the membership in `cookLevinProfileSubspace bp W`.

**Hypothesis provenance.**

  * `hPostSpan` is the Cook-Levin side of the Route C ⇒ Route A
    implication: Agent 9's `profileSubspace_finrank_bound` composed
    with the per-type spanning pipeline (Agents G4 / H3 / H4 / I1 /
    I2 / I3) transported through
    `cookLevinProfileSubspace_contains_postSpan_of_hypothesis`
    delivers this containment at an arbitrary choice of per-type
    interface family `W`.

  * `hRowInPostSpan` is the row-level membership at the
    `transitionLeft` case; Agents M11–M14 (parallel) deliver it by
    composing the H3 (per-factor membership), H4 (derivative closure),
    I1 (shift multiplication), I3 (shift closure), and I4 (mlProj
    closure) primitives at the compiled Cook-Levin `transitionLeft`
    factor polynomial.

All content routes through the two abstract hypotheses; no new
analytic content is introduced at M15. -/
theorem transitionLeft_row_mem_profileSubspace
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (bp : BoundedProfile (Nat.log 2 n))
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (hPostSpan :
      cookLevinPostSpanAt M n hn htb hns bp.toHistogram
        ≤ cookLevinProfileSubspace bp W)
    (hRowInPostSpan :
      ∀ (i : Fin (cookLevinFactorList M n hn htb hns).length),
        cookLevinConstraintType M n hn htb hns i
            = ConstraintType.transitionLeft →
          ∀ (S : List (Fin n)) (_hS : S.length ≤ Nat.log 2 n)
            (shift : MvPolynomial (Fin n) ℚ)
            (_hshift : shift.vars ⊆ S.toFinset),
              MultilinearSPDP.mlProj
                  (shift * SPDP.iterDerivList S
                    ((cookLevinFactorList M n hn htb hns).get i))
                ∈ cookLevinPostSpanAt M n hn htb hns bp.toHistogram) :
    ∀ (i : Fin (cookLevinFactorList M n hn htb hns).length),
      cookLevinConstraintType M n hn htb hns i
          = ConstraintType.transitionLeft →
        ∀ (S : List (Fin n)) (_hS : S.length ≤ Nat.log 2 n)
          (shift : MvPolynomial (Fin n) ℚ)
          (_hshift : shift.vars ⊆ S.toFinset),
            MultilinearSPDP.mlProj
                (shift * SPDP.iterDerivList S
                  ((cookLevinFactorList M n hn htb hns).get i))
              ∈ cookLevinProfileSubspace bp W := by
  -- `hn4` is part of the standard parameter tuple used by the
  -- parallel Direct agents and is retained for downstream chain
  -- compatibility; the transitivity proof below does not consume it
  -- directly, as the `cookLevinProfileSubspace` and `cookLevinPostSpanAt`
  -- spaces are defined at the general `n ≥ 2` hypothesis.
  let _ := hn4
  -- Dispatch the universally quantified statement and apply
  -- transitivity on each row.
  intro i hType S hS shift hshift
  -- Step 1 (Agents M11–M14): the row generator lies in
  -- `cookLevinPostSpanAt M n hn htb hns bp.toHistogram`.
  have hRow :
      MultilinearSPDP.mlProj
          (shift * SPDP.iterDerivList S
            ((cookLevinFactorList M n hn htb hns).get i))
        ∈ cookLevinPostSpanAt M n hn htb hns bp.toHistogram :=
    hRowInPostSpan i hType S hS shift hshift
  -- Step 2 (Agent 9 + G4 via `hPostSpan`): the post-span at
  -- `bp.toHistogram` is contained in `cookLevinProfileSubspace bp W`.
  -- Transitivity of `∈` and `≤` on submodules dispatches the goal.
  exact hPostSpan hRow

-- Suppress unused-variable lints on the cookLevinQ-shape parameters
-- `hn4` and on the bounded-profile admissibility parameters retained
-- in the public signature for downstream chain compatibility.
attribute [nolint unusedArguments] transitionLeft_row_mem_profileSubspace

/-! ## Kernel-only axiom trace

The deliverable should depend only on
`[propext, Classical.choice, Quot.sound]`, i.e. only the standard
Mathlib kernel axioms. No bespoke axiom is introduced; all content
routes through the two abstract hypotheses supplied by Agents
M11–M14 + Agent 9. -/

#print axioms transitionLeft_row_mem_profileSubspace

end PallLean.Paper93.Direct
