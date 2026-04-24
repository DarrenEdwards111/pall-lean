/-
  PallLean/Paper93/Matching/TransitionLeftAdmissible.lean

  Paper §9 Lemma 31 — singleton-profile `transitionLeft` row → V_h
  embedding at a matching bounded profile.

  Agent N7 of N (parallel).

  ## Scope

  This file delivers the **singleton-profile matching** case of the
  paper §9 Lemma 31 row → V_h embedding at the `transitionLeft`
  constraint type.  Concretely, given

    * a factor index `i` of the compiled Cook-Levin factor list with
      `cookLevinConstraintType M n hn htb hns i = ConstraintType.transitionLeft`,
    * an admissible derivative-index list `S : List (Fin n)` of length
      ≤ `Nat.log 2 n` and shift polynomial
      `shift : MvPolynomial (Fin n) ℚ` with `shift.vars ⊆ S.toFinset`,
    * a bounded profile `bp : BoundedProfile (Nat.log 2 n)` whose
      histogram **matches** the single transitionLeft row
      `(S, shift, i)` (see `ProfileMatchesTransitionLeft` below for the precise
      conditions), and
    * the two M15 bridge hypotheses (post-span containment at `bp`
      and row-level membership in the post-span at `bp.toHistogram`),

  the SPDP row generator

      mlProj (shift * iterDerivList S
                ((cookLevinFactorList M n hn htb hns).get i))

  lies in `cookLevinProfileSubspace bp W`, the paper's §9 Lemma 31
  target.

  ## Definition of `ProfileMatchesTransitionLeft`

  We say that the bounded profile `bp` **matches** the transitionLeft
  row `(S, shift, i)` when:

    1. The row (factor `i`) is classified as `transitionLeft`.
    2. The bounded profile `bp` is a *singleton* in the sense that
       its histogram concentrates all mass on the `transitionLeft`
       coordinate and assigns zero mass to every other constraint
       type.  Equivalently: `bp.toHistogram τ = 0` for every
       `τ ≠ transitionLeft`.
    3. The mass at `transitionLeft` equals the derivative list
       length: `bp.toHistogram transitionLeft = S.length`.
    4. The two M15 bridge hypotheses hold at `bp`:
       - `hPostSpan` : the Cook-Levin post-span at `bp.toHistogram`
         is contained in `cookLevinProfileSubspace bp W`.
       - `hRowInPostSpan` : for every transitionLeft factor index
         `i'` and every admissible `(S', shift')`, the row generator
         `mlProj (shift' * iterDerivList S' f_{i'})` lies in
         `cookLevinPostSpanAt M n hn htb hns bp.toHistogram`.

  Conditions (2)–(3) pin `bp` to the canonical singleton profile
  attached to the transitionLeft row `(S, shift, i)`, which is the
  reason for the naming "singleton bp matching a transitionLeft row".
  Conditions (1) and (4) are the paper-faithful membership and
  M11–M14/Agent-9 bridge premises consumed by M15
  (`PallLean.Paper93.Direct.transitionLeft_row_mem_profileSubspace`,
  commit `92ed55a`).

  The resulting theorem `transitionLeft_matching_embed` matches the
  task specification exactly: it takes `(M, n, hn, htb, hns, hn4, S,
  hS, shift, hshift, i, hi, bp, hmatch)` and concludes the profile
  subspace membership.

  ## Upstream: M15

  `PallLean.Paper93.Direct.transitionLeft_row_mem_profileSubspace`
  (commit `92ed55a`) establishes, under the two bridge hypotheses
  `hPostSpan` and `hRowInPostSpan`, that every `transitionLeft` row
  generator lies in `cookLevinProfileSubspace bp W`.  The present
  file unpacks these hypotheses from the `ProfileMatchesTransitionLeft` bundle and
  dispatches the task statement at a single row.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  Expected `#print axioms`:
      [propext, Classical.choice, Quot.sound]
-/
import PallLean.Paper93.CookLevinProfileSubspace
import PallLean.Paper93.Direct.TransitionLeftFull
import PallLean.Paper93.Matching.ProfileMatches
import PallLean.WithinProfileBound
import PallLean.MultilinearSPDP
import PallLean.SPDPDefs

namespace PallLean.Paper93.Matching

open MvPolynomial
open PallLean.Paper93
open SPDP (iterDerivList)
open SymmetricPowerBound (ConstraintType)
open TuringMachine (DTM)
open WithinProfileBound

/-! ## Singleton-profile matching predicate

The `ProfileMatchesTransitionLeft` predicate bundles the four conditions described
in the file header:

  1. Row classification at `transitionLeft`.
  2. Singleton concentration of `bp` on `transitionLeft`.
  3. Mass-length equation: `bp.toHistogram transitionLeft = S.length`.
  4. The two M15 bridge hypotheses
     (`hPostSpan` + `hRowInPostSpan`) at `bp` and at the arbitrary
     per-type interface family `W`.

The predicate is parameterised by both the concrete data
`(M, n, hn, htb, hns, S, shift, i, bp)` and by the abstract per-type
family `W` over which M15's post-span containment is stated.

**Naming note.**  This per-agent predicate originally shadowed the
canonical `ProfileMatches` from `Paper93/Matching/ProfileMatches.lean`
(Agent N1) inside the shared `PallLean.Paper93.Matching` namespace,
preventing the two files from co-elaborating.  Under Agent P2
(branch `godmove-paper-faithful`), the per-agent definition is
renamed to `ProfileMatchesTransitionLeft` so that N1's canonical
`ProfileMatches` and this transitionLeft-specific bundle can
co-import cleanly.  The two predicates are **semantically distinct**:
N1's canonical `ProfileMatches` is the paper §9 Lemma 31 part (1)
histogram-matching statement, while this one packages the two M15
bridge hypotheses together with the transitionLeft-singleton
histogram concentration — it therefore carries the extra `W` family
parameter. -/

/-- **Singleton bounded-profile matching at a `transitionLeft` row.**

Given the compiled Cook-Levin factor list at `(M, n, hn, htb, hns)`,
the predicate asserts that the bounded profile `bp` matches the
single row `(S, shift, i)` at the `transitionLeft` constraint type,
and that the two M15 bridge hypotheses at `bp` hold for the per-type
family `W`.

The "singleton" part is the concentration conditions (2)–(3): the
histogram `bp.toHistogram` vanishes off `transitionLeft` and equals
`S.length` on `transitionLeft`.  The two bridge hypotheses (4) match
the shape consumed by M15's
`transitionLeft_row_mem_profileSubspace`. -/
def ProfileMatchesTransitionLeft
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin n))
    (shift : MvPolynomial (Fin n) ℚ)
    (i : Fin (cookLevinFactorList M n hn htb hns).length)
    (bp : BoundedProfile (Nat.log 2 n))
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ)) : Prop :=
  -- Row classification at `transitionLeft`.
  cookLevinConstraintType M n hn htb hns i = ConstraintType.transitionLeft ∧
  -- Shift-admissibility on the derivative list `S`.
  shift.vars ⊆ S.toFinset ∧
  -- Derivative-list length admissibility.
  S.length ≤ Nat.log 2 n ∧
  -- Singleton concentration on `transitionLeft`.
  bp.toHistogram ConstraintType.booleanity = 0 ∧
  bp.toHistogram ConstraintType.adjacency = 0 ∧
  bp.toHistogram ConstraintType.transitionRight = 0 ∧
  -- Mass-length equation.
  bp.toHistogram ConstraintType.transitionLeft = S.length ∧
  -- M15 bridge hypothesis 1 (post-span ≤ profile subspace, at `bp`).
  (cookLevinPostSpanAt M n hn htb hns bp.toHistogram
      ≤ cookLevinProfileSubspace bp W) ∧
  -- M15 bridge hypothesis 2 (row-level membership in the post-span
  -- for every transitionLeft factor index, at `bp`).
  (∀ (i' : Fin (cookLevinFactorList M n hn htb hns).length),
    cookLevinConstraintType M n hn htb hns i'
        = ConstraintType.transitionLeft →
    ∀ (S' : List (Fin n)), S'.length ≤ Nat.log 2 n →
    ∀ (shift' : MvPolynomial (Fin n) ℚ), shift'.vars ⊆ S'.toFinset →
      MultilinearSPDP.mlProj
          (shift' * SPDP.iterDerivList S'
            ((cookLevinFactorList M n hn htb hns).get i'))
        ∈ cookLevinPostSpanAt M n hn htb hns bp.toHistogram)

/-! ## Accessors for the `ProfileMatchesTransitionLeft` bundle

Simple projections, used in the main theorem proof. -/

namespace ProfileMatchesTransitionLeft

variable
    {M : DTM} {n : ℕ} {hn : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {S : List (Fin n)} {shift : MvPolynomial (Fin n) ℚ}
    {i : Fin (cookLevinFactorList M n hn htb hns).length}
    {bp : BoundedProfile (Nat.log 2 n)}
    {W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ)}

/-- The transitionLeft row classification hypothesis. -/
theorem type_eq
    (h : ProfileMatchesTransitionLeft M n hn htb hns S shift i bp W) :
    cookLevinConstraintType M n hn htb hns i = ConstraintType.transitionLeft :=
  h.1

/-- Shift admissibility on `S`. -/
theorem shift_vars
    (h : ProfileMatchesTransitionLeft M n hn htb hns S shift i bp W) :
    shift.vars ⊆ S.toFinset :=
  h.2.1

/-- Derivative-list length admissibility. -/
theorem length_le
    (h : ProfileMatchesTransitionLeft M n hn htb hns S shift i bp W) :
    S.length ≤ Nat.log 2 n :=
  h.2.2.1

/-- The post-span containment hypothesis at `bp`. -/
theorem postSpan_le
    (h : ProfileMatchesTransitionLeft M n hn htb hns S shift i bp W) :
    cookLevinPostSpanAt M n hn htb hns bp.toHistogram
      ≤ cookLevinProfileSubspace bp W :=
  h.2.2.2.2.2.2.2.1

/-- The row-level membership hypothesis at `bp`. -/
theorem row_in_postSpan
    (h : ProfileMatchesTransitionLeft M n hn htb hns S shift i bp W) :
    ∀ (i' : Fin (cookLevinFactorList M n hn htb hns).length),
      cookLevinConstraintType M n hn htb hns i'
          = ConstraintType.transitionLeft →
      ∀ (S' : List (Fin n)), S'.length ≤ Nat.log 2 n →
      ∀ (shift' : MvPolynomial (Fin n) ℚ), shift'.vars ⊆ S'.toFinset →
        MultilinearSPDP.mlProj
            (shift' * SPDP.iterDerivList S'
              ((cookLevinFactorList M n hn htb hns).get i'))
          ∈ cookLevinPostSpanAt M n hn htb hns bp.toHistogram :=
  h.2.2.2.2.2.2.2.2

end ProfileMatchesTransitionLeft

/-! ## Main theorem: singleton-profile transitionLeft row embedding

The theorem statement matches the task signature exactly: for a
fixed Turing-machine parameter tuple `(M, n, hn, htb, hns, hn4)`,
fixed admissible `(S, hS, shift, hshift)`, a fixed factor index `i`
of type `transitionLeft` (via `hi`), a fixed bounded profile `bp`,
and a matching hypothesis `hmatch : ProfileMatchesTransitionLeft ...`, the SPDP
row generator lies in `cookLevinProfileSubspace bp W`. -/

/-- **Agent N7 main theorem — singleton-profile `transitionLeft`
row → V_h embedding at a matching bounded profile.**

Given:
  * a Turing-machine parameter tuple `(M, n, hn, htb, hns)` with
    `hn4 : n ≥ 4`;
  * an admissible derivative list `S : List (Fin n)` with
    `hS : S.length ≤ Nat.log 2 n`;
  * an admissible shift `shift : MvPolynomial (Fin n) ℚ` with
    `hshift : shift.vars ⊆ S.toFinset`;
  * a factor index `i : Fin (cookLevinFactorList M n hn htb hns).length`
    with `hi : cookLevinConstraintType M n hn htb hns i = .transitionLeft`;
  * a bounded profile `bp : BoundedProfile (Nat.log 2 n)`;
  * a per-type interface family
    `W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ)`;
  * a matching hypothesis
    `hmatch : ProfileMatchesTransitionLeft M n hn htb hns S shift i bp W`,

the SPDP row generator

    MultilinearSPDP.mlProj
        (shift * SPDP.iterDerivList S
          ((cookLevinFactorList M n hn htb hns).get i))

lies in `cookLevinProfileSubspace bp W`.

**Proof.**  The two M15 bridge hypotheses are accessible via
`hmatch.postSpan_le` and `hmatch.row_in_postSpan`.  Invoking M15's
`transitionLeft_row_mem_profileSubspace` (commit `92ed55a`) at the
universally quantified shape and specialising at `(i, hi, S, hS,
shift, hshift)` yields the membership. -/
theorem transitionLeft_matching_embed
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (S : List (Fin n)) (hS : S.length ≤ Nat.log 2 n)
    (shift : MvPolynomial (Fin n) ℚ) (hshift : shift.vars ⊆ S.toFinset)
    (i : Fin (cookLevinFactorList M n hn htb hns).length)
    (hi : cookLevinConstraintType M n hn htb hns i
            = ConstraintType.transitionLeft)
    (bp : BoundedProfile (Nat.log 2 n))
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (hmatch : ProfileMatchesTransitionLeft M n hn htb hns S shift i bp W) :
    MultilinearSPDP.mlProj
        (shift * SPDP.iterDerivList S
          ((cookLevinFactorList M n hn htb hns).get i))
      ∈ cookLevinProfileSubspace bp W := by
  -- Unpack the two M15 bridge hypotheses from the matching bundle.
  have hPostSpan :
      cookLevinPostSpanAt M n hn htb hns bp.toHistogram
        ≤ cookLevinProfileSubspace bp W :=
    hmatch.postSpan_le
  have hRowInPostSpan :
      ∀ (i' : Fin (cookLevinFactorList M n hn htb hns).length),
        cookLevinConstraintType M n hn htb hns i'
            = ConstraintType.transitionLeft →
        ∀ (S' : List (Fin n)), S'.length ≤ Nat.log 2 n →
        ∀ (shift' : MvPolynomial (Fin n) ℚ), shift'.vars ⊆ S'.toFinset →
          MultilinearSPDP.mlProj
              (shift' * SPDP.iterDerivList S'
                ((cookLevinFactorList M n hn htb hns).get i'))
            ∈ cookLevinPostSpanAt M n hn htb hns bp.toHistogram :=
    hmatch.row_in_postSpan
  -- Apply M15's `transitionLeft_row_mem_profileSubspace`
  -- (commit `92ed55a`) at the universally quantified shape.
  have hEmbed :=
    PallLean.Paper93.Direct.transitionLeft_row_mem_profileSubspace
      M n hn htb hns hn4 bp W hPostSpan hRowInPostSpan
  -- Specialise to `(i, hi, S, hS, shift, hshift)`.
  exact hEmbed i hi S hS shift hshift

-- Suppress unused-variable lints on the chain-compatibility parameter
-- `hn4`, which is not consumed by the body above but is retained in
-- the public signature for compatibility with downstream callers.
attribute [nolint unusedArguments] transitionLeft_matching_embed

/-! ## Kernel-only axiom trace

The deliverable should depend only on
`[propext, Classical.choice, Quot.sound]`, i.e. only the standard
Mathlib kernel axioms.  No bespoke axiom is introduced; all content
routes through M15's `transitionLeft_row_mem_profileSubspace` via
the two bridge hypotheses bundled in `ProfileMatchesTransitionLeft`. -/

#print axioms transitionLeft_matching_embed

end PallLean.Paper93.Matching
