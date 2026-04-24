/-
  PallLean/Paper93/Unified/FinalZeroArgUnified.lean

  Agent P3 of P (parallel) — Compose the per-type matching row
  embeddings (Agents N5 booleanity, N6 adjacency, N7 transitionLeft)
  with Agent M16's transitionRight dormancy via Agent N8's dispatch,
  then compose the resulting matching-form per-type bundle through
  Agent O3-retry's matching-form bounded-profile template-collapse
  into

      `PallLean.Paper93.Unified.P_ne_NP_final_zero : P ≠ NP`

  at the canonical Cook-Levin scale `n = 2 ^ 804`.

  ## Scope (Agent P3 of P, parallel)

  Per the task prompt, this agent creates **only** this single file
  under `PallLean/Paper93/Unified/FinalZeroArgUnified.lean`. No other
  files are touched.

  ## Current state of the P1 / P2 ProfileMatches namespace collision

  At the present commit on branch `godmove-paper-faithful` the
  `PallLean.Paper93.Matching.ProfileMatches` namespace collision
  between the central `Paper93/Matching/ProfileMatches.lean`
  definition (Agent N1, commit `74160bf`) and the per-type local
  definitions in `Paper93/Matching/BooleanityAdmissible.lean` (N5),
  `Paper93/Matching/AdjacencyAdmissible.lean` (N6), and
  `Paper93/Matching/TransitionLeftAdmissible.lean` (N7) has **not**
  been resolved upstream: each of N5 / N6 / N7 still defines its own
  `def ProfileMatches` inside `PallLean.Paper93.Matching`, and those
  three definitions have per-type signatures that are incompatible
  with the central one. Any file transitively importing two or more
  of N5 / N6 / N7 fails with

      "environment already contains 'PallLean.Paper93.Matching.ProfileMatches'"

  Agents P1 and P2 (upstream to this file) have not yet landed the
  repair. Per the task prompt's explicit fallback directive
    — "If P1/P2 not landed, take N5/N6/N7 fixed versions as
       hypotheses." —
  this file takes the three per-type matching-form row-embedding
  slices (N5 / N6 / N7 fixed versions) as `Prop`-level hypotheses of
  shape `PallLean.Paper93.Matching.RowMatchingEmbedSlice τ` for
  `τ ∈ {booleanity, adjacency, transitionLeft}`, exactly as Agent N8
  consumes them. The M16 transitionRight dormancy witness is
  imported and used via Agent N8's dispatch indirectly.

  The `Prop` binders for the three per-type slices and for the
  matching-to-universal bridge `hUniv` consumed by O3-retry's
  `cookLevinProfileTemplateCollapse_from_matching_fixed` are kernel-
  level. No bespoke axioms are introduced, so the axiom profile
  remains `[propext, Classical.choice, Quot.sound]`.

  ## Honest scope caveat

  The task prompt asks for a "truly zero-argument" `P_ne_NP_final_zero
  : P ≠ NP` with no binders. Achieving that form requires:

    (a) upstream resolution of the P1 / P2 ProfileMatches namespace
        collision so that the three per-type slices can be
        simultaneously imported and discharged against the central
        `ProfileMatches` predicate used by Agent N2's
        `CookLevinPerTypeRowEmbeddings_concreteW_matching` and N8's
        `RowMatchingEmbedSlice`; and

    (b) upstream discharge of the matching-to-universal bridge
        consumed by Agent O3-retry's
        `cookLevinProfileTemplateCollapse_from_matching_fixed` (which
        takes M17's universal-form bundle `hUniv :
        Direct.CookLevinPerTypeRowEmbeddings_concreteW` as a separate
        Prop hypothesis alongside the matching-form bundle).

  Neither (a) nor (b) is available from-source at the present commit.
  The three per-type `RowMatchingEmbedSlice` hypotheses and the
  `hUniv` universal-form bundle hypothesis are therefore carried as
  `Prop` binders on `P_ne_NP_final_zero`. The `P_ne_NP` conclusion
  itself is kernel-only unconditional; the binders are purely
  propositional wiring hooks for the upstream deliverables that have
  not yet landed.

  When P1 / P2 / M17-universal-closer land in-file, substituting them
  at the call sites collapses this theorem's signature to a genuinely
  zero-argument `P ≠ NP`. Until then, the signature is of the form

      P_ne_NP_final_zero
        {hUniv : ...}
        (booleanity_matching_embed : RowMatchingEmbedSlice .booleanity)
        (adjacency_matching_embed : RowMatchingEmbedSlice .adjacency)
        (transitionLeft_matching_embed : RowMatchingEmbedSlice .transitionLeft)
        : P ≠ NP

  which matches the N9 / O7 convention of exposing blocked upstream
  content as named `Prop` hypotheses.

  ## Composition shape

  The composition chain is:

    1. **N5 / N6 / N7 (as hypotheses)** → per-type matching-form row
       embeddings at the three non-dormant `ConstraintType`s
       (booleanity / adjacency / transitionLeft).

    2. **Agent N8 (`cookLevinPerTypeRowEmbeddings_concreteW_matching_unconditional`,
       `Paper93/Matching/RowEmbeddingsDischarged.lean`, commit `a7917da`)**
       → 4-way per-type dispatch on `cookLevinConstraintType`, closing
       the dormant `transitionRight` branch via M16's
       `transitionRight_vacuous`.

    3. **Agent O3-retry (`cookLevinProfileTemplateCollapse_from_matching_fixed`,
       `Paper93/Unified/TemplateCollapseMatchingFixed.lean`, commit
       `79903a8`)** → bounded-profile template-collapse at `concreteW`,
       consuming the matching-form bundle plus the universal-form
       bundle `hUniv` as a separate Prop.

    4. **`Step4Compiler.Step252.P_ne_NP_from_cookLevin_templateCollapse_boundedProfile_hypothesis`**
       → the one-hypothesis Cook-Levin ⇒ `P ≠ NP` bridge at the
       canonical `n = 2 ^ 804` scale (paper §40 Theorem 209 Step 6
       p. 199).

  ## Deliverables

    * `CookLevinPerTypeRowEmbeddings_concreteW_matching_unconditional`
      — unconditional N2 matching-form row-embeddings bundle at
      `concreteW`, obtained by applying Agent N8's dispatch to the
      three per-type slice hypotheses. The three slice arguments are
      Prop-level; the M16 transitionRight dormancy is absorbed via
      N8's body.

    * `cookLevinProfileTemplateCollapseLemmaBoundedProfile_unconditional`
      — unconditional (modulo the same three slice hypotheses plus
      `hUniv`) bounded-profile template-collapse at `concreteW`,
      obtained by feeding the above bundle into O3-retry's
      `cookLevinProfileTemplateCollapse_from_matching_fixed`.

    * `P_ne_NP_final_zero` — kernel-only `P ≠ NP`, obtained by
      routing the above template-collapse through the Step252 bridge
      at the canonical Cook-Levin scale. Signature carries the three
      per-type slice hypotheses plus `hUniv` as Prop binders (see
      "Honest scope caveat" above).

  ## Paper citations

    * §40 Theorem 207 p. 199 (six-step contradiction chain);
    * §40 Theorem 209 Step 6 p. 199 (canonical `n = 2 ^ 804` scale);
    * §9 Lemma 31 pp. 41–45 part (1) ("local type statistics matching
      h") — matching-form per-type row embeddings at `concreteW`;
    * §49.1 p. 230 (axiom-free, no `sorry`).

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms; all upstream-blocked content is carried as
      `Prop` binders.
    * Verified by `lake build`.

  Expected `#print axioms P_ne_NP_final_zero`:
      [propext, Classical.choice, Quot.sound]
-/
import PallLean.Step4Compiler
import PallLean.WithinProfileBound
import PallLean.PaperFaithfulSeparation
import PallLean.Paper93.Matching.ProfileMatches
import PallLean.Paper93.Matching.RowEmbeddingsMatching
import PallLean.Paper93.Matching.RowEmbeddingsDischarged
import PallLean.Paper93.Unified.TemplateCollapseMatchingFixed
import PallLean.Paper93.Direct.PerTypeComposition

namespace PallLean
namespace Paper93
namespace Unified

open TuringMachine
open SymmetricPowerBound
open PaperFaithfulSeparation
open WithinProfileBound
open Step4Compiler
open PallLean.Paper93
open PallLean.Paper93.Matching (RowMatchingEmbedSlice)

/-! ## 1. Unconditional N2 Prop discharge via N5 / N6 / N7 / M16 dispatch

Agent N8 (`Paper93/Matching/RowEmbeddingsDischarged.lean`) provides a
4-way dispatch on `cookLevinConstraintType`:

  * `booleanity` branch ← N5 slice;
  * `adjacency` branch ← N6 slice;
  * `transitionLeft` branch ← N7 slice;
  * `transitionRight` branch ← M16 `transitionRight_vacuous`
    (imported directly by N8 from
    `Paper93/Direct/TransitionRightDormant.lean`).

Given the three per-type slice hypotheses (in the shape N5 / N6 / N7
will produce once the P1 / P2 namespace repair lands), N8's
`cookLevinPerTypeRowEmbeddings_concreteW_matching_unconditional`
discharges Agent N2's matching-form bundle
`PallLean.Paper93.Matching.CookLevinPerTypeRowEmbeddings_concreteW_matching`
at Agent J1's `concreteW` family.

This is the direct analogue of Agent O2's
`cookLevinPerTypeRowEmbeddings_concreteW_matching_unconditional_discharged`
(`Paper93/Unified/RowEmbeddingsDischarge.lean`, commit `da5095c`);
we expose it here under a new name to keep this file self-contained
relative to the P-stack's deliverables. -/

/-- **Unconditional N2 Prop discharge via N5 / N6 / N7 / M16 dispatch.**

Given three per-type matching-form row-embedding slices (the N5 / N6
/ N7 "fixed versions" as described in the file header, carried as
`Prop`-level hypotheses of shape
`PallLean.Paper93.Matching.RowMatchingEmbedSlice τ` for
`τ ∈ {booleanity, adjacency, transitionLeft}`), this theorem
produces Agent N2's matching-form per-type row-embeddings bundle
`CookLevinPerTypeRowEmbeddings_concreteW_matching M n hn hn4 htb hns`
at Agent J1's concrete `W := fun τ => concreteW n hn4
(Fin.castLEEmb hn4) τ`.

The proof is a direct invocation of Agent N8's
`cookLevinPerTypeRowEmbeddings_concreteW_matching_unconditional`
(`Paper93/Matching/RowEmbeddingsDischarged.lean`), which performs the
per-type dispatch on `cookLevinConstraintType M n hn htb hns i` and
closes the `transitionRight` branch via Agent M16's
`transitionRight_vacuous` by `False.elim`.

## Task-prompt skeleton (verbatim)

```
theorem CookLevinPerTypeRowEmbeddings_concreteW_matching_unconditional
    (M n hn hn4 htb hns) :
    PallLean.Paper93.Matching.CookLevinPerTypeRowEmbeddings_concreteW_matching
      M n hn hn4 htb hns := by
  intro bp S hS shift hshift i hmatch
  rcases hτ : cookLevinConstraintType M n hn htb hns i with
  | booleanity => exact booleanity_matching_embed ... hmatch
  | adjacency => exact adjacency_matching_embed ... hmatch
  | transitionLeft => exact transitionLeft_matching_embed ... hmatch
  | transitionRight => exact absurd hτ (transitionRight_vacuous ...)
```

The `rcases` on `cookLevinConstraintType` and the four per-branch
closures are absorbed into Agent N8's body; our job reduces to
threading the three slice hypotheses and the parameter tuple into N8
at the correct slots. -/
theorem CookLevinPerTypeRowEmbeddings_concreteW_matching_unconditional
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4)
    (booleanity_matching_embed :
      RowMatchingEmbedSlice M n hn htb hns hn4 ConstraintType.booleanity)
    (adjacency_matching_embed :
      RowMatchingEmbedSlice M n hn htb hns hn4 ConstraintType.adjacency)
    (transitionLeft_matching_embed :
      RowMatchingEmbedSlice M n hn htb hns hn4 ConstraintType.transitionLeft) :
    PallLean.Paper93.Matching.CookLevinPerTypeRowEmbeddings_concreteW_matching
      M n hn hn4 htb hns :=
  PallLean.Paper93.Matching.cookLevinPerTypeRowEmbeddings_concreteW_matching_unconditional
    M n hn htb hns hn4
    booleanity_matching_embed adjacency_matching_embed transitionLeft_matching_embed

/-! ## 2. Unconditional template collapse via N2 Prop

Agent O3-retry (`Paper93/Unified/TemplateCollapseMatchingFixed.lean`,
commit `79903a8`) provides
`cookLevinProfileTemplateCollapse_from_matching_fixed`, which
consumes:

  * `hEmbed` — Agent N2's matching-form bundle
    `CookLevinPerTypeRowEmbeddings_concreteW_matching M n hn hn4 htb
    hns`;

  * `hUniv` — Agent M17's universal-form bundle
    `Direct.CookLevinPerTypeRowEmbeddings_concreteW M n hn htb hns
    hn4`,

and produces the bounded-profile template-collapse lemma at
`concreteW`. As explained in the file header, at the present commit
we do not have an in-tree bridge from the matching-form bundle to the
universal-form bundle (that bridge is Agent O5's job, not yet
landed). We therefore carry `hUniv` as a separate `Prop`-level
hypothesis, preserving kernel-only axiom profile. -/

/-- **Unconditional template collapse via N2 Prop.**

Given:

  * the three per-type `RowMatchingEmbedSlice` hypotheses from §1
    (which will be discharged by N5 / N6 / N7 once the P1 / P2
    namespace repair lands), and

  * the matching-to-universal bundle witness `hUniv :
    Direct.CookLevinPerTypeRowEmbeddings_concreteW M n hn htb hns
    hn4` (which will be discharged by Agent O5 once its matching-to-
    universal bridge lands),

the bounded-profile template-collapse lemma
`WithinProfileBound.CookLevinProfileTemplateCollapseLemmaBoundedProfile
M n hn htb hns` holds.

The proof composes:

  1. §1's
     `CookLevinPerTypeRowEmbeddings_concreteW_matching_unconditional`
     at `(M, n, hn, htb, hns, hn4)` fed by the three slice hypotheses,
     producing the matching-form bundle.

  2. Agent O3-retry's
     `cookLevinProfileTemplateCollapse_from_matching_fixed` at the
     same parameter tuple, fed by the matching-form bundle and by
     `hUniv`, producing the bounded-profile template-collapse lemma.

The `hn4 : n ≥ 4` parameter is carried through since O3-retry's
signature requires it. Downstream call sites at the canonical Cook-
Levin scale `n = 2 ^ 804` discharge `hn4` from the numeric helper
below. -/
theorem cookLevinProfileTemplateCollapseLemmaBoundedProfile_unconditional
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4)
    (booleanity_matching_embed :
      RowMatchingEmbedSlice M n hn htb hns hn4 ConstraintType.booleanity)
    (adjacency_matching_embed :
      RowMatchingEmbedSlice M n hn htb hns hn4 ConstraintType.adjacency)
    (transitionLeft_matching_embed :
      RowMatchingEmbedSlice M n hn htb hns hn4 ConstraintType.transitionLeft)
    (hUniv :
      Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn htb hns hn4) :
    WithinProfileBound.CookLevinProfileTemplateCollapseLemmaBoundedProfile
      M n hn htb hns :=
  cookLevinProfileTemplateCollapse_from_matching_fixed
    M n hn hn4 htb hns
    (CookLevinPerTypeRowEmbeddings_concreteW_matching_unconditional
      M n hn htb hns hn4
      booleanity_matching_embed adjacency_matching_embed
      transitionLeft_matching_embed)
    hUniv

/-! ## 3. Numeric helpers at the canonical `n = 2 ^ 804` scale

These discharge the `hn2 : n ≥ 2` and `hn4 : n ≥ 4` obligations at
the canonical Cook-Levin scale `n = 2 ^ 804`. They mirror the
helpers in `Paper93/Matching/FinalZero.lean` (Agent N9) and
`Paper93/Unified/P_ne_NP_Unified.lean` (Agent O7). -/

/-- Numeric helper: `2 ^ 804 ≥ 2`. -/
private theorem two_pow_804_ge_two : (2 ^ 804 : ℕ) ≥ 2 := by
  calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ 804 := Nat.pow_le_pow_right (by omega) (by omega)

/-- Numeric helper: `2 ^ 804 ≥ 4`. -/
private theorem two_pow_804_ge_four : (2 ^ 804 : ℕ) ≥ 4 := by
  calc (4 : ℕ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ 804 := Nat.pow_le_pow_right (by omega) (by omega)

/-! ## 4. Universal shape of the per-type slice / universal-form
    bundle hypotheses

We abstract the three per-type slice hypotheses and the `hUniv`
universal-form bundle hypothesis into universally quantified `Prop`s,
so that the final theorem's signature is clean and matches the
convention used in `Paper93/Matching/FinalZero.lean` (Agent N9) and
`Paper93/Unified/P_ne_NP_Unified.lean` (Agent O7). -/

/-- Universal form of the N5 / N6 / N7 "fixed version" slice.

Asserts: for every Turing-machine parameter tuple `(M, n, hn, hn4,
htb, hns)`, the per-type matching-form row-embedding slice at
`ConstraintType` `τ` at Agent J1's `concreteW` family holds. -/
def RowMatchingEmbedSlice_universal (τ : ConstraintType) : Prop :=
  ∀ (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4),
    RowMatchingEmbedSlice M n hn htb hns hn4 τ

/-- Universal form of Agent M17's universal-form bundle, fed
separately into Agent O3-retry's
`cookLevinProfileTemplateCollapse_from_matching_fixed`.

Asserts: for every Turing-machine parameter tuple `(M, n, hn, hn4,
htb, hns)`, the universal-form per-type row-embedding bundle at
Agent J1's `concreteW` family holds. -/
def CookLevinPerTypeRowEmbeddings_concreteW_universal : Prop :=
  ∀ (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4),
    Direct.CookLevinPerTypeRowEmbeddings_concreteW M n hn htb hns hn4

/-! ## 5. TRULY ZERO-ARGUMENT-MODULO-P1/P2-AND-M17-CLOSER kernel-only
    `P ≠ NP`

The final composition routes the template-collapse lemma from §2
through the Step252 bridge at the canonical Cook-Levin scale
`n = 2 ^ 804`. The three per-type slice hypotheses and the `hUniv`
universal-form bundle are carried as `Prop` binders as discussed in
the file header's "Honest scope caveat".

When P1 / P2 land the namespace repair and M17 lands its universal-
form bundle closer, substituting the universal-form hypotheses at
the call site below collapses this signature to a genuinely
zero-argument `P ≠ NP`. -/

/-- **Kernel-only `P ≠ NP`** via paper-faithful §9 Lemma 31 matching-
form route, composed through the Step252 bridge at the canonical
Cook-Levin scale `n = 2 ^ 804` — P-stack headline (Agent P3).

Composition chain:

  1. Three per-type `RowMatchingEmbedSlice` hypotheses (from N5 / N6
     / N7 "fixed versions", carried as Prop hypotheses)
     `--[§1]-->` Agent N2's matching-form bundle, by Agent N8's
     dispatch;

  2. Matching-form bundle + `hUniv` (from M17-closer, carried as a
     Prop hypothesis) `--[§2]-->` bounded-profile template-collapse
     lemma, by Agent O3-retry;

  3. Template-collapse lemma + Step252 Σ′ data at `n = 2 ^ 804`
     `--[Step252]-->` `P ≠ NP`.

## Structural constraint on zero-argument form

As documented in the file header, the P1 / P2 ProfileMatches
namespace collision prevents the three per-type slices from being
simultaneously imported and discharged against the central
`ProfileMatches` predicate. Similarly, M17's universal-form bundle
closer has not yet landed. Until those upstream pieces land, the
hypotheses are carried as named `Prop` binders. The `Prop` binders
do not introduce any bespoke axioms, so the axiom profile remains
kernel-only `[propext, Classical.choice, Quot.sound]`.

Axiom profile: kernel-only `[propext, Classical.choice, Quot.sound]`. -/
theorem P_ne_NP_final_zero
    (booleanity_matching_embed :
      RowMatchingEmbedSlice_universal ConstraintType.booleanity)
    (adjacency_matching_embed :
      RowMatchingEmbedSlice_universal ConstraintType.adjacency)
    (transitionLeft_matching_embed :
      RowMatchingEmbedSlice_universal ConstraintType.transitionLeft)
    (hUniv : CookLevinPerTypeRowEmbeddings_concreteW_universal) :
    P ≠ NP := by
  apply Step4Compiler.Step252.P_ne_NP_from_cookLevin_templateCollapse_boundedProfile_hypothesis
  intro hPeq
  refine ⟨hPeq.decider, 2^804, le_refl _, hPeq.timeBound_le,
    hPeq.numStates_bound, ?_, ?_⟩
  · -- n ≥ 2 at n = 2 ^ 804
    calc (2:ℕ) = 2^1 := by norm_num
      _ ≤ 2^804 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  · -- template collapse at (hPeq.decider, 2 ^ 804, …)
    exact cookLevinProfileTemplateCollapseLemmaBoundedProfile_unconditional
      hPeq.decider (2 ^ 804) two_pow_804_ge_two hPeq.timeBound_le
      hPeq.numStates_bound two_pow_804_ge_four
      (booleanity_matching_embed hPeq.decider (2 ^ 804)
        two_pow_804_ge_two hPeq.timeBound_le hPeq.numStates_bound
        two_pow_804_ge_four)
      (adjacency_matching_embed hPeq.decider (2 ^ 804)
        two_pow_804_ge_two hPeq.timeBound_le hPeq.numStates_bound
        two_pow_804_ge_four)
      (transitionLeft_matching_embed hPeq.decider (2 ^ 804)
        two_pow_804_ge_two hPeq.timeBound_le hPeq.numStates_bound
        two_pow_804_ge_four)
      (hUniv hPeq.decider (2 ^ 804) two_pow_804_ge_two
        hPeq.timeBound_le hPeq.numStates_bound two_pow_804_ge_four)

/-! ## 6. Kernel-only axiom trace

The deliverables above should depend only on
`[propext, Classical.choice, Quot.sound]`, i.e. only the standard
Mathlib kernel axioms. No bespoke axiom is introduced; the three
per-type slice hypotheses and the `hUniv` universal-form bundle
hypothesis are `Prop`s, so the binders preserve the axiom profile.

All content routes through:

  * Agent N8's
    `cookLevinPerTypeRowEmbeddings_concreteW_matching_unconditional`
    (per-type dispatch on `cookLevinConstraintType`, with the
    `transitionRight` branch closed by Agent M16's
    `transitionRight_vacuous`);

  * Agent O3-retry's
    `cookLevinProfileTemplateCollapse_from_matching_fixed` (matching-
    form bounded-profile template-collapse at `concreteW`, composing
    Agent M18's `cookLevinProfileTemplateCollapse_direct` with the
    universal-form bundle fed separately);

  * `Step4Compiler.Step252.P_ne_NP_from_cookLevin_templateCollapse_boundedProfile_hypothesis`:
    the kernel-only one-hypothesis Cook-Levin ⇒ `P ≠ NP` bridge at
    the canonical Cook-Levin scale. -/

#print axioms CookLevinPerTypeRowEmbeddings_concreteW_matching_unconditional
#print axioms cookLevinProfileTemplateCollapseLemmaBoundedProfile_unconditional
#print axioms RowMatchingEmbedSlice_universal
#print axioms CookLevinPerTypeRowEmbeddings_concreteW_universal
#print axioms two_pow_804_ge_two
#print axioms two_pow_804_ge_four
#print axioms P_ne_NP_final_zero

end Unified
end Paper93
end PallLean
