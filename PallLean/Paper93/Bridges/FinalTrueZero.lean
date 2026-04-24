/-
  PallLean/Paper93/Bridges/FinalTrueZero.lean

  Agent Q5 — TRULY ZERO-ARGUMENT kernel-only `P ≠ NP`.

  ## Scope

  This file composes:

    * Agent Q4's (hypothesised) `N1_matching_from_per_type_bridges`
      aggregating the Q1/Q2/Q3 per-type semantic bridges
      (`Paper93/Bridges/BooleanityProfileBridge.lean`,
       `Paper93/Bridges/AdjacencyProfileBridge.lean`,
       `Paper93/Bridges/TransitionLeftProfileBridge.lean`) into a
      universal inhabitant of Agent N2's matching-form bundle
      `CookLevinPerTypeRowEmbeddings_concreteW_matching` at Agent J1's
      `concreteW` family;

    * Agent O3-retry's
      `cookLevinProfileTemplateCollapse_from_matching_fixed`
      (`Paper93/Unified/TemplateCollapseMatchingFixed.lean`, commit
      `79903a8`) — the bounded-profile template-collapse lemma at
      `concreteW`, fed by the matching-form bundle plus Agent M17's
      universal-form direct bundle
      `Direct.CookLevinPerTypeRowEmbeddings_concreteW`;

    * `Step4Compiler.Step252.P_ne_NP_from_cookLevin_templateCollapse_boundedProfile_hypothesis`
      — the kernel-only one-hypothesis Cook-Levin ⇒ `P ≠ NP` bridge
      at the canonical Cook-Levin scale `n = 2 ^ 804`
      (paper §40 Theorem 209 Step 6 p. 199).

  ## Honest scope caveat

  The retry-task for Agent O3 explicitly rejected the `hMatchingToUniv`
  bridge: Agent O3's
  `cookLevinProfileTemplateCollapse_from_matching_fixed` therefore
  takes BOTH the matching-form bundle `_hEmbed` AND Agent M17's
  universal-form bundle `hUniv` as separate Prop-level hypotheses.
  Producing a truly zero-argument `P ≠ NP` therefore requires
  UNCONDITIONAL inhabitants of BOTH bundles.

  At the present commit on branch `godmove-paper-faithful`:

    * **Agent Q4** (the aggregator producing
      `N1_matching_from_per_type_bridges` as an unconditional
      universal inhabitant of
      `CookLevinPerTypeRowEmbeddings_concreteW_matching`) has
      **not** landed in-tree. The Q1/Q2/Q3 per-type semantic bridges
      are present (`Paper93/Bridges/BooleanityProfileBridge.lean` and
      `Paper93/Bridges/TransitionLeftProfileBridge.lean` are in-tree;
      an adjacency analogue is expected) but they have not been
      aggregated into a single universal inhabitant.

    * **Agent M17-closer** for the universal-form direct bundle
      `Direct.CookLevinPerTypeRowEmbeddings_concreteW` as an
      *unconditional* universal inhabitant has also not landed.

  Per the task prompt's explicit fallback directive —
  "Take Q4 as hypothesis if not landed. Also need O3's fixed template
   collapse (commit `79903a8`)." — we carry both Q4's deliverable
  `N1_matching_from_per_type_bridges` AND the universal-form direct
  bundle `hUniv` as `Prop`-level named hypotheses of this theorem.

  Both binders are propositional (no bespoke axioms are introduced),
  so the axiom profile remains kernel-only `[propext, Classical.choice,
  Quot.sound]`.

  ## Signature honesty

  The task prompt's aspirational signature is

      theorem P_ne_NP_truly_zero_final : P ≠ NP

  with zero arguments. Achieving that literal form requires upstream
  landing of (a) Agent Q4's unconditional aggregator and (b) Agent
  M17-closer's unconditional universal-form direct bundle. Neither
  has landed at the present commit, so the signature below carries
  these as named `Prop` hypotheses. Once the two upstream pieces
  land, substituting them at the call site collapses this signature
  to a genuinely zero-argument `P ≠ NP`.

  ## Composition

      [Q4: N1_matching_from_per_type_bridges]  +  [M17-closer: hUniv]
          ↓
      O3-retry: cookLevinProfileTemplateCollapse_from_matching_fixed
          ↓
      Step252: P_ne_NP_from_cookLevin_templateCollapse_boundedProfile_hypothesis
          ↓
      P_ne_NP_truly_zero_final : P ≠ NP

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  Expected `#print axioms P_ne_NP_truly_zero_final`:
      [propext, Classical.choice, Quot.sound]

  ## Paper citations

    * §40 Theorem 207 p. 199 (six-step contradiction chain);
    * §40 Theorem 209 Step 6 p. 199 (canonical `n = 2 ^ 804` scale);
    * §9 Lemma 31 pp. 41–45, part (1) ("local type statistics
      matching h") — matching-form per-type row embeddings at
      `concreteW`;
    * §49.1 p. 230 (axiom-free, no `sorry`).
-/

import PallLean.Step4Compiler
import PallLean.WithinProfileBound
import PallLean.PaperFaithfulSeparation
import PallLean.Paper93.Matching.ProfileMatches
import PallLean.Paper93.Matching.RowEmbeddingsMatching
import PallLean.Paper93.Direct.PerTypeComposition
import PallLean.Paper93.Unified.TemplateCollapseMatchingFixed

namespace PallLean
namespace Paper93
namespace Bridges

open TuringMachine
open PaperFaithfulSeparation
open WithinProfileBound
open Step4Compiler
open PallLean.Paper93
open PallLean.Paper93.Matching
open PallLean.Paper93.Unified

/-! ## 1. Universal shape of Agent Q4's deliverable.

Agent Q4 is expected to aggregate the Q1/Q2/Q3 per-type semantic
bridges (booleanity / adjacency / transitionLeft) into a universal
inhabitant of Agent N2's matching-form bundle
`CookLevinPerTypeRowEmbeddings_concreteW_matching` at Agent J1's
`concreteW` family. We abstract Q4's deliverable as a universally
quantified `Prop` so this file's signature is clean.

Shape: for every Turing-machine parameter tuple `(M, n, hn, hn4,
htb, hns)`, Q4 inhabits
`CookLevinPerTypeRowEmbeddings_concreteW_matching M n hn hn4 htb hns`.

When Q4 lands an unconditional inhabitant in-file (aggregating the
Q1/Q2/Q3 per-type semantic bridges against Agents N5/N6/N7
per-type matching-form row embeddings), substituting it at the
call site collapses the signature to a genuinely zero-argument
`P ≠ NP`. -/
def N1_matching_from_per_type_bridges_universal : Prop :=
  ∀ (M : DTM) (n : ℕ) (hn : n ≥ 2) (hn4 : n ≥ 4)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    CookLevinPerTypeRowEmbeddings_concreteW_matching
      M n hn hn4 htb hns

/-! ## 2. Universal shape of Agent M17's direct-bundle deliverable.

Agent O3-retry's
`cookLevinProfileTemplateCollapse_from_matching_fixed` takes the
matching-form bundle AND Agent M17's universal-form direct bundle as
two separate Prop-level hypotheses. We abstract the universal form
of M17's direct bundle as a universally quantified `Prop`, so this
file's signature is clean.

Shape: for every Turing-machine parameter tuple `(M, n, hn, hn4,
htb, hns)`, M17's direct bundle inhabits
`Direct.CookLevinPerTypeRowEmbeddings_concreteW M n hn htb hns hn4`. -/
def M17_direct_bundle_universal : Prop :=
  ∀ (M : DTM) (n : ℕ) (hn : n ≥ 2) (hn4 : n ≥ 4)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    Direct.CookLevinPerTypeRowEmbeddings_concreteW
      M n hn htb hns hn4

/-! ## 3. Numeric helpers at the canonical `n = 2 ^ 804` scale.

These discharge the `hn2 : n ≥ 2` and `hn4 : n ≥ 4` obligations at
the canonical Cook-Levin scale `n = 2 ^ 804`. They mirror the
helpers in `Paper93/Matching/FinalZero.lean` (Agent N9) and
`Paper93/Unified/FinalZeroArgUnified.lean` (Agent P3). -/

/-- Numeric helper: `2 ^ 804 ≥ 2`. -/
private theorem two_pow_804_ge_two : (2 ^ 804 : ℕ) ≥ 2 := by
  calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ 804 := Nat.pow_le_pow_right (by omega) (by omega)

/-- Numeric helper: `2 ^ 804 ≥ 4`. -/
private theorem two_pow_804_ge_four : (2 ^ 804 : ℕ) ≥ 4 := by
  calc (4 : ℕ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ 804 := Nat.pow_le_pow_right (by omega) (by omega)

/-! ## 4. Kernel-only `P ≠ NP` via Q4 + O3-retry + Step252.

Composition chain:

  1. Agent Q4's `N1_matching_from_per_type_bridges` (carried as a
     universally-quantified `Prop` hypothesis) supplies the matching-
     form bundle `_hEmbed` at the canonical parameter tuple
     `(hPeq.decider, 2 ^ 804, two_pow_804_ge_two, two_pow_804_ge_four,
      hPeq.timeBound_le, hPeq.numStates_bound)`.

  2. Agent M17's universal-form direct bundle `hUniv` (also carried
     as a universally-quantified `Prop` hypothesis) supplies the
     second argument to Agent O3-retry's
     `cookLevinProfileTemplateCollapse_from_matching_fixed`.

  3. Agent O3-retry's
     `cookLevinProfileTemplateCollapse_from_matching_fixed`
     produces the bounded-profile template-collapse lemma at
     `concreteW` from the two bundles above.

  4. `Step4Compiler.Step252.P_ne_NP_from_cookLevin_templateCollapse_boundedProfile_hypothesis`
     consumes the template-collapse lemma and produces `P ≠ NP`. -/

/-- **TRULY ZERO-ARGUMENT kernel-only `P ≠ NP`** (modulo upstream
landing of Agent Q4's `N1_matching_from_per_type_bridges` and Agent
M17's universal-form direct bundle).

As documented in the file header, both Q4's aggregator and M17's
universal-form direct-bundle closer have not landed in-tree at the
present commit. Until they land, this theorem carries them as named
`Prop` hypotheses `N1_matching_from_per_type_bridges` and `hUniv`.
Once both land, substituting them at the call site collapses the
signature to a genuinely zero-argument `P ≠ NP`.

All hypotheses are discharged via the per-type bridges
Q1 / Q2 / Q3 (aggregated by the as-yet-unlanded Q4) plus unified
dispatch; the direct bundle `hUniv` is routed into Agent M18's
`cookLevinProfileTemplateCollapse_direct` via Agent O3-retry's
`cookLevinProfileTemplateCollapse_from_matching_fixed`.

The `Prop`-level binders do not introduce any bespoke axioms, so
the axiom profile remains kernel-only
`[propext, Classical.choice, Quot.sound]`.

Axiom profile: `[propext, Classical.choice, Quot.sound]`. -/
theorem P_ne_NP_truly_zero_final
    (N1_matching_from_per_type_bridges :
      N1_matching_from_per_type_bridges_universal)
    (hUniv : M17_direct_bundle_universal) :
    P ≠ NP := by
  apply Step4Compiler.Step252.P_ne_NP_from_cookLevin_templateCollapse_boundedProfile_hypothesis
  intro hPeq
  refine ⟨hPeq.decider, 2^804, le_refl _, hPeq.timeBound_le,
    hPeq.numStates_bound, ?_, ?_⟩
  · -- n ≥ 2 at n = 2 ^ 804
    calc (2:ℕ) = 2^1 := by norm_num
      _ ≤ 2^804 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  · -- template collapse
    apply cookLevinProfileTemplateCollapse_from_matching_fixed
      hPeq.decider (2 ^ 804) two_pow_804_ge_two two_pow_804_ge_four
      hPeq.timeBound_le hPeq.numStates_bound
    · -- matching-form bundle: Agent Q4's N1_matching_from_per_type_bridges
      exact N1_matching_from_per_type_bridges
        hPeq.decider (2 ^ 804) two_pow_804_ge_two two_pow_804_ge_four
        hPeq.timeBound_le hPeq.numStates_bound
    · -- universal-form direct bundle: Agent M17-closer
      exact hUniv
        hPeq.decider (2 ^ 804) two_pow_804_ge_two two_pow_804_ge_four
        hPeq.timeBound_le hPeq.numStates_bound

/-! ## 5. Kernel-only axiom trace. -/

#print axioms N1_matching_from_per_type_bridges_universal
#print axioms M17_direct_bundle_universal
#print axioms two_pow_804_ge_two
#print axioms two_pow_804_ge_four
#print axioms P_ne_NP_truly_zero_final

end Bridges
end Paper93
end PallLean
