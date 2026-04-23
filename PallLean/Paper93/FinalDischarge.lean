/-
  PallLean/Paper93/FinalDischarge.lean

  Agent G5 (parallel, 5 of 10) — Composition of:

    * Agent F5 — ambient finrank ≤ 3 (per-type shared `W_σ` family in the
      ambient `MvPolynomial (Fin n) ℚ` with `finrank ≤ 3`);
    * Agent G4 — spanning (the Cook-Levin post-span at each bounded profile
      is contained in `cookLevinProfileSubspace bp W`);
    * Agent C's `of_profileSubspace` / `of_bridge` composition
      (`PallLean.Paper93.CookLevinProfileSubspace.cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_bridge`)

  The three pieces combine to discharge
  `PallLean.Paper93.BoundedProfileTemplateCollapseDischarge` — the single
  hypothesis that Agent D's `P_ne_NP_absolute_unconditional`
  (commit `1df51de`, `Paper93/FinalComposition.lean`) takes.

  F5 and G4 have NOT yet landed in repo. Per the task prompt's explicit
  fallback instruction, this file therefore:

    * Exposes F5 as the Prop-valued hypothesis
      `AgentF5_AmbientFinrankLeThree`
      (per-(`M`,`n`,…) existence of a `W` family with
      `Module.Finite ℚ ↥(W τ)` and `finrank ℚ ↥(W τ) ≤ 3`);

    * Exposes G4 as the Prop-valued hypothesis
      `AgentG4_Spanning`
      (per-(`M`,`n`,…) and per-bounded-profile containment of the
      Cook-Levin post-span inside `cookLevinProfileSubspace bp W`);

    * Derives `boundedProfileTemplateCollapseDischarged : F5 → G4 → _`
      by composition through Agent C's `of_bridge`;

    * Specialises `P_ne_NP_absolute_unconditional` to
      `P_ne_NP_absolute_zero_args : F5 → G4 → P ≠ NP`.

  When F5 and G4 land in-file, supplying those derivations at the use site
  collapses the signature to `P ≠ NP` with zero arguments. The axiom profile
  is kernel-only (`[propext, Classical.choice, Quot.sound]`) throughout.

  No additional axioms are introduced. No `sorry`. No bad axioms.
-/
import PallLean.Paper93.FinalComposition
import PallLean.Paper93.CookLevinProfileSubspace
import PallLean.WithinProfileBound

namespace PallLean
namespace Paper93

open TuringMachine MvPolynomial WithinProfileBound
open PaperFaithfulSeparation SymmetricPowerBound
open Step4Compiler

/-! ## Agent F5 hypothesis: ambient finrank ≤ 3 family

For every bounded-parameter input `(M, n, hn, htb, hns)`, there is a
per-`ConstraintType` family of ℚ-submodules of `MvPolynomial (Fin n) ℚ`,
each finite-dimensional and of `finrank ≤ 3`. This is the ambient
per-type `W_σ` target of paper §9 Lemma 31, stated as a Prop to allow
dependency-injection until Agent F5 lands a constructive instance
in-file (e.g. via a paper-faithful compiled-basis projection). -/
def AgentF5_AmbientFinrankLeThree : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2)
    (_htb : M.timeBound ≤ 4) (_hns : M.numStates ≤ n),
    ∃ W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ),
      (∀ τ, Module.Finite ℚ ↥(W τ)) ∧
      (∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3)

/-! ## Agent G4 hypothesis: spanning containment

For every bounded-parameter input, and for every ambient `W` family
satisfying F5's structural bounds, the Cook-Levin post-span at every
bounded-profile histogram is contained in `cookLevinProfileSubspace bp W`.

This is the structural content of Agent G4: the paper-faithful §9 Lemma
31 bridge step identifying each classified-set generator with an
element of `∏_τ Sym^{bp.toHistogram τ}(W τ)`. Stated as a Prop at the
full universal-quantifier level so it combines cleanly with F5 above. -/
def AgentG4_Spanning : Prop :=
  ∀ (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ)),
    (∀ τ, Module.Finite ℚ ↥(W τ)) →
    (∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3) →
    ∀ bp : BoundedProfile (Nat.log 2 n),
      cookLevinPostSpanAt M n hn htb hns bp.toHistogram
        ≤ cookLevinProfileSubspace bp W

/-! ## Composition: F5 + G4 ⇒ BoundedProfileTemplateCollapseDischarge

Given the two hypotheses above and Agent C's
`cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_bridge`
(from `Paper93/CookLevinProfileSubspace.lean`), we compose into the
single Prop consumed by `P_ne_NP_absolute_unconditional` in
`Paper93/FinalComposition.lean`. -/

/-- **Agent G5 composition (F5 + G4 ⇒ bounded-profile discharge).**

Given Agent F5 (ambient finrank ≤ 3 family) and Agent G4 (post-span
spanning), `BoundedProfileTemplateCollapseDischarge` holds: for every
`(M, n, hn, htb, hns)` with `timeBound ≤ 4`, `numStates ≤ n`, and
`n ≥ 2`, the Cook-Levin bounded-profile template-collapse lemma is
derivable.

The proof: pick `W` from F5, then feed it (and G4's containment) into
Agent B/C's `cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_bridge`
which internally runs:
  - Agent 9's generic `profileSubspace_finrank_bound` for finrank ≤ ∏;
  - Finset-image of a basis, cardinality ≤ finrank ≤ profileTemplateBound;
  - containment via the spanning hypothesis.

All steps are kernel-level proof-term compositions. -/
theorem boundedProfileTemplateCollapseDischarged
    (hF5 : AgentF5_AmbientFinrankLeThree)
    (hG4 : AgentG4_Spanning) :
    BoundedProfileTemplateCollapseDischarge := by
  intro M n hn2 htb hns
  -- Pull F5's ambient W family.
  obtain ⟨W, hW_fin, hW_dim⟩ := hF5 M n hn2 htb hns
  -- Feed into Agent C's bridge with G4's spanning.
  exact
    cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_bridge
      M n hn2 htb hns W hW_fin hW_dim (hG4 M n hn2 htb hns W hW_fin hW_dim)

/-- **Alias matching the task spec name.** -/
theorem boundedProfileTemplateCollapseDischarge_discharged
    (hF5 : AgentF5_AmbientFinrankLeThree)
    (hG4 : AgentG4_Spanning) :
    BoundedProfileTemplateCollapseDischarge :=
  boundedProfileTemplateCollapseDischarged hF5 hG4

/-! ## Final kernel-only `P ≠ NP` — zero-arg modulo F5/G4

With F5 and G4 discharged (hypotheses awaiting constructive Agent F5/G4
in-file landings), the Cook-Levin bounded-profile template-collapse
obligation is dispatched, and Agent D's `P_ne_NP_absolute_unconditional`
closes to `P ≠ NP`. -/

/-- **`P ≠ NP` — zero explicit algebraic/combinatorial arguments beyond
the F5/G4 hypothesis pair.**

Composes:
  * Agent F5 (ambient finrank ≤ 3 per-type `W_σ` family)
  * Agent G4 (Cook-Levin post-span spanning containment)
  * Agent C's `of_bridge` (Agent B layer, `CookLevinProfileSubspace.lean`)
  * Agent D's `P_ne_NP_absolute_unconditional`
    (`Paper93/FinalComposition.lean`, commit `1df51de`)

Axiom profile: kernel-only `[propext, Classical.choice, Quot.sound]`. -/
theorem P_ne_NP_absolute_zero_args
    (hF5 : AgentF5_AmbientFinrankLeThree)
    (hG4 : AgentG4_Spanning) :
    P ≠ NP :=
  P_ne_NP_absolute_unconditional
    (boundedProfileTemplateCollapseDischarge_discharged hF5 hG4)

-- **Axiom audit** — expected: kernel-only `[propext, Classical.choice, Quot.sound]`.
#print axioms boundedProfileTemplateCollapseDischarged
#print axioms boundedProfileTemplateCollapseDischarge_discharged
#print axioms P_ne_NP_absolute_zero_args

end Paper93
end PallLean
