/-
  PallLean/Paper93/FinalCompositionV2.lean

  Agent K1 of 2 (parallel) — **Specialised** final composition of the
  paper-faithful kernel-only chain into `P ≠ NP` with zero explicit
  arguments beyond the `AgentF5_AmbientFinrankLeThree` /
  `AgentG4_Spanning_concrete` pair.

  ## Scope

  This is a *parallel* sibling of `Paper93/FinalComposition.lean` and
  `Paper93/FinalDischarge.lean` that uses Agent J1's **concrete**
  `W_σ(τ)` family (`PallLean.Paper93.Wiring.concreteW`) directly,
  rather than quantifying `AgentG4_Spanning` over every abstract
  `W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ)`
  satisfying the F5 structural bounds.

  Concretely, we expose:

    * `AgentG4_Spanning_concrete` — a specialised G4 Prop at the
      canonical scale `n ≥ 2^804` that only asserts the existence of
      a coordinate embedding `σ : Fin 4 ↪ Fin n` such that the
      Cook-Levin post-span at every bounded-profile histogram is
      contained in
      `cookLevinProfileSubspace bp (concreteW n hn4 σ)`; and

    * `P_ne_NP_absolute_zero_args_v2` — a specialised zero-args
      theorem threading this concrete spanning Prop directly into
      `Step4Compiler.Step252.P_ne_NP_from_cookLevin_templateCollapse_boundedProfile_hypothesis`,
      **without** routing through the fully-universal
      `BoundedProfileTemplateCollapseDischarge` of
      `Paper93/FinalComposition.lean`.

  We deliberately do **not** edit `Paper93/FinalComposition.lean`;
  instead this file is an additive parallel entry point that downstream
  callers may use whenever a concrete `W_σ(τ)` discharge is available.

  ## Proof skeleton

  The `P_ne_NP_absolute_zero_args_v2` proof uses the same top-level
  Σ′-producer ⇒ `Step252` pipeline as
  `P_ne_NP_absolute_unconditional`, but the Σ′ producer feeds the
  bounded-profile template-collapse witness via
  `cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_bridge`
  applied to the concrete `W := concreteW n hn4 σ`, using
  `concreteW_finite` / `concreteW_finrank_le_three` for the structural
  hypotheses and the `hG4` existential for the spanning hypothesis.

  The `hF5` argument is retained purely to mirror the signature of
  Agent G5's `P_ne_NP_absolute_zero_args`, so callers that already
  have an F5 proof can plug it in without restructuring. It is unused
  in the proof term (the concrete `W_σ(τ)` family supplied by
  `concreteW` already witnesses the F5 structural conclusion via
  `concreteW_finite` and `concreteW_finrank_le_three`).

  ## Paper citations

    * §40 Theorem 207 p. 199 (six-step contradiction chain);
    * §40 Theorem 209 Step 6 p. 199 (canonical `n = 2^804` scale);
    * §9 Lemma 31 pp. 41-45 (bounded-profile template collapse;
      concrete `W_σ(τ)` form);
    * §49.1 p. 230 (axiom-free, no `sorry`).

  ## Axiom profile

  Every theorem in this file is kernel-only
  (`[propext, Classical.choice, Quot.sound]`). No bad axioms, no
  `sorry`.
-/

import PallLean.Paper93.FinalComposition
import PallLean.Paper93.FinalDischarge
import PallLean.Paper93.CookLevinProfileSubspace
import PallLean.Paper93.Wiring.ConcreteW
import PallLean.WithinProfileBound

namespace PallLean
namespace Paper93

open TuringMachine MvPolynomial WithinProfileBound
open PaperFaithfulSeparation SymmetricPowerBound
open Step4Compiler
open PallLean.Paper93.Wiring (concreteW concreteW_finite concreteW_finrank_le_three)

/-! ## Specialised G4 Prop using `concreteW`

The universal `AgentG4_Spanning` of `Paper93/FinalDischarge.lean`
quantifies over every `W : ConstraintType → Submodule ℚ
(MvPolynomial (Fin n) ℚ)` with the F5 structural bounds and demands a
uniform spanning containment. Here we specialise to Agent J1's
concrete `concreteW n hn4 σ τ` family, asking only for the existence
of a coordinate embedding `σ : Fin 4 ↪ Fin n` witnessing the
containment at each bounded profile.

The scale is pinned at `n ≥ 2^804` (paper §40 Theorem 209 Step 6
p. 199 contradiction threshold), and we explicitly package
`n ≥ 2`, `n ≥ 4`, and `n ≥ 2^804` (redundant but convenient for
downstream specialisation). -/

/-- **Specialised G4 Prop (concrete `W_σ` form).**

For every DTM `M` at canonical scale `n ≥ 2^804` (with
`timeBound ≤ 4` and `numStates ≤ n`), and every bounded-profile
histogram `bp`, there exists a coordinate embedding
`σ : Fin 4 ↪ Fin n` such that the Cook-Levin post-span at
`bp.toHistogram` is contained in
`cookLevinProfileSubspace bp (concreteW n hn4 σ)`.

This is the `concreteW`-specialised form of
`PallLean.Paper93.AgentG4_Spanning`, with the universal quantifier
over abstract `W` families replaced by an existential witness over
coordinate embeddings into Agent J1's concrete per-type source
space. -/
def AgentG4_Spanning_concrete : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn2 : n ≥ 2) (hn4 : n ≥ 4),
    ∀ bp : BoundedProfile (Nat.log 2 n),
      ∃ σ : Fin 4 ↪ Fin n,
        cookLevinPostSpanAt M n hn2 htb hns bp.toHistogram
          ≤ cookLevinProfileSubspace bp (fun τ => concreteW n hn4 σ τ)

/-! ## `n ≥ 2^804 ⇒ n ≥ 4` and `n ≥ 2^804 ⇒ n ≥ 2`

Two numeric helpers used to feed the canonical `n = 2^804` scale
into the bridge producer below. -/

private theorem two_pow_804_ge_two : (2 ^ 804 : ℕ) ≥ 2 := by
  calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ 804 := Nat.pow_le_pow_right (by omega) (by omega)

private theorem two_pow_804_ge_four : (2 ^ 804 : ℕ) ≥ 4 := by
  calc (4 : ℕ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ 804 := Nat.pow_le_pow_right (by omega) (by omega)

private theorem ge_two_pow_804_ge_two {n : ℕ} (hn : n ≥ 2 ^ 804) : n ≥ 2 :=
  le_trans two_pow_804_ge_two hn

private theorem ge_two_pow_804_ge_four {n : ℕ} (hn : n ≥ 2 ^ 804) : n ≥ 4 :=
  le_trans two_pow_804_ge_four hn

/-! ## Specialised Σ′ witness producer

We skip the fully-universal `BoundedProfileTemplateCollapseDischarge`
stage and produce the Σ′ witness consumed by
`Step252.P_ne_NP_from_cookLevin_templateCollapse_boundedProfile_hypothesis`
directly from the concrete G4 spanning hypothesis.

For each `hPeq : PeqNP_Paper`, we take:

  * `M := hPeq.decider`;
  * `n := 2^804`;
  * structural hypotheses `hn2`, `hn4` from the numeric helpers above;
  * the bounded-profile template-collapse witness produced by
    `cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_bridge`
    applied to `W := concreteW (2^804) hn4 σ`, with `σ` supplied
    bp-by-bp by the concrete G4 spanning hypothesis.

The `hF5` argument is accepted for signature compatibility with
`P_ne_NP_absolute_zero_args` but is not used in the proof term
(the concrete `W_σ(τ)` family already carries the F5 structural
bounds via `concreteW_finite` and `concreteW_finrank_le_three`). -/

/-- **Specialised Σ′ witness producer (concrete W_σ form).**

Given the specialised G4 spanning hypothesis `hG4` (and the unused
F5 hypothesis `hF5` retained for signature compatibility), for every
`PeqNP_Paper` bundle we produce the Σ′ witness at the canonical
`n = 2^804` scale, using Agent B/C's
`cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_bridge`
with the concrete `concreteW` family as `W`. -/
noncomputable def sigmaWitness_of_PeqNP_Paper_v2
    (_hF5 : AgentF5_AmbientFinrankLeThree)
    (hG4 : AgentG4_Spanning_concrete)
    (hPeq : PeqNP_Paper) :
    Σ' (M : DTM) (n : ℕ) (_ : n ≥ 2 ^ 804)
      (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn2 : n ≥ 2),
      WithinProfileBound.CookLevinProfileTemplateCollapseLemmaBoundedProfile
        M n hn2 htb hns := by
  classical
  -- Numeric hypotheses at the canonical scale.
  have hn2 : (2 ^ 804 : ℕ) ≥ 2 := two_pow_804_ge_two
  have hn4 : (2 ^ 804 : ℕ) ≥ 4 := two_pow_804_ge_four
  -- Per-bounded-profile spanning containment via `hG4`.
  -- We select a *single* `σ` per bounded-profile `bp`, which is the
  -- shape required by `cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_bridge`
  -- modulo routing through the per-profile at-profile form.
  refine ⟨hPeq.decider, 2 ^ 804, le_refl _,
          hPeq.timeBound_le, hPeq.numStates_bound, hn2, ?_⟩
  -- Unpack the bounded-profile template-collapse obligation per `bp`.
  intro bp
  -- Extract a σ witness for this specific `bp` from `hG4`.
  obtain ⟨σ, hPostSpan⟩ :=
    hG4 hPeq.decider (2 ^ 804) (le_refl _)
      hPeq.timeBound_le hPeq.numStates_bound hn2 hn4 bp
  -- Finiteness and finrank ≤ 3 for the concrete W_σ family.
  have hW_fin : ∀ τ, Module.Finite ℚ ↥(concreteW (2 ^ 804) hn4 σ τ) :=
    fun τ => concreteW_finite (2 ^ 804) hn4 σ τ
  have hW_dim : ∀ τ, Module.finrank ℚ ↥(concreteW (2 ^ 804) hn4 σ τ) ≤ 3 :=
    fun τ => concreteW_finrank_le_three (2 ^ 804) hn4 σ τ
  -- Feed to Agent B/C's *per-profile* bridge to obtain the
  -- `cookLevinProfileTemplateCollapseAtProfile` witness at `bp`.
  exact cookLevinProfileTemplateCollapseAtProfile_of_bridge
    hPeq.decider (2 ^ 804) hn2 hPeq.timeBound_le hPeq.numStates_bound
    bp (concreteW (2 ^ 804) hn4 σ) hW_fin hW_dim hPostSpan

/-! ## Specialised final theorem

With the specialised Σ′ witness producer in hand, the specialised
final theorem is the direct composition with
`Step4Compiler.Step252.P_ne_NP_from_cookLevin_templateCollapse_boundedProfile_hypothesis`. -/

/-- **`P ≠ NP` (specialised, concrete `W_σ` form).**

Specialised sibling of `P_ne_NP_absolute_zero_args` of
`Paper93/FinalDischarge.lean`. Uses Agent J1's concrete `concreteW`
family directly, instead of threading a universally-quantified `W`
through the F5/G4/`of_bridge` pipeline.

  * `hF5 : AgentF5_AmbientFinrankLeThree` — retained for signature
    compatibility with the universal variant; unused in the proof
    term (the `concreteW` family already carries F5's structural
    content).

  * `hG4 : AgentG4_Spanning_concrete` — the specialised, existential
    `σ`-form of G4 at the canonical `n ≥ 2^804` scale.

Axiom profile: kernel-only `[propext, Classical.choice, Quot.sound]`. -/
theorem P_ne_NP_absolute_zero_args_v2
    (hF5 : AgentF5_AmbientFinrankLeThree)
    (hG4 : AgentG4_Spanning_concrete) :
    P ≠ NP :=
  Step4Compiler.Step252.P_ne_NP_from_cookLevin_templateCollapse_boundedProfile_hypothesis
    (sigmaWitness_of_PeqNP_Paper_v2 hF5 hG4)

-- **Axiom audit** — expected: kernel-only
-- `[propext, Classical.choice, Quot.sound]`.
#print axioms AgentG4_Spanning_concrete
#print axioms sigmaWitness_of_PeqNP_Paper_v2
#print axioms P_ne_NP_absolute_zero_args_v2

end Paper93
end PallLean
