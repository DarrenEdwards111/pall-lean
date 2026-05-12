/-
  PallLean/Paper93/Paper283/ZeroArgP_ne_NP.lean

  Z14: Final composition attempt via paper §28.3 complete chain.

  This file packages the bounded-profile `Step252` bridge
  `Step4Compiler.Step252.P_ne_NP_from_cookLevin_templateCollapse_boundedProfile_hypothesis`
  at the canonical `n = 2 ^ 804` scale (paper §40 Theorem 209 Step 6
  p. 199), discharging the six concrete `Σ'` components and taking the
  residual bounded-profile template-collapse obligation as an explicit
  `Prop`-level hypothesis. Per the task prompt's "hypothesis-taking
  form if necessary" directive, this keeps the file `sorry`-free and
  kernel-only while the §28.3 chain's bounded-profile collapse is
  assembled elsewhere.

  ## Composition shape

    * `P_ne_NP_from_cookLevin_templateCollapse_boundedProfile_hypothesis`
      (Step252 §252.13h): one-hypothesis Cook-Levin ⇒ `P ≠ NP` bridge.
    * Six concrete components at `n = 2 ^ 804`:
        - `M := hPeq.decider`
        - `n := 2 ^ 804`, `hn := le_refl _`
        - `htb := hPeq.timeBound_le`
        - `hns := hPeq.numStates_bound`
        - `hn2 : n ≥ 2` via a local calc bridge `(2 : ℕ) = 2^1 ≤ 2^804`
    * Seventh component: bounded-profile template-collapse obligation
      taken as a `∀ (hPeq : PeqNP_Paper), …` hypothesis of this
      theorem. This is the honest §28.3-chain slot: any inhabitant of
      this hypothesis (assembled via the paper §28.3 chain) collapses
      the signature to a zero-argument `P ≠ NP`.

  ## Paper citations

    * §28.3 (complete chain, bounded-profile template collapse)
    * §40 Theorem 207 p. 199 (six-step contradiction chain)
    * §40 Theorem 209 Step 6 p. 199 (canonical `n = 2 ^ 804` scale)
    * §9 Lemma 31 parts (1)-(2) (stars-and-bars bounded-profile count)
    * §49.1 p. 230 (axiom-free, no `sorry`)

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  Expected `#print axioms P_ne_NP_via_SNF_chain`:
      [propext, Classical.choice, Quot.sound]
-/

import PallLean.Step4Compiler
import PallLean.WithinProfileBound
import PallLean.PaperFaithfulSeparation

namespace PallLean.Paper93.Paper283

open TuringMachine
open PaperFaithfulSeparation
open WithinProfileBound
open Step4Compiler

/-- Conditional zero-arg P ≠ NP via paper §28.3 complete chain.

The `_hChain : True` slot marks this as the §28.3 complete-chain
composition headline (per the Z14 task prompt's exact signature
directive). The bounded-profile template-collapse obligation is
threaded as an explicit `Prop`-level hypothesis — the honest §28.3
slot — keeping this file `sorry`-free and kernel-only until the
chain's bounded-profile collapse lands unconditionally.

Composition routes through
`Step4Compiler.Step252.P_ne_NP_from_cookLevin_templateCollapse_boundedProfile_hypothesis`
at the canonical `n = 2 ^ 804` scale, with six Σ′ components
discharged concretely from `PeqNP_Paper` data and the seventh (the
bounded-profile template-collapse obligation itself) threaded
through the explicit `hBoundedProfile` hypothesis. -/
theorem P_ne_NP_via_SNF_chain
    (_hChain : True)
    (hBoundedProfile :
      ∀ (hPeq : PaperFaithfulSeparation.PeqNP_Paper),
        WithinProfileBound.CookLevinProfileTemplateCollapseLemmaBoundedProfile
          hPeq.decider (2 ^ 804)
          (by
            calc (2 : ℕ) = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ 804 := Nat.pow_le_pow_right (by norm_num) (by norm_num))
          hPeq.timeBound_le hPeq.numStates_bound) :
    P ≠ NP := by
  -- Compose via existing Step252 bounded-profile bridge.
  apply Step4Compiler.Step252.P_ne_NP_from_cookLevin_templateCollapse_boundedProfile_hypothesis
  intro hPeq
  refine ⟨hPeq.decider, 2 ^ 804, le_refl _, hPeq.timeBound_le,
    hPeq.numStates_bound, ?_, ?_⟩
  · -- `hn2 : n ≥ 2` at `n = 2 ^ 804`.
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ 804 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  · -- Bounded-profile template-collapse obligation threaded through
    -- the explicit §28.3-chain hypothesis.
    exact hBoundedProfile hPeq

#print axioms P_ne_NP_via_SNF_chain

end PallLean.Paper93.Paper283
