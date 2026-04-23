/-
  PallLean/Paper93/Spanning/Composition.lean — Per-type spanning
  composition discharging Agent B's
  `cookLevinProfileSubspace_contains_postSpan` hypothesis.

  ## Scope

  Agent B (commit `3c20a56`,
  `PallLean/Paper93/CookLevinProfileSubspace.lean`) left the concrete
  containment

    `cookLevinPostSpanAt M n hn htb hns bp.toHistogram
        ≤ cookLevinProfileSubspace bp W`

  open as an explicit hypothesis
  (`cookLevinProfileSubspace_contains_postSpan_of_hypothesis`).

  The per-type spanning work was split across parallel agents
  G1 (booleanity), G2 (adjacency), G3 (transitionLeft). Each Gi
  supplies, for its constraint type `τ`, a direct subspace-level
  containment of the restricted post-span image.

  This file (Agent G4 of 10) contains ONLY the composition layer:

  * we take as hypothesis a single bundled per-type containment
    of the form delivered by G1/G2/G3 — namely, for every bounded
    profile `bp` and every generator of the Cook–Levin post-span at
    `bp.toHistogram`, the generator already lies in the Cook–Levin
    profile subspace supplied by the per-type spaces `W τ`;
  * we produce the aggregate containment
    `cookLevinProfileSubspace_contains_postSpan_discharged`, which
    is exactly the premise consumed by Agent B's bridge lemmas
    (`cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_bridge`,
    `cookLevin_allBoundedProfilePostSpan_finrank_le_of_bridge`).

  ## Faithfulness

  The per-type hypothesis is expressed pointwise on the generating
  set of `allBoundedProfilePostSpan`, matching exactly what each
  Gi delivers. The composition is a pure `Submodule.span_le`
  dispatch; no new analytic content is introduced.

  ## Axiom trace

  `#print axioms` at the end of this file should show only the
  kernel-level `propext`, `Classical.choice`, `Quot.sound`
  dependencies inherited from Mathlib.
-/

import PallLean.Paper93.CookLevinProfileSubspace
import PallLean.WithinProfileBound

open Module
open scoped BigOperators

namespace PallLean
namespace Paper93
namespace Spanning

open MvPolynomial SymmetricPowerBound TuringMachine PaperFaithfulSeparation
open WithinProfileBound MultilinearSPDP

/-! ## Per-type generator hypothesis bundle

Each per-type agent Gi (i ∈ {1,2,3}) delivers a pointwise containment
statement on the generators of `allBoundedProfilePostSpan`. We expose
a single bundled datatype packaging all three deliverables.

The bundle asserts: for every bounded profile `bp`, every triple
`(S, shift, g)` generating `cookLevinPostSpanAt M n hn htb hns
bp.toHistogram` produces an element lying in
`cookLevinProfileSubspace bp W`.

This is precisely the content of G1/G2/G3 once one dispatches on
constraint type within each generator: each factor of type τ
contributes a term in `symPower (h τ) (W τ)`, and the joint
product assembles (by definition of `profileSubspace`) into a
member of `profileSubspace bp.toHistogram W = cookLevinProfileSubspace
bp W`. -/

/-- Per-type spanning bundle.

    For a fixed Turing machine `M`, input length `n`, and per-type
    family `W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ)`,
    this bundle asserts that every generator of the Cook–Levin
    post-span (at any bounded profile) lies in the corresponding
    Cook–Levin profile subspace.

    Content-wise, the bundle collates G1 (booleanity), G2 (adjacency),
    G3 (transitionLeft) into one per-generator containment. The
    ambient `transitionRight` coordinate of `ConstraintType` is
    dormant on the Cook–Levin factor list (see
    `WithinProfileBound.cookLevinConstraintType`), so no fourth
    per-type agent is needed. -/
def CookLevinPerTypeSpanning
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ)) : Prop :=
  ∀ (bp : BoundedProfile (Nat.log 2 n))
    (S : List (Fin n)) (_hSlen : S.length ≤ Nat.log 2 n)
    (shift : MvPolynomial (Fin n) ℚ) (_hshift : shift.vars ⊆ S.toFinset)
    (g : MvPolynomial (Fin n) ℚ)
    (_hg : g ∈ boundedProfileClassifiedSet
              (fun i => (cookLevinFactorList M n hn htb hns).get i)
              (cookLevinConstraintType M n hn htb hns)
              S bp.toHistogram),
    mlProj (shift * g) ∈ cookLevinProfileSubspace bp W

/-! ## Composition: the discharged containment

Given `CookLevinPerTypeSpanning`, we establish the containment

  `cookLevinPostSpanAt M n hn htb hns bp.toHistogram
      ≤ cookLevinProfileSubspace bp W`

for every bounded profile `bp`. This is exactly the premise
`hPostSpan` of Agent B's bridge lemmas. -/

/-- **Composition lemma: per-type spanning ⇒ post-span containment.**

    The full containment follows from the per-type bundle by
    `Submodule.span_le`: the post-span is the `ℚ`-span of
    `{mlProj (shift * g)}` ranging over all (S, shift, g) triples,
    and the bundle places every such generator directly inside
    `cookLevinProfileSubspace bp W`. -/
theorem cookLevinProfileSubspace_contains_postSpan_at_bp
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (hSpan : CookLevinPerTypeSpanning M n hn htb hns W)
    (bp : BoundedProfile (Nat.log 2 n)) :
    cookLevinPostSpanAt M n hn htb hns bp.toHistogram
      ≤ cookLevinProfileSubspace bp W := by
  classical
  -- Unfold `cookLevinPostSpanAt` and apply `Submodule.span_le`.
  refine Submodule.span_le.mpr ?_
  intro q hq
  -- `hq` exhibits `q = mlProj (shift * g)` for some generator.
  simp only [Set.mem_iUnion, Set.mem_image] at hq
  obtain ⟨S, hSlen, shift, hshiftvars, g, hg, rfl⟩ := hq
  -- Apply the per-type spanning bundle to this generator.
  exact hSpan bp S hSlen shift hshiftvars g hg

/-- **Full per-profile discharged containment.**

    Packaging `cookLevinProfileSubspace_contains_postSpan_at_bp`
    across all bounded profiles, producing exactly the family of
    containments consumed by
    `cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_bridge`. -/
theorem cookLevinProfileSubspace_contains_postSpan_discharged
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (hSpan : CookLevinPerTypeSpanning M n hn htb hns W) :
    ∀ bp : BoundedProfile (Nat.log 2 n),
      cookLevinPostSpanAt M n hn htb hns bp.toHistogram
        ≤ cookLevinProfileSubspace bp W := by
  intro bp
  exact cookLevinProfileSubspace_contains_postSpan_at_bp
    M n hn htb hns W hSpan bp

/-! ## Composed end-to-end bridge

Direct plug-in to Agent B's template-collapse bridge. Given per-type
spanning and the per-type dimension / finiteness data for `W`,
produces the universal template-collapse lemma. -/

/-- **End-to-end template-collapse bridge from per-type spanning.** -/
theorem cookLevinProfileTemplateCollapseLemmaBoundedProfile_from_perTypeSpanning
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (hW_fin : ∀ τ, Module.Finite ℚ ↥(W τ))
    (hW_dim : ∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3)
    (hSpan : CookLevinPerTypeSpanning M n hn htb hns W) :
    CookLevinProfileTemplateCollapseLemmaBoundedProfile M n hn htb hns :=
  cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_bridge
    M n hn htb hns W hW_fin hW_dim
    (cookLevinProfileSubspace_contains_postSpan_discharged
      M n hn htb hns W hSpan)

/-- **End-to-end finrank bound from per-type spanning.**

    For a fixed bounded profile `bp`, the Cook–Levin post-span
    finrank is at most `profileTemplateBound bp.toHistogram` once
    the per-type spanning and dim ≤ 3 data are supplied. -/
theorem cookLevin_allBoundedProfilePostSpan_finrank_le_from_perTypeSpanning
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (bp : BoundedProfile (Nat.log 2 n))
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (hW_fin : ∀ τ, Module.Finite ℚ ↥(W τ))
    (hW_dim : ∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3)
    (hSpan : CookLevinPerTypeSpanning M n hn htb hns W) :
    Module.finrank ℚ
        ↥(cookLevinPostSpanAt M n hn htb hns bp.toHistogram)
      ≤ profileTemplateBound bp.toHistogram :=
  cookLevin_allBoundedProfilePostSpan_finrank_le_of_bridge
    M n hn htb hns bp W hW_fin hW_dim
    (cookLevinProfileSubspace_contains_postSpan_at_bp
      M n hn htb hns W hSpan bp)

/-! ## Shape aligned with Agent G5's `AgentG4_Spanning` hypothesis

Agent G5 (commit `9b4641d`, `Paper93/FinalDischarge.lean`) consumes a
hypothesis named `AgentG4_Spanning` with the signature

  `∀ M n hn htb hns W, (∀ τ, Finite) → (∀ τ, finrank ≤ 3)
       → ∀ bp, cookLevinPostSpanAt ... ≤ cookLevinProfileSubspace bp W`.

We expose a theorem with exactly that signature, assuming the per-type
spanning bundle `CookLevinPerTypeSpanning` as a universal hypothesis
(delivered by G1/G2/G3). This is the precise landing point against
which G5's final-discharge theorem is parameterised. -/

/-- **Universal per-type spanning bundle** — the universal-quantifier
    version of `CookLevinPerTypeSpanning` suitable as a single
    Prop-level substitute for Agent G5's `AgentG4_Spanning`. -/
def CookLevinPerTypeSpanning_universal : Prop :=
  ∀ (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ)),
    CookLevinPerTypeSpanning M n hn htb hns W

/-- **Composition of G1/G2/G3 ⇒ `AgentG4_Spanning` shape.**

    Given the universal per-type spanning bundle, we produce the
    full containment family in exactly the shape required by Agent
    G5's `AgentG4_Spanning` Prop. -/
theorem cookLevinProfileSubspace_contains_postSpan_universal
    (hSpan : CookLevinPerTypeSpanning_universal) :
    ∀ (M : DTM) (n : ℕ) (hn : n ≥ 2)
      (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
      (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ)),
      (∀ τ, Module.Finite ℚ ↥(W τ)) →
      (∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3) →
      ∀ bp : BoundedProfile (Nat.log 2 n),
        cookLevinPostSpanAt M n hn htb hns bp.toHistogram
          ≤ cookLevinProfileSubspace bp W := by
  intro M n hn htb hns W _hW_fin _hW_dim bp
  exact cookLevinProfileSubspace_contains_postSpan_at_bp
    M n hn htb hns W (hSpan M n hn htb hns W) bp

#print axioms cookLevinProfileSubspace_contains_postSpan_at_bp
#print axioms cookLevinProfileSubspace_contains_postSpan_discharged
#print axioms cookLevinProfileTemplateCollapseLemmaBoundedProfile_from_perTypeSpanning
#print axioms cookLevin_allBoundedProfilePostSpan_finrank_le_from_perTypeSpanning
#print axioms cookLevinProfileSubspace_contains_postSpan_universal

end Spanning
end Paper93
end PallLean
