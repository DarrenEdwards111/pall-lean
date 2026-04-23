/-
  PallLean/Paper93/Direct/TemplateCollapseDirect.lean

  Paper §9 Lemma 31 — Direct Route C ⇒ Route A discharge of the
  bounded-profile template-collapse lemma at Agent J1's `concreteW`
  family.

  Agent M18 of M (parallel).

  ## Scope

  This file composes:

    * Agent M17's
      `cookLevinProfileSubspace_contains_postSpan_direct`
      (`PallLean/Paper93/Direct/PerTypeComposition.lean`): direct
      post-span containment at Agent J1's `concreteW n hn4
      (Fin.castLEEmb hn4) τ` family, composed from the four per-type
      row embeddings (M5 booleanity, M10 adjacency, M15 transitionLeft,
      M16 transitionRight dormant), **without** going through Agent
      I6 / J2's `CookLevinPerTypeSpanning_universal` bundle.

    * Agent C's basis-image Finset construction
      `basisImageFinset` / `basisImageFinset_card_le` /
      `span_basisImageFinset_eq`
      (`PallLean/Paper93/TemplateCollapseDischarge.lean`, commit
      `22fc7dc`): the Finset `G ⊆ MvPolynomial (Fin n) ℚ` obtained as
      the image of a basis of a finite-dimensional profile subspace,
      with `G.card ≤ finrank` and `span ℚ G = U`.

    * Agent J1's `concreteW_finite` / `concreteW_finrank_le_three`
      (`PallLean/Paper93/Wiring/ConcreteW.lean`, commit `b36a8b1`):
      per-type finite-dimensionality and `finrank ≤ 3` uniform bound
      for the concrete ambient `W_σ(τ)` family.

    * Agent B's `cookLevinProfileSubspace_finite` /
      `cookLevinProfileSubspace_finrank_le`
      (`PallLean/Paper93/CookLevinProfileSubspace.lean`): the
      Cook-Levin profile subspace's `Module.Finite` closure and its
      `finrank ≤ profileTemplateBound bp.toHistogram` bound via Agent
      9's generic profile-subspace finrank bound.

  The composition produces the bounded-profile template-collapse
  lemma
  `WithinProfileBound.CookLevinProfileTemplateCollapseLemmaBoundedProfile
   M n hn htb hns`, modulo the single residual hypothesis
  `CookLevinPerTypeRowEmbeddings_concreteW` consumed by M17.

  When M5 / M10 / M15 / M16 land as real theorems (not Props) and are
  aggregated into an unconditional inhabitant of
  `CookLevinPerTypeRowEmbeddings_concreteW`, substituting it at the
  call site of M18 below collapses this theorem to a genuinely
  zero-argument, kernel-only discharge of the bounded-profile
  template-collapse lemma at Agent J1's `concreteW` family.

  ## Deliverable

    * `cookLevinProfileTemplateCollapse_direct` — bounded-profile
      template-collapse lemma at Agent J1's `concreteW` family,
      composed from M17's direct post-span containment + Agent C's
      basis-image Finset construction + J1's `concreteW` structural
      bounds + Agent B's profile-subspace finrank bound.

  ## Proof strategy

  For every bounded profile `bp : BoundedProfile (Nat.log 2 n)`:

    1. Let `U := cookLevinProfileSubspace bp (fun τ => concreteW n hn4
       (Fin.castLEEmb hn4) τ)`. By J1 + Agent B,
         - `Module.Finite ℚ ↥U` via `cookLevinProfileSubspace_finite`
           + `concreteW_finite`,
         - `Module.finrank ℚ ↥U ≤ profileTemplateBound bp.toHistogram`
           via `cookLevinProfileSubspace_finrank_le` +
           `concreteW_finrank_le_three`.

    2. By M17, `cookLevinPostSpanAt M n hn htb hns bp.toHistogram ≤ U`
       (the direct post-span containment at `concreteW`, via the
       M5 / M10 / M15 / M16 row-embedding bundle).

    3. By Agent C's `basisImageFinset`, we obtain a Finset
       `G : Finset (MvPolynomial (Fin n) ℚ)` with
         - `Submodule.span ℚ (↑G) = U`        (via `span_basisImageFinset_eq`),
         - `G.card ≤ Module.finrank ℚ ↥U`      (via `basisImageFinset_card_le`).

    4. Combining 1 + 2 + 3 yields the per-bp
       `CookLevinProfileTemplateCollapseAtProfile` witness with
       `G.card ≤ profileTemplateBound bp.toHistogram`, discharging
       the bounded-profile obligation.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  Expected `#print axioms`:
      [propext, Classical.choice, Quot.sound]
-/
import PallLean.Paper93.Direct.PerTypeComposition
import PallLean.Paper93.TemplateCollapseDischarge
import PallLean.Paper93.CookLevinProfileSubspace
import PallLean.Paper93.Wiring.ConcreteW
import PallLean.WithinProfileBound

namespace PallLean.Paper93.Direct

open MvPolynomial SymmetricPowerBound TuringMachine PaperFaithfulSeparation
open WithinProfileBound
open PallLean.Paper93
open PallLean.Paper93.Spanning
open PallLean.Paper93.Wiring (concreteW concreteW_finite concreteW_finrank_le_three)

/-! ## 1. Main theorem — direct bounded-profile template-collapse at `concreteW`

Composition of Agent M17's direct post-span containment with Agent C's
basis-image Finset construction, yielding the bounded-profile
template-collapse lemma at Agent J1's `concreteW` family.

The single residual hypothesis is the
`CookLevinPerTypeRowEmbeddings_concreteW` bundle (aggregate of the
four per-type row embeddings M5 / M10 / M15 / M16), consumed by M17.
When that bundle lands as an unconditional inhabitant (i.e. all four
M5 / M10 / M15 / M16 are landed as real theorems), substituting it at
the call site below collapses this theorem to a zero-argument
`CookLevinProfileTemplateCollapseLemmaBoundedProfile`. -/

/-- **Agent M18 main theorem: direct bounded-profile template-collapse
at `concreteW`.**

For every Turing-machine parameter tuple `(M, n, hn, htb, hns)` with
`n ≥ 4`, given the direct M17 per-type row-embedding bundle at
`concreteW n hn4 (Fin.castLEEmb hn4)`, the bounded-profile
template-collapse lemma
`WithinProfileBound.CookLevinProfileTemplateCollapseLemmaBoundedProfile
M n hn htb hns` holds.

For every bounded profile `bp : BoundedProfile (Nat.log 2 n)`, the
generating finset `G` is constructed as Agent C's `basisImageFinset`
of the Cook-Levin profile subspace
`cookLevinProfileSubspace bp (fun τ => concreteW n hn4 (Fin.castLEEmb
hn4) τ)`, with cardinality bounded by
`profileTemplateBound bp.toHistogram` via Agent B's
`cookLevinProfileSubspace_finrank_le` + Agent J1's
`concreteW_finrank_le_three`. The containment of the post-span in
`span ℚ G` routes through M17's direct post-span containment, which
is the direct-chain Route C ⇒ Route A analogue.

Matches the task prompt's template signature:

```
theorem cookLevinProfileTemplateCollapse_direct
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2) (hn4 : n ≥ 4)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    WithinProfileBound.CookLevinProfileTemplateCollapseLemmaBoundedProfile
      M n hn htb hns
```

with the residual `hRowEmbeddings` hypothesis bound to the
`CookLevinPerTypeRowEmbeddings_concreteW` bundle (the aggregate of the
four per-type row embeddings M5 / M10 / M15 / M16, the parallel M-stack
deliverables). This is the exact pattern used by Agent M19's
`P_ne_NP_zero` for its residual `cookLevinProfileTemplateCollapse_direct`
hypothesis: a universal-form binder of the per-type hypothesis that is
preserved through the composition until the parallel M-stack lands
the unconditional inhabitant. The binder is `Prop`-level, so the
axiom profile remains kernel-only
`[propext, Classical.choice, Quot.sound]`.

When M5 / M10 / M15 / M16 land as real theorems and are aggregated
into an unconditional inhabitant of
`CookLevinPerTypeRowEmbeddings_concreteW M n hn htb hns hn4`,
substituting it at the call site collapses this theorem's signature
to a genuinely zero-argument `CookLevinProfileTemplateCollapseLemmaBoundedProfile`. -/
theorem cookLevinProfileTemplateCollapse_direct
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2) (hn4 : n ≥ 4)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hRowEmbeddings :
      CookLevinPerTypeRowEmbeddings_concreteW M n hn htb hns hn4) :
    WithinProfileBound.CookLevinProfileTemplateCollapseLemmaBoundedProfile
      M n hn htb hns := by
  classical
  intro bp
  -- Abbreviate the per-type family used throughout.
  set W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
    fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ with hW_def
  -- Step 1: structural data at `concreteW` (Agent J1).
  have hW_fin : ∀ τ, Module.Finite ℚ ↥(W τ) :=
    fun τ => concreteW_finite n hn4 (Fin.castLEEmb hn4) τ
  have hW_dim : ∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3 :=
    fun τ => concreteW_finrank_le_three n hn4 (Fin.castLEEmb hn4) τ
  -- Step 2: profile subspace `U := cookLevinProfileSubspace bp W`
  -- finite + finrank ≤ profileTemplateBound (Agent B).
  let U : Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
    cookLevinProfileSubspace bp W
  haveI hU_fin : Module.Finite ℚ ↥U :=
    cookLevinProfileSubspace_finite bp W hW_fin
  have hU_finrank :
      Module.finrank ℚ ↥U ≤ profileTemplateBound bp.toHistogram :=
    cookLevinProfileSubspace_finrank_le bp W hW_fin hW_dim
  -- Step 3: M17's direct post-span containment at `concreteW`,
  -- fed by the per-type row-embedding bundle hypothesis.
  have hPostSpan :
      allBoundedProfilePostSpan
          (PaperFaithfulSeparation.cook_levin_compilation M n hn htb hns).partition
          (Nat.log 2 n) (Nat.log 2 n)
          (fun i => (cookLevinFactorList M n hn htb hns).get i)
          (cookLevinConstraintType M n hn htb hns)
          bp.toHistogram
        ≤ U :=
    cookLevinProfileSubspace_contains_postSpan_direct
      M n hn htb hns hn4 bp hRowEmbeddings
  -- Step 4: Agent C's basis-image Finset construction of `G ⊆
  -- MvPolynomial (Fin n) ℚ` from a basis of `U`, with
  --   `Submodule.span ℚ (↑G) = U` and `G.card ≤ finrank ℚ ↥U`.
  let G : Finset (MvPolynomial (Fin n) ℚ) := @basisImageFinset n U hU_fin
  have hGspan :
      Submodule.span ℚ (↑G : Set (MvPolynomial (Fin n) ℚ)) = U :=
    @span_basisImageFinset_eq n U hU_fin
  have hGcard : G.card ≤ Module.finrank ℚ ↥U :=
    @basisImageFinset_card_le n U hU_fin
  -- Step 5: package the `CookLevinProfileTemplateCollapseAtProfile`
  -- witness for `bp` at `G`, via the two bounds composed above.
  refine ⟨G, ?_, ?_⟩
  · -- Containment `allBoundedProfilePostSpan … ≤ span ℚ G`.
    calc allBoundedProfilePostSpan
            (PaperFaithfulSeparation.cook_levin_compilation M n hn htb hns).partition
            (Nat.log 2 n) (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn htb hns).get i)
            (cookLevinConstraintType M n hn htb hns)
            bp.toHistogram
        ≤ U := hPostSpan
      _ = Submodule.span ℚ (↑G : Set (MvPolynomial (Fin n) ℚ)) := hGspan.symm
  · -- Cardinality bound `G.card ≤ profileTemplateBound bp.toHistogram`.
    calc G.card
        ≤ Module.finrank ℚ ↥U := hGcard
      _ ≤ profileTemplateBound bp.toHistogram := hU_finrank

/-! ## 2. Universal-form packaging

For downstream callers (e.g. Agent M19's `ZeroArgFinal.lean`) that
consume the M18 deliverable as a single universal hypothesis, we
expose the universal form that binds `(M, n, hn, hn4, htb, hns)` under
a forall. This matches the `CookLevinProfileTemplateCollapseDirect_universal`
shape consumed by M19's `P_ne_NP_zero`. -/

/-- **Universal M18 discharge, modulo M17's per-type row-embedding
bundle hypothesis.**

Binds the residual `hRowEmbeddings` hypothesis under a universal
quantifier over `(M, n, hn, hn4, htb, hns)`. Matches the shape of
`CookLevinProfileTemplateCollapseDirect_universal` in
`PallLean/Paper93/Direct/ZeroArgFinal.lean` exactly, with one
additional `hRowEmbeddings` argument per parameter tuple.

When the universal form of `CookLevinPerTypeRowEmbeddings_concreteW`
lands (i.e. all four per-type row embeddings M5 / M10 / M15 / M16 are
delivered as real theorems and aggregated), substituting it yields
the unconditional `CookLevinProfileTemplateCollapseDirect_universal`
consumed by M19. -/
theorem cookLevinProfileTemplateCollapse_direct_universal
    (hRowEmbeddings_universal :
      ∀ (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2)
        (hn4 : n ≥ 4) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinPerTypeRowEmbeddings_concreteW M n hn htb hns hn4) :
    ∀ (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2)
      (_hn4 : n ≥ 4) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
      WithinProfileBound.CookLevinProfileTemplateCollapseLemmaBoundedProfile
        M n hn htb hns := by
  intro M n hn hn4 htb hns
  exact cookLevinProfileTemplateCollapse_direct M n hn hn4 htb hns
    (hRowEmbeddings_universal M n hn hn4 htb hns)

/-! ## 3. Kernel-only axiom trace

Both deliverables above should depend only on
`[propext, Classical.choice, Quot.sound]`, i.e. only the standard
Mathlib kernel axioms. No bespoke axiom is introduced; the residual
`hRowEmbeddings` hypothesis is a `Prop`, so the binder preserves the
axiom profile.

All content routes through:

  * Agent M17's
    `cookLevinProfileSubspace_contains_postSpan_direct` (direct
    post-span containment at `concreteW` via the per-type row
    embeddings, without going through
    `CookLevinPerTypeSpanning_universal`);

  * Agent C's `basisImageFinset` / `basisImageFinset_card_le` /
    `span_basisImageFinset_eq` (basis-image Finset construction of a
    finite-dimensional submodule of `MvPolynomial (Fin n) ℚ`);

  * Agent J1's `concreteW_finite` / `concreteW_finrank_le_three`
    (structural bounds on the concrete ambient per-type `W_σ(τ)`);

  * Agent B's `cookLevinProfileSubspace_finite` /
    `cookLevinProfileSubspace_finrank_le` (Cook-Levin specialisation
    of Agent 9's generic profile-subspace finrank bound). -/

#print axioms cookLevinProfileTemplateCollapse_direct
#print axioms cookLevinProfileTemplateCollapse_direct_universal

end PallLean.Paper93.Direct
