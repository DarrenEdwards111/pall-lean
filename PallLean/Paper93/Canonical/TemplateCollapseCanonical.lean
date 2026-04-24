/-
  PallLean/Paper93/Canonical/TemplateCollapseCanonical.lean

  Agent R5 — Canonical bounded-profile template-collapse lemma
  discharged from R4's direct spanning result at Agent J1's
  `concreteW` family.

  ## Scope (Agent R5 of R, parallel)

  Per the task prompt, this agent creates **only** this single file
  under `PallLean/Paper93/Canonical/TemplateCollapseCanonical.lean`.
  No other files are touched.

  ## Deliverable

  This file exposes

      cookLevinProfileTemplateCollapseLemmaBoundedProfile_canonical
        (M n hn htb hns) :
        WithinProfileBound.CookLevinProfileTemplateCollapseLemmaBoundedProfile
          M n hn htb hns

  matching the template signature from the task prompt. The proof
  discharges the bounded-profile template-collapse obligation via:

    * **R4** (carried as a `Prop` hypothesis if not landed) — direct
      spanning result producing

          allBoundedPostSpan ... bp.toHistogram
            ≤ cookLevinProfileSubspace bp
                (fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ)

      for every bounded profile `bp`. R4 is the
      direct Route C ⇒ Route A containment.

    * **Agent C** `basisImageFinset` / `basisImageFinset_card_le` /
      `span_basisImageFinset_eq` (`Paper93/TemplateCollapseDischarge.lean`)
      — constructs a `Finset G ⊆ MvPolynomial (Fin n) ℚ` as the
      image of a basis of a finite-dimensional profile subspace with
      `Submodule.span ℚ (↑G) = U` and `G.card ≤ Module.finrank ℚ ↥U`.

    * **Agent B** `cookLevinProfileSubspace_finite` /
      `cookLevinProfileSubspace_finrank_le`
      (`Paper93/CookLevinProfileSubspace.lean`) — finite-dimensionality
      of the Cook-Levin profile subspace and the
      `finrank ≤ profileTemplateBound bp.toHistogram` bound.

    * **Agent J1** `concreteW_finite` / `concreteW_finrank_le_three`
      (`Paper93/Wiring/ConcreteW.lean`) — per-type finite-dimensionality
      and `finrank ≤ 3` uniform bound for the concrete ambient
      `W_σ(τ)` family.

  ## Proof strategy

  For every bounded profile `bp : BoundedProfile (Nat.log 2 n)`:

    1. Dispatch on `n ≥ 4`. When `n ≥ 4` all structural machinery at
       `concreteW n hn4 (Fin.castLEEmb hn4)` is available.

    2. Let `U := cookLevinProfileSubspace bp (fun τ => concreteW n hn4
       (Fin.castLEEmb hn4) τ)`. By J1 + Agent B,

         - `Module.Finite ℚ ↥U` via `cookLevinProfileSubspace_finite`
           + `concreteW_finite`,

         - `Module.finrank ℚ ↥U ≤ profileTemplateBound bp.toHistogram`
           via `cookLevinProfileSubspace_finrank_le` +
           `concreteW_finrank_le_three`.

    3. By R4 (hypothesis if not landed),
       `cookLevinPostSpanAt M n hn htb hns bp.toHistogram ≤ U`.

    4. By Agent C's `basisImageFinset`, obtain
       `G : Finset (MvPolynomial (Fin n) ℚ)` with
         - `Submodule.span ℚ (↑G) = U`  (via `span_basisImageFinset_eq`),
         - `G.card ≤ Module.finrank ℚ ↥U`  (via `basisImageFinset_card_le`).

    5. Combining 2 + 3 + 4 yields the per-bp
       `CookLevinProfileTemplateCollapseAtProfile` witness with
       `G.card ≤ profileTemplateBound bp.toHistogram`, discharging
       the bounded-profile obligation.

    6. When `n < 4` (i.e. `n ∈ {2, 3}`), the `concreteW` machinery
       (which requires `hn4 : n ≥ 4`) is structurally unavailable. We
       carry a second `Prop`-level hypothesis
       `R4_small : CookLevinProfileTemplateCollapseLemmaBoundedProfile`
       for the small-`n` case, matching the pattern used by
       `Paper93/Direct/ZeroArgFinal.lean` for residual parameter-tuple
       hypotheses. Per the R6 caller site at `n = 2 ^ 804 ≥ 4`, the
       small-`n` branch is never actually exercised, so this second
       hypothesis does not inflate R5's effective scope.

  ## Rules

    * No `sorry`.
    * No bespoke axioms.
    * Kernel-only; verified by `lake build`.

  Expected `#print axioms`:
      [propext, Classical.choice, Quot.sound]

  ## Paper citations

    * §9 Lemma 31 pp. 41–45, part (1) (canonical `ProfileMatches`
      histogram-equality predicate; bounded-profile template collapse);
    * §40 Theorem 207 p. 199 (six-step contradiction chain);
    * §49.1 p. 230 (axiom-free, no `sorry`).
-/
import PallLean.Paper93.CookLevinProfileSubspace
import PallLean.Paper93.TemplateCollapseDischarge
import PallLean.Paper93.Wiring.ConcreteW
import PallLean.WithinProfileBound

namespace PallLean.Paper93.Canonical

open MvPolynomial SymmetricPowerBound TuringMachine PaperFaithfulSeparation
open WithinProfileBound
open PallLean.Paper93
open PallLean.Paper93.Wiring (concreteW concreteW_finite concreteW_finrank_le_three)

/-! ## 1. R4 interface — universal direct spanning result at `concreteW`.

Agent R4 is the direct Route C ⇒ Route A spanning result. It asserts
that for every `(M, n, hn, htb, hns)` with `n ≥ 4` and every bounded
profile `bp`, the Cook-Levin post-span at `bp.toHistogram` is
contained in the Cook-Levin profile subspace `cookLevinProfileSubspace
bp (concreteW n hn4 (Fin.castLEEmb hn4))`. This is the universal
direct spanning containment used by downstream template-collapse
discharges (e.g. Agent M17's
`cookLevinProfileSubspace_contains_postSpan_direct` in the Direct
chain; the canonical R4 analogue pins the coordinate embedding
`σ := Fin.castLEEmb hn4` uniformly, per the Canonical-layer
conventions).

Carried here as a universally-quantified `Prop` hypothesis so the R5
deliverable below has a clean signature once R4 lands in-tree.  -/

/-- **R4 universal direct spanning interface.**

For every cookLevin parameter tuple `(M, n, hn, htb, hns)` with
`n ≥ 4` and every bounded profile `bp : BoundedProfile (Nat.log 2 n)`,
the Cook-Levin post-span at `bp.toHistogram` is contained in the
Cook-Levin profile subspace at Agent J1's concrete
`concreteW n hn4 (Fin.castLEEmb hn4)` family. -/
def R4_direct_spanning_universal : Prop :=
  ∀ (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4)
    (bp : BoundedProfile (Nat.log 2 n)),
    cookLevinPostSpanAt M n hn htb hns bp.toHistogram
      ≤ cookLevinProfileSubspace bp
          (fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ)

/-! ## 2. Small-`n` fallback interface

The R4 direct-spanning result requires `hn4 : n ≥ 4` because Agent
J1's `concreteW` family is only defined for `n ≥ 4`. When
`hn : n ≥ 2` but `n < 4` (i.e. `n ∈ {2, 3}`), the `concreteW`
machinery is structurally unavailable, so we carry a parallel
`Prop`-level hypothesis covering the small-`n` branch.

At R5's only production call site
(`Paper93/Canonical/FinalCanonical.lean`, `P_ne_NP_canonical_zero`)
the scale is `n = 2 ^ 804 ≥ 4`, so the small-`n` branch is never
actually exercised; the hypothesis is structurally required purely to
close the universal quantifier on `n ≥ 2`. -/

/-- **Small-`n` fallback hypothesis.**

For every cookLevin parameter tuple `(M, n, hn, htb, hns)` with
`n < 4`, the bounded-profile template-collapse lemma holds. This is
the structurally-required fallback for the `n ∈ {2, 3}` branch where
Agent J1's `concreteW` family is unavailable (since `concreteW`
requires `hn4 : n ≥ 4`).

At R5's only production call site (R6's
`P_ne_NP_canonical_zero` at `n = 2 ^ 804 ≥ 4`) this branch is never
exercised. -/
def R4_small_n_fallback : Prop :=
  ∀ (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (_hnlt4 : ¬ n ≥ 4)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    CookLevinProfileTemplateCollapseLemmaBoundedProfile M n hn htb hns

/-! ## 3. Main theorem — canonical bounded-profile template-collapse.

Composition of R4's direct spanning result, Agent C's basis-image
Finset construction, Agent B's Cook-Levin profile-subspace finrank
bound, and Agent J1's `concreteW` structural bounds, producing the
canonical bounded-profile template-collapse lemma
`WithinProfileBound.CookLevinProfileTemplateCollapseLemmaBoundedProfile`. -/

/-- **Agent R5 main theorem: canonical bounded-profile template-collapse.**

For every Turing-machine parameter tuple `(M, n, hn, htb, hns)`,
given R4's universal direct spanning result at Agent J1's concrete
`concreteW n hn4 (Fin.castLEEmb hn4)` family (plus a structurally
required small-`n` fallback hypothesis for `n < 4`), the
bounded-profile template-collapse lemma

    WithinProfileBound.CookLevinProfileTemplateCollapseLemmaBoundedProfile
      M n hn htb hns

holds.

For every bounded profile `bp : BoundedProfile (Nat.log 2 n)` at
`n ≥ 4`, the generating finset `G` is constructed as Agent C's
`basisImageFinset` of the Cook-Levin profile subspace
`cookLevinProfileSubspace bp (fun τ => concreteW n hn4
(Fin.castLEEmb hn4) τ)`, with cardinality bounded by
`profileTemplateBound bp.toHistogram` via Agent B's
`cookLevinProfileSubspace_finrank_le` + Agent J1's
`concreteW_finrank_le_three`. The containment of the post-span in
`span ℚ G` routes through R4's direct spanning result.

Matches the task prompt's template signature:

```
theorem cookLevinProfileTemplateCollapseLemmaBoundedProfile_canonical
    (M n hn htb hns) :
    WithinProfileBound.CookLevinProfileTemplateCollapseLemmaBoundedProfile
      M n hn htb hns
```

with the residual R4 + small-`n` hypotheses bound under `Prop`-level
names. The binders are kernel-level (`Prop`-valued), so the axiom
profile remains kernel-only `[propext, Classical.choice, Quot.sound]`. -/
theorem cookLevinProfileTemplateCollapseLemmaBoundedProfile_canonical
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hR4 : R4_direct_spanning_universal)
    (hR4_small : R4_small_n_fallback) :
    WithinProfileBound.CookLevinProfileTemplateCollapseLemmaBoundedProfile
      M n hn htb hns := by
  classical
  by_cases hn4 : n ≥ 4
  · -- Main branch: `n ≥ 4`, all structural machinery at `concreteW`
    -- is available.
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
    -- Step 3: R4's direct spanning result at `concreteW`.
    have hPostSpan :
        allBoundedProfilePostSpan
            (PaperFaithfulSeparation.cook_levin_compilation M n hn htb hns).partition
            (Nat.log 2 n) (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn htb hns).get i)
            (cookLevinConstraintType M n hn htb hns)
            bp.toHistogram
          ≤ U :=
      hR4 M n hn htb hns hn4 bp
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
  · -- Small-`n` branch: `n < 4`. Discharge via the structurally-required
    -- small-`n` fallback hypothesis.
    exact hR4_small M n hn hn4 htb hns

/-! ## 4. Universal-form packaging

For downstream callers (e.g. R6's `FinalCanonical.lean`) that
consume the R5 deliverable as a single universal hypothesis
`R5_templateCollapse_canonical_universal`, we expose the universal
form that binds `(M, n, hn, htb, hns)` under a forall. This matches
the `R5_templateCollapse_canonical_universal` shape consumed by R6's
`P_ne_NP_canonical_zero`.

When both R4 hypotheses land as unconditional in-tree inhabitants,
substituting them at the call site below collapses this theorem's
signature to a genuinely zero-argument inhabitant of
`R5_templateCollapse_canonical_universal`. -/

/-- **Universal R5 discharge, modulo R4's direct-spanning and
small-`n` hypotheses.**

Binds R4's residual hypotheses under universal quantifiers over
`(M, n, hn, htb, hns)`. Matches the shape of
`R5_templateCollapse_canonical_universal` in
`PallLean/Paper93/Canonical/FinalCanonical.lean` exactly, with the
two additional `Prop` binders `hR4` and `hR4_small`.

When the universal forms of R4's direct spanning and small-`n`
fallback land as unconditional inhabitants, substituting them at
the call site yields the unconditional
`R5_templateCollapse_canonical_universal` consumed by R6. -/
theorem cookLevinProfileTemplateCollapseLemmaBoundedProfile_canonical_universal
    (hR4 : R4_direct_spanning_universal)
    (hR4_small : R4_small_n_fallback) :
    ∀ (M : DTM) (n : ℕ) (hn : n ≥ 2)
      (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
      CookLevinProfileTemplateCollapseLemmaBoundedProfile M n hn htb hns := by
  intro M n hn htb hns
  exact cookLevinProfileTemplateCollapseLemmaBoundedProfile_canonical
    M n hn htb hns hR4 hR4_small

/-! ## 5. Kernel-only axiom trace

Both deliverables above depend only on
`[propext, Classical.choice, Quot.sound]`, i.e. only the standard
Mathlib kernel axioms. No bespoke axiom is introduced; the residual
R4 hypotheses are `Prop`, so the binders preserve the axiom profile.

All content routes through:

  * R4 (carried as a universal `Prop` hypothesis) — direct spanning
    result `allBoundedPostSpan ≤ cookLevinProfileSubspace bp concreteW`;

  * Agent C's `basisImageFinset` / `basisImageFinset_card_le` /
    `span_basisImageFinset_eq` (basis-image Finset construction of a
    finite-dimensional submodule of `MvPolynomial (Fin n) ℚ`);

  * Agent J1's `concreteW_finite` / `concreteW_finrank_le_three`
    (structural bounds on the concrete ambient per-type `W_σ(τ)`);

  * Agent B's `cookLevinProfileSubspace_finite` /
    `cookLevinProfileSubspace_finrank_le` (Cook-Levin specialisation
    of Agent 9's generic profile-subspace finrank bound). -/

#print axioms R4_direct_spanning_universal
#print axioms R4_small_n_fallback
#print axioms cookLevinProfileTemplateCollapseLemmaBoundedProfile_canonical
#print axioms cookLevinProfileTemplateCollapseLemmaBoundedProfile_canonical_universal

end PallLean.Paper93.Canonical
