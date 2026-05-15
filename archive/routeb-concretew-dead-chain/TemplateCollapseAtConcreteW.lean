/-
  PallLean/Paper93/Specialized/TemplateCollapseAtConcreteW.lean
  ============================================================================

  Agent L1 of 5 (parallel) — **Specialised** discharge of
  `WithinProfileBound.CookLevinProfileTemplateCollapseLemmaBoundedProfile`
  routed through Agent J1's concrete `concreteW` family *only*
  (no universal-over-`W` quantification).

  ## Scope

  Paper §9 Lemma 31 asserts "there exists `V_h` with
  `finrank V_h ≤ ∏_τ C(h τ + 2, 2)` containing the post-span".
  The universal chain (`Paper93/FinalDischarge.lean` →
  `Paper93/Closure/UnconditionalSpanning.lean` →
  `Paper93/Spanning/Composition.lean`) exposes a
  `CookLevinProfileTemplateCollapseLemmaBoundedProfile`-discharge that
  quantifies over *every* abstract per-type family
  `W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ)` with
  `dim (W τ) ≤ 3`, via the universal spanning package
  `CookLevinPerTypeSpanning_universal` of Agent I6 / J2.

  This file performs the **paper-faithful specialisation**: we take
  `V_h := cookLevinProfileSubspace bp (fun τ => concreteW n hn4 σ τ)`
  with Agent J1's concrete `concreteW` family at a specific
  coordinate embedding `σ : Fin 4 ↪ Fin n`, and construct the
  generating finset `G` directly as a basis of this profile subspace
  via
  `WithinProfileBound.finite_submodule_le_span_finset_card_le_finrank`.
  The cardinality bound
  `G.card ≤ profileTemplateBound bp.toHistogram` is then obtained by
  composing

    * Agent 9's generic profile-subspace finrank bound
      `PallLean.Paper93.profileSubspace_finrank_bound`
      (`Paper93/TensorDimBound.lean`, commit `e92fc29`);

    * Agent B's Cook-Levin specialisation
      `PallLean.Paper93.cookLevinProfileSubspace_finrank_le`
      (`Paper93/CookLevinProfileSubspace.lean`, commit `3c20a56`);

    * Agent H2's ambient per-type finrank bound exposed by Agent J1
      as `concreteW_finrank_le_three`
      (`Paper93/Wiring/ConcreteW.lean`, commit `b36a8b1`), together
      with the matching finiteness instance `concreteW_finite`.

  The spanning property
  `allBoundedProfilePostSpan … ≤ cookLevinProfileSubspace bp
     (concreteW n hn4 σ)` is the paper-faithful per-concreteW
  containment content. In the current repository it is not
  zero-argument at `concreteW`: the universal per-type spanning
  package
  `PallLean.Paper93.Spanning.CookLevinPerTypeSpanning`
  (a direct consequence of Agent H3's unconditional factor membership
  combined with Agent H4's derivative-closure submodule and Agent
  I5's per-type shift/mlProj closure — see commits `34e3af5`,
  `8fba527`, `6e6712c` / `85b472d` / `295e346`) is the exact
  paper-faithful analytic content delivering this containment. We
  therefore take this per-`σ`, per-`concreteW` spanning package as
  the **single residual hypothesis** of the theorem below; it is
  *not* universal-over-`W`, matching this file's specialisation
  target.

  ## What this file delivers

  **`cookLevinProfileTemplateCollapseLemmaBoundedProfile_at_concreteW_discharged`**.

  For every `(M : DTM)`, `(n : ℕ)` with `n ≥ 2` and `n ≥ 4`,
  `M.timeBound ≤ 4`, `M.numStates ≤ n`, every coordinate embedding
  `σ : Fin 4 ↪ Fin n`, and every inhabitant of the per-`σ`
  per-`concreteW` spanning Prop
  `CookLevinPerTypeSpanning M n hn htb hns (concreteW n hn4 σ)`,
  the bounded-profile template-collapse lemma
  `WithinProfileBound.CookLevinProfileTemplateCollapseLemmaBoundedProfile`
  holds. The proof constructs the generating finset `G` at each
  bounded profile `bp` directly as a basis of
  `cookLevinProfileSubspace bp (concreteW n hn4 σ)`, bounded by
  `profileTemplateBound bp.toHistogram` via Agent B + Agent 9 +
  Agent J1.

  ## Why this is *paper-faithful* specialisation

    * We never use the universal-over-`W` package
      `CookLevinPerTypeSpanning_universal`; only the
      per-`concreteW`, per-`σ` instance `CookLevinPerTypeSpanning …
      (concreteW n hn4 σ)` is consumed.

    * The ambient per-type family is Agent J1's concrete `concreteW`
      rather than an abstract hypothesised `W`: the finiteness and
      `dim ≤ 3` structural bounds are supplied directly by
      `concreteW_finite` and `concreteW_finrank_le_three`, no F5
      universal package invoked.

    * The generating finset `G` is constructed AT `concreteW` as a
      basis of `cookLevinProfileSubspace bp (concreteW n hn4 σ)`;
      its cardinality is bounded by
      `finrank (cookLevinProfileSubspace bp (concreteW n hn4 σ)) ≤
       profileTemplateBound bp.toHistogram` via Agent B's
      `cookLevinProfileSubspace_finrank_le` specialised at
      `W := concreteW n hn4 σ`.

  ## Rules

    * **No `sorry`.**
    * **Kernel-only** — no bespoke axioms.
    * **Verified by `lake build`.**
    * Only this file is touched (Agent L1 of 5, parallel scope).
    * Not fully unconditional: takes one residual hypothesis
      (`CookLevinPerTypeSpanning … (concreteW n hn4 σ)`), which is
      the paper-faithful per-concreteW analytic content, *not* the
      universal-over-`W` package.

  Expected `#print axioms`:
      `[propext, Classical.choice, Quot.sound]`
-/

import PallLean.Paper93.CookLevinProfileSubspace
import PallLean.Paper93.Spanning.Composition
import PallLean.Paper93.Wiring.ConcreteW
import PallLean.WithinProfileBound

namespace PallLean
namespace Paper93
namespace Specialized

open TuringMachine MvPolynomial WithinProfileBound
open PaperFaithfulSeparation SymmetricPowerBound
open PallLean.Paper93
open PallLean.Paper93.Spanning
open PallLean.Paper93.Wiring (concreteW concreteW_finite concreteW_finrank_le_three)

/-! ## Paper §9 Lemma 31 at Agent J1's `concreteW`

Paper §9 Lemma 31: "there exists `V_h` of finrank
≤ `∏_τ C(h τ + 2, 2)` containing the post-span at profile `h`".

For the bounded-profile histogram `bp.toHistogram` we take

  `V_bp := cookLevinProfileSubspace bp (concreteW n hn4 σ)`

and construct the generating finset `G` as a finite basis of `V_bp`
(via `finite_submodule_le_span_finset_card_le_finrank`). The
cardinality bound on `G` falls out by composing Agent B's
`cookLevinProfileSubspace_finrank_le` with Agent J1's
`concreteW_finrank_le_three`.

The spanning property `postSpan ≤ span G` routes through
`cookLevinProfileSubspace_contains_postSpan_at_bp` applied to the
per-`σ` per-`concreteW` `CookLevinPerTypeSpanning` package taken as
the single residual hypothesis of this theorem. -/

/-- **Paper §9 Lemma 31 — specialised per-`bp` discharge at
    `concreteW`.**

For a fixed coordinate embedding `σ : Fin 4 ↪ Fin n` and the
per-`σ` per-`concreteW` spanning package, exhibit the
`CookLevinProfileTemplateCollapseAtProfile` witness at
`bp.toHistogram` with the generating finset `G` taken as a basis of
`cookLevinProfileSubspace bp (concreteW n hn4 σ)` and cardinality
bound obtained via Agent B + Agent 9 + Agent J1.

This is the per-profile ingredient of the bounded-profile
template-collapse lemma; the full lemma
`cookLevinProfileTemplateCollapseLemmaBoundedProfile_at_concreteW_discharged`
below is obtained by quantifying over `bp`. -/
theorem cookLevinProfileTemplateCollapseAtProfile_at_concreteW_discharged
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2) (hn4 : n ≥ 4)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (σ : Fin 4 ↪ Fin n)
    (hSpan :
      CookLevinPerTypeSpanning M n hn htb hns
        (fun τ => concreteW n hn4 σ τ))
    (bp : BoundedProfile (Nat.log 2 n)) :
    CookLevinProfileTemplateCollapseAtProfile M n hn htb hns
      bp.toHistogram := by
  classical
  -- Structural data for the concrete per-type family `concreteW`:
  have hW_fin :
      ∀ τ, Module.Finite ℚ ↥(concreteW n hn4 σ τ) :=
    fun τ => concreteW_finite n hn4 σ τ
  have hW_dim :
      ∀ τ, Module.finrank ℚ ↥(concreteW n hn4 σ τ) ≤ 3 :=
    fun τ => concreteW_finrank_le_three n hn4 σ τ
  -- Per-bp post-span containment via the per-concreteW spanning
  -- package (Agent H5's composition lemma).
  have hPostSpan :
      cookLevinPostSpanAt M n hn htb hns bp.toHistogram
        ≤ cookLevinProfileSubspace bp (fun τ => concreteW n hn4 σ τ) :=
    cookLevinProfileSubspace_contains_postSpan_at_bp
      M n hn htb hns (fun τ => concreteW n hn4 σ τ) hSpan bp
  -- Feed to Agent B's per-profile bridge, which constructs the
  -- template-collapse witness `G` directly from a basis of
  -- `cookLevinProfileSubspace bp concreteW`. Agent B's
  -- `cookLevinProfileTemplateCollapseAtProfile_of_bridge` proof
  -- invokes `finite_submodule_le_span_finset_card_le_finrank` on
  -- `cookLevinProfileSubspace bp (concreteW n hn4 σ)` to produce
  -- the finite basis `G`, then caps `G.card` by the profile
  -- subspace's finrank which is bounded by
  -- `profileTemplateBound bp.toHistogram` via
  -- `cookLevinProfileSubspace_finrank_le`.
  exact cookLevinProfileTemplateCollapseAtProfile_of_bridge
    M n hn htb hns bp
    (fun τ => concreteW n hn4 σ τ)
    hW_fin hW_dim hPostSpan

/-- **Paper §9 Lemma 31 — specialised bounded-profile discharge at
    `concreteW`.**

For a fixed coordinate embedding `σ : Fin 4 ↪ Fin n` and the
per-`σ` per-`concreteW` spanning package, the bounded-profile
template-collapse lemma
`WithinProfileBound.CookLevinProfileTemplateCollapseLemmaBoundedProfile`
holds. The generating finset at each bounded profile `bp` is taken
as a basis of `cookLevinProfileSubspace bp (concreteW n hn4 σ)`,
with cardinality bounded by `profileTemplateBound bp.toHistogram`
via Agent B's `cookLevinProfileSubspace_finrank_le` composed with
Agent J1's `concreteW_finrank_le_three` (= Agent 9's generic
profile-subspace finrank bound at `dim = 3`).

This is a **paper-faithful specialisation**: no
universal-over-`W` quantifier is invoked; only the per-`σ`
per-`concreteW` spanning instance is consumed.

  * `hSpan : CookLevinPerTypeSpanning M n hn htb hns (concreteW n
    hn4 σ)` — the per-`concreteW` per-`σ` paper-faithful spanning
    content (H3 + H4 + I5 at `concreteW`).

The theorem is *not* fully unconditional: the residual hypothesis
`hSpan` is the paper-faithful per-concreteW analytic content
(H3 unconditional factor membership + H4 derivative closure + I5
shift-mlproj closure, composed at `concreteW`). It is *not*
universal-over-`W`, matching this file's specialisation target.

Axiom profile: kernel-only
`[propext, Classical.choice, Quot.sound]`. -/
theorem cookLevinProfileTemplateCollapseLemmaBoundedProfile_at_concreteW_discharged
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2) (hn4 : n ≥ 4)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (σ : Fin 4 ↪ Fin n)
    (hSpan :
      CookLevinPerTypeSpanning M n hn htb hns
        (fun τ => concreteW n hn4 σ τ)) :
    WithinProfileBound.CookLevinProfileTemplateCollapseLemmaBoundedProfile
      M n hn htb hns := by
  intro bp
  exact cookLevinProfileTemplateCollapseAtProfile_at_concreteW_discharged
    M n hn hn4 htb hns σ hSpan bp

/-! ## Convenience variant at the canonical `σ = Fin.castLEEmb hn4`

For callers that want to fix `σ` canonically (matching Agent H8's
`F5_universal` and Agent K2's `P_ne_NP_truly_zero`), we expose a
convenience alias with `σ := Fin.castLEEmb hn4`. -/

/-- **Canonical-`σ` alias.**

Variant of
`cookLevinProfileTemplateCollapseLemmaBoundedProfile_at_concreteW_discharged`
with `σ := Fin.castLEEmb hn4` fixed to the canonical coordinate
embedding (matching Agent H8's `F5_universal` and Agent K2's
`P_ne_NP_truly_zero`). The residual spanning hypothesis is the
per-canonical-`σ` per-`concreteW` spanning package. -/
theorem cookLevinProfileTemplateCollapseLemmaBoundedProfile_at_concreteW_castLEEmb_discharged
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2) (hn4 : n ≥ 4)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hSpan :
      CookLevinPerTypeSpanning M n hn htb hns
        (fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ)) :
    WithinProfileBound.CookLevinProfileTemplateCollapseLemmaBoundedProfile
      M n hn htb hns :=
  cookLevinProfileTemplateCollapseLemmaBoundedProfile_at_concreteW_discharged
    M n hn hn4 htb hns (Fin.castLEEmb hn4) hSpan

-- **Axiom audit** — expected: kernel-only
-- `[propext, Classical.choice, Quot.sound]`.
#print axioms cookLevinProfileTemplateCollapseAtProfile_at_concreteW_discharged
#print axioms cookLevinProfileTemplateCollapseLemmaBoundedProfile_at_concreteW_discharged
#print axioms cookLevinProfileTemplateCollapseLemmaBoundedProfile_at_concreteW_castLEEmb_discharged

end Specialized
end Paper93
end PallLean
