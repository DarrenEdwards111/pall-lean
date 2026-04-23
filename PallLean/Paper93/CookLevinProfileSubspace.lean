/-
  CookLevinProfileSubspace.lean — Cook-Levin-specific bridge to Agent 9's
  profile subspace dimension bound.

  Agent B (of 5, parallel) bridge layer (paper §9 Lemma 31 specialisation):

  Agent 9 (PallLean.Paper93.TensorDimBound) provided the generic profile
  subspace dimension bound

    `profileSubspace_finrank_bound`
      : finrank ℚ (profileSubspace h W) ≤ ∏_σ C(h σ + 2, 2)

  for any family `W : Iface → Submodule ℚ (MvPolynomial (Fin N) ℚ)` with
  `dim (W σ) ≤ 3`.

  This file specialises that bound to the Cook-Levin setting: `Iface` is
  `ConstraintType`, the profile is `bp.toHistogram` for some
  `bp : BoundedProfile (Nat.log 2 n)`, and the concrete container for
  `allBoundedProfilePostSpan` of the Cook-Levin factor list at profile
  `bp.toHistogram` is built from the generic `profileSubspace`.

  ## Faithfulness disclaimer

  The real-interface shared-W family `W_σ` at paper target dimension
  ≤ 3 is structurally unavailable in the uniform polynomial basis at
  `n ≥ 4` for the booleanity type (see WithinProfileBound.lean §27 and
  `cookLevinQ_interfaceTypeSpace_finrank_bound_shared_abstract`). Agent A
  has NOT (yet) published a concrete `realInterfaceSpace` family in repo.

  We therefore take the `W_σ` family **as a variable hypothesis**:
  every theorem below parametrises over
  `W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ)` with
  `dim (W σ) ≤ 3`. This matches the abstract-family signature already
  present in `WithinProfileBound.CookLevinSharedInterfaceTypeFinrankBound`.

  The spanning theorem `cookLevinProfileSubspace_contains_postSpan` is
  likewise stated as a **hypothesized frontier**: it takes the explicit
  containment as an abstract premise, and discharges the Cook-Levin
  side of the bridge by combining it with Agent 9's generic bound.
-/
import PallLean.Paper93.TensorDimBound
import PallLean.WithinProfileBound

open Module
open scoped BigOperators

namespace PallLean
namespace Paper93

open MvPolynomial SymmetricPowerBound TuringMachine PaperFaithfulSeparation
open WithinProfileBound

/-! ## Abbreviation for the Cook-Levin post-span

We introduce a local abbreviation so the large polymorphic expression
`allBoundedProfilePostSpan ...` is not re-elaborated at every call
site (avoiding heartbeat blow-ups during type checking). -/

/-- Abbreviation for the concrete Cook-Levin
`allBoundedProfilePostSpan` at a given profile histogram. -/
noncomputable abbrev cookLevinPostSpanAt
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (h : ProfileHistogram) :
    Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
  allBoundedProfilePostSpan
    (PaperFaithfulSeparation.cook_levin_compilation M n hn htb hns).partition
    (Nat.log 2 n) (Nat.log 2 n)
    (fun i => (cookLevinFactorList M n hn htb hns).get i)
    (cookLevinConstraintType M n hn htb hns)
    h

/-! ## The Cook-Levin specialisation of Agent 9's profile subspace -/

/-- **Cook-Levin profile subspace.**

    Specialisation of Agent 9's generic `profileSubspace` to the
    Cook-Levin setting: the index family `Iface` is `ConstraintType`,
    the profile is `bp.toHistogram`, and the per-interface family
    `W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ)` is
    supplied as a hypothesis (Agent A's `realInterfaceSpace` not yet
    in repo).

    By construction this is the submodule
    `span { ∏_τ f τ | f τ ∈ Sym^{bp.toHistogram τ}(W τ) }`,
    matching the paper's §9 Lemma 31 target. -/
noncomputable def cookLevinProfileSubspace {n : ℕ}
    (bp : BoundedProfile (Nat.log 2 n))
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ)) :
    Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
  profileSubspace bp.toHistogram W

/-! ## Finite-dimensionality of the Cook-Levin profile subspace

Agent 9's `profileSubspace_le_profileSymProd_span` exhibits the profile
subspace as contained in the span of a finite family. Combined with
finite-dimensional hypotheses on the `W_σ`, this gives
`Module.Finite` for `cookLevinProfileSubspace`. -/

theorem cookLevinProfileSubspace_finite {n : ℕ}
    (bp : BoundedProfile (Nat.log 2 n))
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (hW_fin : ∀ τ, Module.Finite ℚ ↥(W τ)) :
    Module.Finite ℚ ↥(cookLevinProfileSubspace bp W) := by
  classical
  unfold cookLevinProfileSubspace profileSubspace
  set d : ConstraintType → ℕ := fun τ => Module.finrank ℚ ↥(W τ) with hd_def
  let b : ∀ τ, Module.Basis (Fin (d τ)) ℚ ↥(W τ) :=
    fun τ => Module.finBasis ℚ ↥(W τ)
  have hle :
      profileSubspace bp.toHistogram W ≤
        Submodule.span ℚ
          (Set.range (profileSymProd W b : ProfileIndex bp.toHistogram d → _)) :=
    profileSubspace_le_profileSymProd_span W b
  haveI hfin_big : Module.Finite ℚ
      ↥(Submodule.span ℚ
        (Set.range (profileSymProd W b : ProfileIndex bp.toHistogram d → _))) := by
    apply Module.Finite.span_of_finite
    exact Set.finite_range _
  exact Module.Finite.of_injective
    ((Submodule.inclusion hle) : _ →ₗ[ℚ] _)
    (Submodule.inclusion_injective hle)

/-! ## Dim bound via Agent 9

Agent 9's `profileSubspace_finrank_bound` transports directly to the
Cook-Levin specialisation. The RHS `∏_τ C(bp.toHistogram τ + 2, 2)`
is exactly `profileTemplateBound bp.toHistogram` from
`WithinProfileBound.lean`. -/

/-- **Dimension bound (Agent 9 application).**

    Under the hypothesis `dim (W τ) ≤ 3`, the Cook-Levin profile
    subspace has finrank bounded by the paper's literal template count
    `profileTemplateBound bp.toHistogram = ∏_τ C(bp.toHistogram τ + 2, 2)`. -/
theorem cookLevinProfileSubspace_finrank_le
    {n : ℕ}
    (bp : BoundedProfile (Nat.log 2 n))
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (hW_fin : ∀ τ, Module.Finite ℚ ↥(W τ))
    (hW_dim : ∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3) :
    Module.finrank ℚ (cookLevinProfileSubspace bp W) ≤
      profileTemplateBound bp.toHistogram := by
  classical
  unfold cookLevinProfileSubspace
  have hbound :=
    profileSubspace_finrank_bound (Iface := ConstraintType)
      bp.toHistogram W hW_fin hW_dim
  -- `profileTemplateBound h = ∏_τ C(h τ + 2, 2)` by definition.
  have hrhs :
      (∏ τ : ConstraintType, Nat.choose (bp.toHistogram τ + 2) 2)
        = profileTemplateBound bp.toHistogram := rfl
  simpa [hrhs] using hbound

/-! ## Containment: abstract hypothesis version

The concrete containment
`allBoundedProfilePostSpan ... bp.toHistogram ≤ cookLevinProfileSubspace bp W`
requires a paper-faithful argument combining:

  1. For each factor index `i` of type `τ`, the differentiated atoms of
     factor `i` lie in `Sym^{≤ h τ}(W τ)` (Agent A's per-interface
     identification).
  2. Multilinear expansion: products of such atoms assemble into
     `∏_τ Sym^{h τ}(W τ)`, i.e. `profileSubspace h W`.

Neither piece is yet in repo at the concrete Cook-Levin factor list.
We therefore expose the containment as a hypothesized premise below. -/

/-- **Hypothesised containment bridge.**

    Given an explicit containment hypothesis `hPostSpan`, the Cook-Levin
    `allBoundedProfilePostSpan` at profile `bp.toHistogram` is contained
    in the Cook-Levin profile subspace.

    The hypothesis formalises the concrete Cook-Levin side of the paper's
    §9 Lemma 31 bridge, namely that every differentiated classified-set
    generator `mlProj (shift * ∏_i iterDerivList (d i) (f i))` with
    derivative-count profile equal to `bp.toHistogram` lies in
    `∏_τ Sym^{bp.toHistogram τ}(W τ)`. -/
theorem cookLevinProfileSubspace_contains_postSpan_of_hypothesis
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (bp : BoundedProfile (Nat.log 2 n))
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (hPostSpan :
      cookLevinPostSpanAt M n hn htb hns bp.toHistogram
        ≤ cookLevinProfileSubspace bp W) :
    cookLevinPostSpanAt M n hn htb hns bp.toHistogram
      ≤ cookLevinProfileSubspace bp W :=
  hPostSpan

/-! ## Combined bridge: containment hypothesis + Agent 9 bound

Chaining the hypothesised containment with Agent 9's dim bound yields
the Cook-Levin-specific finrank bound for the actual Cook-Levin
`allBoundedProfilePostSpan`. -/

/-- **Cook-Levin post-span finrank bound** (combined bridge).

    Under the two hypotheses
      * `hW_dim` : `dim (W τ) ≤ 3` for each constraint type τ;
      * `hPostSpan` : the concrete Cook-Levin post-span at profile
        `bp.toHistogram` is contained in `cookLevinProfileSubspace bp W`;
    the Cook-Levin `allBoundedProfilePostSpan` at profile `bp.toHistogram`
    has finrank ≤ `profileTemplateBound bp.toHistogram`. -/
theorem cookLevin_allBoundedProfilePostSpan_finrank_le_of_bridge
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (bp : BoundedProfile (Nat.log 2 n))
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (hW_fin : ∀ τ, Module.Finite ℚ ↥(W τ))
    (hW_dim : ∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3)
    (hPostSpan :
      cookLevinPostSpanAt M n hn htb hns bp.toHistogram
        ≤ cookLevinProfileSubspace bp W) :
    Module.finrank ℚ
        ↥(cookLevinPostSpanAt M n hn htb hns bp.toHistogram)
      ≤ profileTemplateBound bp.toHistogram := by
  classical
  haveI hfin_V : Module.Finite ℚ ↥(cookLevinProfileSubspace bp W) :=
    cookLevinProfileSubspace_finite bp W hW_fin
  have hmono :
      Module.finrank ℚ
          ↥(cookLevinPostSpanAt M n hn htb hns bp.toHistogram)
        ≤ Module.finrank ℚ ↥(cookLevinProfileSubspace bp W) :=
    Submodule.finrank_mono hPostSpan
  exact le_trans hmono
    (cookLevinProfileSubspace_finrank_le bp W hW_fin hW_dim)

/-! ## Final packaging: template-collapse bridge via explicit family

Packaging the above into the shape required by
`CookLevinProfileTemplateCollapseLemmaBoundedProfile`: for each
`bp : BoundedProfile (Nat.log 2 n)`, exhibit a finite family `G`
spanning the Cook-Levin post-span at `bp.toHistogram` with
`G.card ≤ profileTemplateBound bp.toHistogram`. -/

/-- **Final bridge: bounded-profile template collapse from the abstract
    `W_τ` hypothesis + containment hypothesis.** -/
theorem cookLevinProfileTemplateCollapseAtProfile_of_bridge
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (bp : BoundedProfile (Nat.log 2 n))
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (hW_fin : ∀ τ, Module.Finite ℚ ↥(W τ))
    (hW_dim : ∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3)
    (hPostSpan :
      cookLevinPostSpanAt M n hn htb hns bp.toHistogram
        ≤ cookLevinProfileSubspace bp W) :
    CookLevinProfileTemplateCollapseAtProfile M n hn htb hns bp.toHistogram := by
  classical
  haveI hfin_V : Module.Finite ℚ ↥(cookLevinProfileSubspace bp W) :=
    cookLevinProfileSubspace_finite bp W hW_fin
  rcases finite_submodule_le_span_finset_card_le_finrank
    (cookLevinProfileSubspace bp W) with ⟨G, hGspan, hGcard⟩
  refine ⟨G, ?_, ?_⟩
  · exact le_trans hPostSpan hGspan
  · exact le_trans hGcard
      (cookLevinProfileSubspace_finrank_le bp W hW_fin hW_dim)

/-- **Universal (all-bounded-profiles) bridge.**

    Discharging `CookLevinProfileTemplateCollapseLemmaBoundedProfile`
    from:
      * a per-type `W_τ` family with `dim ≤ 3`;
      * a per-bounded-profile containment
        `allBoundedProfilePostSpan ... bp.toHistogram ≤
         cookLevinProfileSubspace bp W` for every `bp`. -/
theorem cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_bridge
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (hW_fin : ∀ τ, Module.Finite ℚ ↥(W τ))
    (hW_dim : ∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3)
    (hPostSpan :
      ∀ bp : BoundedProfile (Nat.log 2 n),
        cookLevinPostSpanAt M n hn htb hns bp.toHistogram
          ≤ cookLevinProfileSubspace bp W) :
    CookLevinProfileTemplateCollapseLemmaBoundedProfile M n hn htb hns := by
  intro bp
  exact cookLevinProfileTemplateCollapseAtProfile_of_bridge
    M n hn htb hns bp W hW_fin hW_dim (hPostSpan bp)

#print axioms cookLevinProfileSubspace_finrank_le
#print axioms cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_bridge

end Paper93
end PallLean
