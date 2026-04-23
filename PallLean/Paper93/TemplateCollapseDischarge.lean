/-
  PallLean/Paper93/TemplateCollapseDischarge.lean

  Paper §9 Lemma 31 — Route C ⇒ Route A.

  Discharge of `WithinProfileBound.CookLevinProfileTemplateCollapseLemmaBoundedProfile`
  from an Agent-B–style "profile subspace" family
  `cookLevinProfileSubspace M n ... bp` satisfying:

    * `allBoundedProfilePostSpan ... bp.toHistogram ≤ cookLevinProfileSubspace M n ... bp`
    * `Module.Finite ℚ ↥(cookLevinProfileSubspace M n ... bp)`
    * `Module.finrank ℚ ↥(cookLevinProfileSubspace M n ... bp) ≤
          profileTemplateBound bp.toHistogram`

  The discharge proceeds by picking a finite basis of the (finite-dimensional)
  profile subspace. The images of the basis vectors under the inclusion form a
  Finset `G ⊆ MvPolynomial (Fin n) ℚ` with
    * `G.card = Module.finrank ℚ (cookLevinProfileSubspace ... bp)
              ≤ profileTemplateBound bp.toHistogram`
    * `Submodule.span ℚ G = cookLevinProfileSubspace ... bp`, hence
      `allBoundedProfilePostSpan ... ≤ cookLevinProfileSubspace ... = span ℚ G`.

  This file does NOT modify any existing file. It only *consumes* the
  (agent-B) profile-subspace hypotheses as explicit arguments; when Agent B
  lands its concrete construction in `PallLean.WithinProfileBound`, the
  theorem proved here specialises unconditionally via a one-line
  `from cookLevinProfileSubspace_contains_postSpan ... ...`.
-/
import PallLean.WithinProfileBound
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Tactic

open Module
open scoped BigOperators

namespace PallLean
namespace Paper93

open TuringMachine MvPolynomial WithinProfileBound

/-! ## Finset G of basis-image polynomials

Given a ℚ-submodule `U ⊆ MvPolynomial (Fin n) ℚ` that is finite-dimensional
as a ℚ-module, we build a Finset `G : Finset (MvPolynomial (Fin n) ℚ)` whose
cardinality equals `finrank ℚ ↥U` and whose ℚ-span (inside the ambient
`MvPolynomial (Fin n) ℚ`) equals `U`.

The construction: take `d := finrank ℚ ↥U`, pick a `Module.Basis (Fin d)` of
`↥U`, map each basis vector through the subtype coercion, and finally
image `Finset.univ : Finset (Fin d)`.

These lemmas are generic, depending only on `U : Submodule ℚ M` with
`Module.Finite ℚ ↥U`. They are the structural core of the discharge below.
-/

/-- Basis-image Finset for a finite-dimensional ℚ-submodule `U` of a larger
`MvPolynomial (Fin n) ℚ`. Each element is the ambient-space image of a
basis vector of `↥U`. -/
noncomputable def basisImageFinset {n : ℕ}
    (U : Submodule ℚ (MvPolynomial (Fin n) ℚ))
    [Module.Finite ℚ ↥U] :
    Finset (MvPolynomial (Fin n) ℚ) :=
  (Finset.univ : Finset (Fin (Module.finrank ℚ ↥U))).image
    (fun i => ((Module.finBasis ℚ (↥U)) i : MvPolynomial (Fin n) ℚ))

/-- The cardinality of `basisImageFinset U` is at most `finrank ℚ ↥U`. -/
theorem basisImageFinset_card_le {n : ℕ}
    (U : Submodule ℚ (MvPolynomial (Fin n) ℚ))
    [Module.Finite ℚ ↥U] :
    (basisImageFinset U).card ≤ Module.finrank ℚ ↥U := by
  classical
  unfold basisImageFinset
  refine le_trans (Finset.card_image_le) ?_
  simp

/-- The ℚ-span of the basis-image Finset equals the submodule `U`. -/
theorem span_basisImageFinset_eq {n : ℕ}
    (U : Submodule ℚ (MvPolynomial (Fin n) ℚ))
    [hfin : Module.Finite ℚ ↥U] :
    Submodule.span ℚ
        (↑(basisImageFinset U) : Set (MvPolynomial (Fin n) ℚ)) = U := by
  classical
  set d := Module.finrank ℚ ↥U with hd_def
  set b : Module.Basis (Fin d) ℚ (↥U) := Module.finBasis ℚ (↥U) with hb_def
  -- Coe of Finset.image is Set.image of coe.
  have hcoe :
      (↑(basisImageFinset U) : Set (MvPolynomial (Fin n) ℚ))
      = Set.range (fun i : Fin d => (b i : MvPolynomial (Fin n) ℚ)) := by
    unfold basisImageFinset
    rw [Finset.coe_image]
    ext y
    constructor
    · rintro ⟨i, _, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, by simp, rfl⟩
  rw [hcoe]
  -- Show the two spans agree: `span (range (coe ∘ b)) = U`.
  apply le_antisymm
  · -- ≤ : each `b i` (as an element of the ambient space) lies in `U`.
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact (b i).2
  · -- ⊇ : every `u ∈ U` is in the span.
    -- Any `x ∈ ↥U` lies in `Submodule.span ℚ (Set.range b)` (Basis.span_eq).
    intro x hx
    -- Use: for `u : ↥U`, `(u : M) ∈ Submodule.span ℚ (range (coe ∘ b))`.
    -- We proceed by restricting to `↥U` and using `Basis.mem_span`.
    -- Apply `Submodule.span_subtype_mono` style via `Submodule.map`.
    set f : ↥U →ₗ[ℚ] MvPolynomial (Fin n) ℚ := U.subtype with hf_def
    have hU_eq : U = Submodule.map f (⊤ : Submodule ℚ ↥U) := by
      simp [hf_def]
    -- Reduce the statement `x ∈ ...` to `⟨x, hx⟩ ∈ map f ⊤`.
    have hx' : (⟨x, hx⟩ : ↥U) ∈ (⊤ : Submodule ℚ ↥U) := Submodule.mem_top
    -- `⊤ = span (range b)` for the basis `b`, and map distributes over span.
    have h_top : (⊤ : Submodule ℚ ↥U) = Submodule.span ℚ (Set.range b) :=
      (b.span_eq).symm
    rw [h_top] at hx'
    -- `map f (span (range b)) = span (range (f ∘ b))` = span (range (coe ∘ b)).
    have h_map :
        Submodule.map f (Submodule.span ℚ (Set.range b))
          = Submodule.span ℚ (f '' Set.range b) :=
      Submodule.map_span f (Set.range b)
    have h_image :
        (f '' Set.range b)
          = Set.range (fun i : Fin d => (b i : MvPolynomial (Fin n) ℚ)) := by
      ext y
      constructor
      · rintro ⟨u, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨b i, ⟨i, rfl⟩, rfl⟩
    -- Now transport `hx'` through `Submodule.mem_map`.
    have : x ∈ Submodule.map f (Submodule.span ℚ (Set.range b)) := by
      refine ⟨⟨x, hx⟩, hx', ?_⟩
      simp [hf_def]
    rw [h_map, h_image] at this
    exact this

/-! ## Route C ⇒ Route A: the bounded-profile template-collapse discharge

Given an Agent-B–style profile-subspace family, the bounded-profile
template-collapse obligation is discharged by choosing, for each bounded
profile `bp`, the basis-image Finset of the profile subspace. -/

/-- **Route C ⇒ Route A, bounded-profile template-collapse discharge**
(agent-B hypothesis form).

Given:

  * a (possibly noncomputable) family `cookLevinProfileSubspace`
    assigning to each bounded profile a ℚ-submodule of
    `MvPolynomial (Fin n) ℚ`;
  * a containment hypothesis: the corresponding
    `allBoundedProfilePostSpan` slice sits inside the subspace;
  * a finite-dimensionality hypothesis on each subspace;
  * a finrank hypothesis: the subspace dimension is bounded by the
    paper's per-profile template count
    `profileTemplateBound bp.toHistogram = ∏_τ C(bp.toHistogram τ + 2, 2)`

we conclude `CookLevinProfileTemplateCollapseLemmaBoundedProfile M n hn htb hns`:
for every bounded profile `bp`, there exists a Finset
`G : Finset (MvPolynomial (Fin n) ℚ)` with
  * `allBoundedProfilePostSpan ... bp.toHistogram ≤ Submodule.span ℚ G`;
  * `G.card ≤ profileTemplateBound bp.toHistogram`.

The Finset `G` is taken to be the image of a finite basis of the profile
subspace. -/
theorem cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_profileSubspace
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (cookLevinProfileSubspace :
      BoundedProfile (Nat.log 2 n) → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (cookLevinProfileSubspace_finite :
      ∀ bp : BoundedProfile (Nat.log 2 n),
        Module.Finite ℚ ↥(cookLevinProfileSubspace bp))
    (cookLevinProfileSubspace_contains_postSpan :
      ∀ bp : BoundedProfile (Nat.log 2 n),
        allBoundedProfilePostSpan
            (PaperFaithfulSeparation.cook_levin_compilation M n hn htb hns).partition
            (Nat.log 2 n) (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn htb hns).get i)
            (cookLevinConstraintType M n hn htb hns)
            bp.toHistogram
          ≤ cookLevinProfileSubspace bp)
    (cookLevinProfileSubspace_finrank_le :
      ∀ bp : BoundedProfile (Nat.log 2 n),
        Module.finrank ℚ ↥(cookLevinProfileSubspace bp)
          ≤ profileTemplateBound bp.toHistogram) :
    CookLevinProfileTemplateCollapseLemmaBoundedProfile M n hn htb hns := by
  classical
  intro bp
  -- Pick the basis-image Finset of the profile subspace `U := cookLevinProfileSubspace bp`.
  have hfin : Module.Finite ℚ ↥(cookLevinProfileSubspace bp) :=
    cookLevinProfileSubspace_finite bp
  -- Build G as the image of a basis of `cookLevinProfileSubspace bp`.
  let U : Submodule ℚ (MvPolynomial (Fin n) ℚ) := cookLevinProfileSubspace bp
  have hU_fin : Module.Finite ℚ ↥U := hfin
  let G : Finset (MvPolynomial (Fin n) ℚ) := @basisImageFinset n U hU_fin
  refine ⟨G, ?_, ?_⟩
  · -- Containment of `allBoundedProfilePostSpan ≤ span G`.
    have hspan_eq :
        Submodule.span ℚ (↑G : Set (MvPolynomial (Fin n) ℚ)) = U := by
      exact @span_basisImageFinset_eq n U hU_fin
    calc allBoundedProfilePostSpan
            (PaperFaithfulSeparation.cook_levin_compilation M n hn htb hns).partition
            (Nat.log 2 n) (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn htb hns).get i)
            (cookLevinConstraintType M n hn htb hns)
            bp.toHistogram
        ≤ U := cookLevinProfileSubspace_contains_postSpan bp
      _ = Submodule.span ℚ (↑G : Set (MvPolynomial (Fin n) ℚ)) := hspan_eq.symm
  · -- Cardinality bound via `G.card ≤ finrank ≤ profileTemplateBound`.
    calc G.card
        ≤ Module.finrank ℚ ↥U := @basisImageFinset_card_le n U hU_fin
      _ ≤ profileTemplateBound bp.toHistogram :=
          cookLevinProfileSubspace_finrank_le bp

/-- **Corollary** (fallback / abstract form matching Agent 3's discharge
menu): the bounded-profile template-collapse obligation reduces to providing
the Agent-B profile-subspace data as a single ∃-statement.

This is the "clean-signature" repackaging of
`cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_profileSubspace`:
downstream callers may either (a) supply a concrete Agent-B profile-subspace
family in the compiled coefficient basis (matching the paper's §9 Lemma 31)
or (b) consume this corollary with the existential data. -/
theorem cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_profileSubspace_exists
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdata :
      ∃ U : BoundedProfile (Nat.log 2 n) → Submodule ℚ (MvPolynomial (Fin n) ℚ),
        (∀ bp : BoundedProfile (Nat.log 2 n), Module.Finite ℚ ↥(U bp)) ∧
        (∀ bp : BoundedProfile (Nat.log 2 n),
          allBoundedProfilePostSpan
              (PaperFaithfulSeparation.cook_levin_compilation M n hn htb hns).partition
              (Nat.log 2 n) (Nat.log 2 n)
              (fun i => (cookLevinFactorList M n hn htb hns).get i)
              (cookLevinConstraintType M n hn htb hns)
              bp.toHistogram
            ≤ U bp) ∧
        (∀ bp : BoundedProfile (Nat.log 2 n),
          Module.finrank ℚ ↥(U bp) ≤ profileTemplateBound bp.toHistogram)) :
    CookLevinProfileTemplateCollapseLemmaBoundedProfile M n hn htb hns := by
  rcases hdata with ⟨U, hU_fin, hU_contains, hU_fr⟩
  exact cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_profileSubspace
    M n hn htb hns U hU_fin hU_contains hU_fr

end Paper93
end PallLean
