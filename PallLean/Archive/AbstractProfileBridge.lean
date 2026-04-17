/-
  AbstractProfileBridge.lean — Bridge from AbstractLocalDerivSpace to
  WithinProfileBound, connecting piProdSet to the profile subspace.

  ## Architecture

  1. atomProductSet = piProdSet with A(i) = localDerivAtoms(factors i, S)
  2. finrank(span(atomProductSet)) ≤ ∏ |localDerivAtoms(factors i, S)|
     via finrank_span_piProdSet_le
  3. localDerivAtoms(f, S) ⊆ maxLocalDerivAtoms(f) ∪ {0}, where
     maxLocalDerivAtoms does NOT depend on S
  4. The all-S atomProductSet(S) ⊆ span(piProdSet(maxLocalDerivAtoms))
  5. finrank(span(piProdSet(maxLocalDerivAtoms))) ≤ ∏ |maxLocalDerivAtoms(f_i)|

  This reduces the all-S finrank bound to a bound on ∏ |maxLocalDerivAtoms|,
  which is computable from the factor structure alone.
-/
import PallLean.Archive.AbstractLocalDerivSpace
import PallLean.WithinProfileBound
import PallLean.Archive.PDerivVars
import Mathlib.Tactic

namespace AbstractProfileBridge

open AbstractLocalDerivSpace WithinProfileBound SPDP MultilinearSPDP
open MvPolynomial TuringMachine PaperFaithfulSeparation SymmetricPowerBound

attribute [local instance] Classical.dec

/-! ## Part 1: atomProductSet equals piProdSet -/

/-- atomProductSet factors S = piProdSet Finset.univ (fun i => ↑(localDerivAtoms (factors i) S)). -/
theorem atomProductSet_eq_piProdSet {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ) (S : List (Fin n)) :
    atomProductSet factors S =
      piProdSet Finset.univ
        (fun i => (↑(localDerivAtoms (factors i) S) : Set (MvPolynomial (Fin n) ℚ))) := by
  ext g
  simp only [atomProductSet, piProdSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨atoms, hatoms, rfl⟩
    exact ⟨atoms, fun i _ => hatoms i, rfl⟩
  · rintro ⟨choice, hchoice, rfl⟩
    exact ⟨choice, fun i => hchoice i (Finset.mem_univ i), rfl⟩

/-! ## Part 2: finrank of span(atomProductSet) via finrank_span_piProdSet_le -/

/-- finrank(span(atomProductSet)) ≤ ∏ |localDerivAtoms(f_i, S)|. -/
theorem finrank_span_atomProductSet_le {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ) (S : List (Fin n)) :
    Module.finrank ℚ (Submodule.span ℚ (atomProductSet factors S)) ≤
      ∏ i : Fin L, (localDerivAtoms (factors i) S).card := by
  rw [atomProductSet_eq_piProdSet]
  exact finrank_span_piProdSet_le (fun i => localDerivAtoms (factors i) S)

/-- The per-S-shift post-span finrank via piProdSet infrastructure. -/
theorem perSShift_finrank_via_piProdSet {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (hfactors : ∀ i, (factors i).totalDegree ≤ 2)
    (constraintType : Fin L → ConstraintType)
    (S : List (Fin n)) (shift : MvPolynomial (Fin n) ℚ)
    (h : ProfileHistogram) :
    Module.finrank ℚ ↥(boundedProfilePostSpan factors constraintType S shift h) ≤
      ∏ i : Fin L, (localDerivAtoms (factors i) S).card := by
  have hle : boundedProfilePostSpan factors constraintType S shift h ≤
      Submodule.map (postProcessLinearMap shift)
        (Submodule.span ℚ (atomProductSet factors S)) := by
    calc boundedProfilePostSpan factors constraintType S shift h
        ≤ Submodule.map (postProcessLinearMap shift)
            (Submodule.span ℚ (locallyBoundedClassifiedSet factors constraintType S h)) :=
          boundedProfilePostSpan_le_map_locallyBounded
            factors hfactors constraintType S shift h
      _ ≤ Submodule.map (postProcessLinearMap shift)
            (Submodule.span ℚ (atomProductSet factors S)) := by
          apply Submodule.map_mono
          exact span_locallyBounded_le_span_atomProducts factors constraintType S h
  have hfin_atoms : Module.Finite ℚ ↥(Submodule.span ℚ (atomProductSet factors S)) :=
    Module.Finite.span_of_finite ℚ (atomProductSet_finite factors S)
  calc Module.finrank ℚ ↥(boundedProfilePostSpan factors constraintType S shift h)
      ≤ Module.finrank ℚ ↥(Submodule.map (postProcessLinearMap shift)
          (Submodule.span ℚ (atomProductSet factors S))) :=
        Submodule.finrank_mono hle
    _ ≤ Module.finrank ℚ ↥(Submodule.span ℚ (atomProductSet factors S)) :=
        Submodule.finrank_map_le _ _
    _ ≤ ∏ i : Fin L, (localDerivAtoms (factors i) S).card :=
        finrank_span_atomProductSet_le factors S

/-! ## Part 3: S-independent maximal atom set -/

/-- maxLocalDerivAtoms(f) = all local derivatives using vars(f). -/
noncomputable def maxLocalDerivAtoms {n : ℕ}
    (f : MvPolynomial (Fin n) ℚ) :
    Finset (MvPolynomial (Fin n) ℚ) :=
  {f} ∪
  (f.vars.image (fun v => MvPolynomial.pderiv v f)) ∪
  ((f.vars ×ˢ f.vars).image
    (fun p => MvPolynomial.pderiv p.1 (MvPolynomial.pderiv p.2 f)))

/-- localDerivAtoms(f, S) ⊆ maxLocalDerivAtoms(f) ∪ {0}.

    Every local derivative atom w.r.t. S is either a local derivative atom w.r.t.
    vars(f) (hence in maxLocalDerivAtoms), or a derivative w.r.t. a variable
    outside vars(f) (hence = 0). -/
theorem localDerivAtoms_subset_max_union_zero {n : ℕ}
    (f : MvPolynomial (Fin n) ℚ) (S : List (Fin n)) :
    ∀ a ∈ localDerivAtoms f S, a ∈ maxLocalDerivAtoms f ∨ a = 0 := by
  intro a ha
  unfold localDerivAtoms at ha
  rw [Finset.mem_union, Finset.mem_union] at ha
  rcases ha with (hf | hpd1) | hpd2
  · -- a = f: in maxLocalDerivAtoms via {f}
    left
    unfold maxLocalDerivAtoms
    rw [Finset.mem_union, Finset.mem_union]
    left; left; exact hf
  · -- a = pderiv v f for some v ∈ S.toFinset
    rw [Finset.mem_image] at hpd1
    obtain ⟨v, _, rfl⟩ := hpd1
    by_cases hv_var : v ∈ f.vars
    · left
      unfold maxLocalDerivAtoms
      rw [Finset.mem_union, Finset.mem_union]
      left; right
      exact Finset.mem_image.mpr ⟨v, hv_var, rfl⟩
    · right
      exact MvPolynomial.pderiv_eq_zero_of_notMem_vars hv_var
  · -- a = pderiv v (pderiv w f) for some v,w ∈ S.toFinset
    rw [Finset.mem_image] at hpd2
    obtain ⟨⟨v, w⟩, hvw_mem, rfl⟩ := hpd2
    rw [Finset.mem_product] at hvw_mem
    by_cases hv_var : v ∈ f.vars
    · by_cases hw_var : w ∈ f.vars
      · left
        unfold maxLocalDerivAtoms
        rw [Finset.mem_union, Finset.mem_union]
        right
        exact Finset.mem_image.mpr ⟨(v, w), Finset.mem_product.mpr ⟨hv_var, hw_var⟩, rfl⟩
      · right
        have hw0 : MvPolynomial.pderiv w f = 0 :=
          MvPolynomial.pderiv_eq_zero_of_notMem_vars hw_var
        simp [hw0]
    · right
      have : v ∉ (MvPolynomial.pderiv w f).vars := by
        intro hv; exact hv_var (PDerivVars.pderiv_vars_subset w f hv)
      exact MvPolynomial.pderiv_eq_zero_of_notMem_vars this

/-- span(localDerivAtoms(f, S)) ≤ span(maxLocalDerivAtoms(f)). -/
theorem span_localDerivAtoms_le_span_max {n : ℕ}
    (f : MvPolynomial (Fin n) ℚ) (S : List (Fin n)) :
    Submodule.span ℚ (↑(localDerivAtoms f S) : Set (MvPolynomial (Fin n) ℚ)) ≤
      Submodule.span ℚ (↑(maxLocalDerivAtoms f) : Set (MvPolynomial (Fin n) ℚ)) := by
  apply Submodule.span_le.mpr
  intro a ha
  have ha' : a ∈ localDerivAtoms f S := ha
  rcases localDerivAtoms_subset_max_union_zero f S a ha' with h_max | h_zero
  · exact Submodule.subset_span (show a ∈ ↑(maxLocalDerivAtoms f) from h_max)
  · rw [h_zero]; exact Submodule.zero_mem _

/-! ## Part 4: piProdSet over localDerivAtoms ⊆ span of piProdSet over maxLocalDerivAtoms

Products choosing from localDerivAtoms(f_i, S) lie in the span of products
choosing from maxLocalDerivAtoms(f_i). This uses finset_prod_mem_span_piProdSet
from AbstractLocalDerivSpace: each factor from span(localDerivAtoms) is in
span(maxLocalDerivAtoms), so the product is in span(piProdSet(maxLocalDerivAtoms)). -/

/-- Each element of atomProductSet(S) lies in span(piProdSet(maxLocalDerivAtoms)). -/
theorem atomProductSet_subset_span_maxPiProdSet {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ) (S : List (Fin n)) :
    atomProductSet factors S ⊆
      ↑(Submodule.span ℚ (piProdSet Finset.univ
        (fun i => (↑(maxLocalDerivAtoms (factors i)) : Set (MvPolynomial (Fin n) ℚ))))) := by
  rw [atomProductSet_eq_piProdSet]
  intro g hg
  obtain ⟨choice, hchoice, rfl⟩ := hg
  -- Each choice i ∈ localDerivAtoms(factors i, S) ⊆ maxLocalDerivAtoms ∪ {0}
  -- So choice i ∈ span(maxLocalDerivAtoms(factors i))
  have hchoice_span : ∀ i ∈ Finset.univ,
      choice i ∈ Submodule.span ℚ
        (↑(maxLocalDerivAtoms (factors i)) : Set (MvPolynomial (Fin n) ℚ)) := by
    intro i _
    have hmem : choice i ∈ localDerivAtoms (factors i) S := hchoice i (Finset.mem_univ i)
    rcases localDerivAtoms_subset_max_union_zero (factors i) S (choice i) hmem with h_max | h_zero
    · exact Submodule.subset_span (show choice i ∈ ↑(maxLocalDerivAtoms (factors i)) from h_max)
    · rw [h_zero]; exact Submodule.zero_mem _
  -- By finset_prod_mem_span_piProdSet, the product is in span(piProdSet(max))
  exact finset_prod_mem_span_piProdSet Finset.univ
    (fun i => (↑(maxLocalDerivAtoms (factors i)) : Set (MvPolynomial (Fin n) ℚ)))
    choice hchoice_span

/-- For ALL S: span(atomProductSet(S)) ≤ span(piProdSet(maxLocalDerivAtoms)). -/
theorem allS_span_atomProductSet_le {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ) (S : List (Fin n)) :
    Submodule.span ℚ (atomProductSet factors S) ≤
      Submodule.span ℚ (piProdSet Finset.univ
        (fun i => (↑(maxLocalDerivAtoms (factors i)) : Set (MvPolynomial (Fin n) ℚ)))) := by
  apply Submodule.span_le.mpr
  exact atomProductSet_subset_span_maxPiProdSet factors S

/-! ## Part 5: S-independent finrank bound -/

/-- finrank(span(piProdSet(maxLocalDerivAtoms))) ≤ ∏ |maxLocalDerivAtoms(f_i)|. -/
theorem finrank_span_maxPiProdSet_le {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ) :
    Module.finrank ℚ (Submodule.span ℚ (piProdSet Finset.univ
      (fun i => (↑(maxLocalDerivAtoms (factors i)) : Set (MvPolynomial (Fin n) ℚ))))) ≤
      ∏ i : Fin L, (maxLocalDerivAtoms (factors i)).card :=
  finrank_span_piProdSet_le (fun i => maxLocalDerivAtoms (factors i))

/-- |maxLocalDerivAtoms(f)| ≤ (|vars(f)| + 1)². -/
theorem maxLocalDerivAtoms_card_le {n : ℕ}
    (f : MvPolynomial (Fin n) ℚ) :
    (maxLocalDerivAtoms f).card ≤ (f.vars.card + 1) ^ 2 := by
  unfold maxLocalDerivAtoms
  calc (({f} ∪
      f.vars.image (fun v => MvPolynomial.pderiv v f) ∪
      (f.vars ×ˢ f.vars).image
        (fun p => MvPolynomial.pderiv p.1 (MvPolynomial.pderiv p.2 f))) : Finset _).card
      ≤ 1 + f.vars.card + f.vars.card ^ 2 := by
        calc _ ≤ ({f} ∪
            f.vars.image (fun v => MvPolynomial.pderiv v f)).card +
            ((f.vars ×ˢ f.vars).image
              (fun p => MvPolynomial.pderiv p.1 (MvPolynomial.pderiv p.2 f))).card :=
              Finset.card_union_le _ _
          _ ≤ (({f} : Finset _).card +
              (f.vars.image (fun v => MvPolynomial.pderiv v f)).card) +
              ((f.vars ×ˢ f.vars).image
                (fun p => MvPolynomial.pderiv p.1 (MvPolynomial.pderiv p.2 f))).card := by
            gcongr; exact Finset.card_union_le _ _
          _ ≤ (1 + f.vars.card) + f.vars.card ^ 2 := by
            gcongr
            · simp [Finset.card_singleton]
            · exact Finset.card_image_le
            · calc _ ≤ (f.vars ×ˢ f.vars).card := Finset.card_image_le
                _ = f.vars.card * f.vars.card := Finset.card_product _ _
                _ = f.vars.card ^ 2 := (sq _).symm
    _ ≤ (f.vars.card + 1) ^ 2 := by nlinarith

/-- Per-S-shift finrank ≤ ∏ |maxLocalDerivAtoms(f_i)| (S-independent),
    via span containment rather than per-factor card comparison.

    This is the key S-independent bound: the post-span for ANY S has finrank
    bounded by a quantity that depends only on the factors, not on S. -/
theorem perSShift_finrank_Sindep {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (hfactors : ∀ i, (factors i).totalDegree ≤ 2)
    (constraintType : Fin L → ConstraintType)
    (S : List (Fin n)) (shift : MvPolynomial (Fin n) ℚ)
    (h : ProfileHistogram) :
    Module.finrank ℚ ↥(boundedProfilePostSpan factors constraintType S shift h) ≤
      ∏ i : Fin L, (maxLocalDerivAtoms (factors i)).card := by
  -- Chain: post-span ≤ map(span(atomProductSet)) ≤ map(span(piProdSet(max)))
  -- finrank ≤ finrank(span(piProdSet(max))) ≤ ∏ card(max)
  have hle1 : boundedProfilePostSpan factors constraintType S shift h ≤
      Submodule.map (postProcessLinearMap shift)
        (Submodule.span ℚ (atomProductSet factors S)) := by
    calc boundedProfilePostSpan factors constraintType S shift h
        ≤ Submodule.map (postProcessLinearMap shift)
            (Submodule.span ℚ (locallyBoundedClassifiedSet factors constraintType S h)) :=
          boundedProfilePostSpan_le_map_locallyBounded
            factors hfactors constraintType S shift h
      _ ≤ Submodule.map (postProcessLinearMap shift)
            (Submodule.span ℚ (atomProductSet factors S)) := by
          apply Submodule.map_mono
          exact span_locallyBounded_le_span_atomProducts factors constraintType S h
  have hle2 : Submodule.span ℚ (atomProductSet factors S) ≤
      Submodule.span ℚ (piProdSet Finset.univ
        (fun i => (↑(maxLocalDerivAtoms (factors i)) : Set (MvPolynomial (Fin n) ℚ)))) :=
    allS_span_atomProductSet_le factors S
  have hle3 : boundedProfilePostSpan factors constraintType S shift h ≤
      Submodule.map (postProcessLinearMap shift)
        (Submodule.span ℚ (piProdSet Finset.univ
          (fun i => (↑(maxLocalDerivAtoms (factors i)) : Set (MvPolynomial (Fin n) ℚ))))) :=
    le_trans hle1 (Submodule.map_mono hle2)
  have hfin_max : Module.Finite ℚ ↥(Submodule.span ℚ (piProdSet Finset.univ
      (fun i => (↑(maxLocalDerivAtoms (factors i)) : Set (MvPolynomial (Fin n) ℚ))))) :=
    Module.Finite.span_of_finite ℚ (piProdSet_finite Finset.univ
      (fun i => (↑(maxLocalDerivAtoms (factors i)) : Set (MvPolynomial (Fin n) ℚ)))
      (fun i _ => Finset.finite_toSet _))
  calc Module.finrank ℚ ↥(boundedProfilePostSpan factors constraintType S shift h)
      ≤ Module.finrank ℚ ↥(Submodule.map (postProcessLinearMap shift)
          (Submodule.span ℚ (piProdSet Finset.univ
            (fun i => (↑(maxLocalDerivAtoms (factors i)) : Set (MvPolynomial (Fin n) ℚ)))))) :=
        Submodule.finrank_mono hle3
    _ ≤ Module.finrank ℚ ↥(Submodule.span ℚ (piProdSet Finset.univ
          (fun i => (↑(maxLocalDerivAtoms (factors i)) : Set (MvPolynomial (Fin n) ℚ))))) :=
        Submodule.finrank_map_le _ _
    _ ≤ ∏ i : Fin L, (maxLocalDerivAtoms (factors i)).card :=
        finrank_span_maxPiProdSet_le factors

/-! ## Part 6: The all-S allBoundedProfilePostSpan finrank bound

The allBoundedProfilePostSpan is the span of generators mlProj(shift * g) across
ALL (S, shift) pairs with S.length ≤ κ. Since each generator's g lies in
atomProductSet(S) ⊆ span(piProdSet(maxLocalDerivAtoms)), the post-processed
generator lies in the image of span(piProdSet(max)) under SOME postProcessLinearMap.

The images of a fixed submodule V under different linear maps L_α can have
total span ≤ dim(V) × (dim of the ambient multilinear space). But we need
a better bound.

Key structural fact: allBoundedProfilePostSpan is itself contained in
the image of span(piProdSet(max)) under the LINEAR MAP
  g ↦ mlProj(shift * g)
for VARYING shift. But varying shift means varying linear maps.

The correct bound: allBoundedProfilePostSpan ≤ the multilinear monomial
subspace (2^n dimensional). This is too crude.

The better bound uses the FACTORIZATION from Part 24 of WithinProfileBound:
generators factor as (touched part) × (untouched factor). The untouched
factor is FIXED for a given profile. The touched part lives in the image
of span(piProdSet restricted to TOUCHED factors) under postProcessLinearMap.

For κ touched factors with ≤ 2 variables each:
  ∏_{touched} |maxLocalDerivAtoms| ≤ ((2+1)²)^κ = 9^κ

This is the per-S-shift bound for the TOUCHED part only.
The all-S union of touched parts is still in the SAME piProdSet(max, touched),
because maxLocalDerivAtoms doesn't depend on S.

BUT: different S have different SETS of touched factors! Factor i is touched
by S if S intersects vars(f_i). For profile h, the touched factors are those
with d_i.length > 0. Different S touch different factors.

The resolution: the all-S allBoundedProfilePostSpan for profile h collects
generators from ALL possible choices of κ-many touched factors (with the
right type histogram h). The piProdSet(max, touched) for each choice has
finrank ≤ 9^κ. But different choices give different piProdSets on
different variable sets. The UNION of these piProdSets has finrank
≤ 9^κ × C(L, κ) which is superpolynomial.

THIS is where the symmetric power reduction is needed:
- Factors of the same type τ are STRUCTURALLY IDENTICAL (same polynomial form
  on different variables)
- Their maxLocalDerivAtoms are ISOMORPHIC (same abstract elements, instantiated
  at different variable positions)
- The span of products across different choices of which factors to touch
  factors through Sym^{h(τ)}(W_τ) ⊗ Sym^{h(τ')}(W_{τ'}) ⊗ ...
- dim(Sym^m(W)) = C(m + dim(W) - 1, dim(W) - 1) ≤ (m+1)^{dim(W)-1}

This is exactly the content of the axiom spdp_profile_generators.

For now, we record the S-independent per-S-shift bound as the main result. -/

/-- For degree-2 factors with ≤ d variables each, the per-S-shift post-span
    has finrank ≤ ((d+1)²)^L, independently of S. -/
theorem perSShift_finrank_degree2 {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (hfactors : ∀ i, (factors i).totalDegree ≤ 2)
    (d : ℕ) (hd : ∀ i, (factors i).vars.card ≤ d)
    (constraintType : Fin L → ConstraintType)
    (S : List (Fin n)) (shift : MvPolynomial (Fin n) ℚ)
    (h : ProfileHistogram) :
    Module.finrank ℚ ↥(boundedProfilePostSpan factors constraintType S shift h) ≤
      ((d + 1) ^ 2) ^ L := by
  calc Module.finrank ℚ ↥(boundedProfilePostSpan factors constraintType S shift h)
      ≤ ∏ i : Fin L, (maxLocalDerivAtoms (factors i)).card :=
        perSShift_finrank_Sindep factors hfactors constraintType S shift h
    _ ≤ ∏ _i : Fin L, (d + 1) ^ 2 := by
        apply Finset.prod_le_prod
        · intro i _; exact Nat.zero_le _
        · intro i _
          exact le_trans (maxLocalDerivAtoms_card_le (factors i))
            (Nat.pow_le_pow_left (Nat.succ_le_succ (hd i)) 2)
    _ = ((d + 1) ^ 2) ^ L := by simp [Finset.prod_const]

end AbstractProfileBridge
