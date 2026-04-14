/-
  WithinProfileBound.lean — Finite enumeration of bounded profiles and
  structural reduction of HasFiniteProfileCover

  ## Overview

  1. Bounded profiles (each component ≤ κ) are finite: ≤ (κ+1)^4.
  2. Admissible profiles (mass ≤ κ) are bounded.
  3. The within-profile template arithmetic: ∏_τ C(h(τ)+2,2) ≤ (κ+1)^8.
  4. A clean statement of the remaining within-profile finrank claim.
  5. Formal derivation: claim → HasFiniteProfileCover → rank bound.
-/
import PallLean.SymmetricPowerBound
import PallLean.MlProjFar
import Mathlib.Tactic

namespace WithinProfileBound

open SPDP MultilinearSPDP MvPolynomial TuringMachine PaperFaithfulSeparation
open SymmetricPowerBound

attribute [local instance] Classical.dec

/-! ## Part 1: Finite enumeration of bounded profiles -/

/-- A bounded profile at radius κ: each component is ≤ κ. -/
def BoundedProfile (κ : ℕ) := { h : ProfileHistogram // ∀ τ, h τ ≤ κ }

/-- Extract the underlying histogram. -/
def BoundedProfile.toHistogram {κ : ℕ} (bp : BoundedProfile κ) : ProfileHistogram :=
  bp.val

/-- Encode a bounded profile as a 4-tuple of Fin (κ+1). -/
def boundedProfileToTuple (κ : ℕ) (bp : BoundedProfile κ) :
    Fin (κ + 1) × Fin (κ + 1) × Fin (κ + 1) × Fin (κ + 1) :=
  (⟨bp.val ConstraintType.booleanity,
      Nat.lt_succ_of_le (bp.property ConstraintType.booleanity)⟩,
   ⟨bp.val ConstraintType.adjacency,
      Nat.lt_succ_of_le (bp.property ConstraintType.adjacency)⟩,
   ⟨bp.val ConstraintType.transitionLeft,
      Nat.lt_succ_of_le (bp.property ConstraintType.transitionLeft)⟩,
   ⟨bp.val ConstraintType.transitionRight,
      Nat.lt_succ_of_le (bp.property ConstraintType.transitionRight)⟩)

/-- The tuple encoding is injective. -/
theorem boundedProfileToTuple_injective (κ : ℕ) :
    Function.Injective (boundedProfileToTuple κ) := by
  intro ⟨h₁, hb₁⟩ ⟨h₂, hb₂⟩ heq
  simp only [boundedProfileToTuple, Prod.mk.injEq, Fin.mk.injEq] at heq
  obtain ⟨h1, h2, h3, h4⟩ := heq
  congr 1
  funext τ
  cases τ <;> assumption

/-- Bounded profiles are finite. -/
noncomputable instance boundedProfileFintype (κ : ℕ) : Fintype (BoundedProfile κ) :=
  Fintype.ofInjective (boundedProfileToTuple κ) (boundedProfileToTuple_injective κ)

/-- The number of bounded profiles is ≤ (κ+1)^4. -/
theorem boundedProfile_card_le (κ : ℕ) :
    Fintype.card (BoundedProfile κ) ≤ (κ + 1) ^ 4 := by
  calc Fintype.card (BoundedProfile κ)
      ≤ Fintype.card (Fin (κ + 1) × Fin (κ + 1) × Fin (κ + 1) × Fin (κ + 1)) :=
        Fintype.card_le_of_injective _ (boundedProfileToTuple_injective κ)
    _ = (κ + 1) ^ 4 := by
        simp [Fintype.card_prod, Fintype.card_fin]
        ring

/-- The number of bounded profiles is ≤ profileCount κ. -/
theorem boundedProfile_card_le_profileCount (κ : ℕ) :
    Fintype.card (BoundedProfile κ) ≤ profileCount κ := by
  unfold profileCount; exact boundedProfile_card_le κ

/-! ## Part 2: Admissible profiles are bounded -/

/-- An admissible profile (mass ≤ κ) has each component ≤ κ. -/
theorem admissible_implies_bounded {κ : ℕ} {h : ProfileHistogram}
    (hadm : ProfileAdmissible κ h) : ∀ τ, h τ ≤ κ :=
  fun τ => admissibleProfile_component_le hadm τ

/-- Embed an admissible profile into bounded profiles. -/
def admissibleToBounded {κ : ℕ} {h : ProfileHistogram}
    (hadm : ProfileAdmissible κ h) : BoundedProfile κ :=
  ⟨h, admissible_implies_bounded hadm⟩

/-- The embedding preserves the histogram. -/
@[simp] theorem admissibleToBounded_toHistogram {κ : ℕ} {h : ProfileHistogram}
    (hadm : ProfileAdmissible κ h) :
    (admissibleToBounded hadm).toHistogram = h := rfl

/-! ## Part 3: Derivative-count profiles from Leibniz terms -/

/-- The derivative-count profile of a distribution with total length ≤ κ
    has each component ≤ κ (hence is bounded). -/
theorem derivCountProfile_bounded_of_total_le {L n κ : ℕ}
    (constraintType : Fin L → ConstraintType)
    (d : Fin L → List (Fin n))
    (htotal : ∑ i : Fin L, (d i).length ≤ κ) :
    ∀ τ, (derivCountProfile constraintType d) τ ≤ κ :=
  admissible_implies_bounded (derivCountProfile_admissible_of_total_le constraintType d htotal)

/-! ## Part 4: Within-profile template count (arithmetic) -/

/-- The within-profile template count is ≤ (κ+1)^8 for admissible profiles.

    Chain: ∏_τ C(h(τ)+2, 2) ≤ ∏_τ (h(τ)+1)^2 ≤ ∏_τ (κ+1)^2 = (κ+1)^8. -/
theorem within_profile_template_count_le (κ : ℕ)
    (h : ProfileHistogram) (hadm : ProfileAdmissible κ h) :
    (∏ τ : ConstraintType, Nat.choose (h τ + 2) 2) ≤ withinProfileBound κ := by
  calc ∏ τ : ConstraintType, Nat.choose (h τ + 2) 2
      ≤ ∏ τ : ConstraintType, (κ + 1) ^ 2 := by
        apply Finset.prod_le_prod
        · intro τ _; exact Nat.zero_le _
        · intro τ _
          have hτ : h τ ≤ κ := admissibleProfile_component_le hadm τ
          calc Nat.choose (h τ + 2) 2
              ≤ (h τ + 1) ^ 2 := dim_sym_le (h τ) 2
            _ ≤ (κ + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    _ = (κ + 1) ^ 8 := by
        have : Fintype.card ConstraintType = 4 := by decide
        simp [Finset.prod_const, this]
        ring
    _ = withinProfileBound κ := by unfold withinProfileBound; rfl

/-! ## Part 5: Within-profile finrank claim and formal reduction

The remaining mathematical frontier is: for each profile h, the
within-profile post-span has finrank ≤ withinProfileBound κ.

We state this as a clean Prop targeting the allProfilePostSpan decomposition
(which uses the hit-count profile, not the derivative-count profile).
Once this is proved, HasFiniteProfileCover follows formally. -/

/-- Clean proposition: within-profile finrank bound for the hit-count profile
    decomposition. For each bounded profile bp, the allProfilePostSpan
    (collecting generators across all S and shifts with that hit-count profile)
    has finrank ≤ withinProfileBound κ.

    The mathematical content (not yet formalized):
    - Each Cook-Levin factor has degree ≤ 2, so its local derivative space W_τ
      has dimension ≤ 3
    - Products of local contributions factor through ⊗_τ Sym^{h(τ)}(W_τ)
    - dim(Sym^m(W)) ≤ (m+1)^(dim(W)-1) by stars-and-bars
    - Product over types: ∏_τ (h(τ)+1)^2 ≤ (κ+1)^8 -/
def WithinProfileFinrankClaim {n L : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (constraintType : Fin L → ConstraintType) : Prop :=
  ∀ (h : ProfileHistogram),
    Module.Finite ℚ ↥(allProfilePostSpan B κ ℓ factors constraintType h) ∧
    Module.finrank ℚ ↥(allProfilePostSpan B κ ℓ factors constraintType h)
      ≤ withinProfileBound κ

/-- The remaining step for a direct rank bound from WithinProfileFinrankClaim:
    show SPDP ≤ ⨆_{bounded h} V_h (rather than ⨆_{all h} V_h).

    The mathematical argument: each SPDP generator's Leibniz expansion
    produces terms with distributions d that partition S (total length = |S| = κ),
    hence with admissible (therefore bounded) profiles. So the infinite sup
    restricts to a finite one. Formalizing this requires refining the
    distribDerivProds construction to track total distribution length.

    Once this gap is closed, the rank bound follows:
      SPDP ≤ ⨆_{Fin P} V_{enum(i)}  (P = |BoundedProfile κ| ≤ (κ+1)^4)
      finrank(V_i) ≤ (κ+1)^8         (from WithinProfileFinrankClaim)
      rank ≤ P × (κ+1)^8 ≤ (κ+1)^12 = combinedProfileBound κ -/
def InfiniteToFiniteProfileCoverGap {n L : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (constraintType : Fin L → ConstraintType)
    (p : MvPolynomial (Fin n) ℚ) : Prop :=
  mlBlockedSpdpSubspace B κ ℓ p ≤
    ⨆ (bp : BoundedProfile κ),
      allProfilePostSpan B κ ℓ factors constraintType bp.toHistogram

/-! ## Part 6: Bounded distribution Leibniz span

We define a refined distribDerivProds set that tracks the total distribution
length, ensuring profiles are bounded. The Leibniz expansion theorem still
applies because the actual linear combination only uses distributions with
total length = |S|. -/

/-- Bounded distribDerivProds: derivative distributions where the total number
    of derivative assignments is bounded by some threshold B.
    This refines LeibnizProduct.distribDerivProds to only include distributions
    where ∑ |d(i)| ≤ B. -/
def boundedDistribDerivProds {n : ℕ} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → MvPolynomial (Fin n) ℚ) (S : List (Fin n))
    (B : ℕ) :
    Set (MvPolynomial (Fin n) ℚ) :=
  { g | ∃ (d : ι → List (Fin n)),
    (∀ i, ∀ v ∈ d i, v ∈ S) ∧
    g = s.prod (fun i => iterDerivList (d i) (f i)) ∧
    ∑ i ∈ s, (d i).length ≤ B }

/-- The bounded distribDerivProds is a subset of the unrestricted distribDerivProds. -/
theorem boundedDistribDerivProds_subset {n : ℕ} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → MvPolynomial (Fin n) ℚ) (S : List (Fin n))
    (B : ℕ) :
    boundedDistribDerivProds s f S B ⊆ LeibnizProduct.distribDerivProds s f S := by
  intro g ⟨d, hd_elts, hg, _⟩
  exact ⟨d, hd_elts, hg⟩

/-- The iterated derivative of a product lies in the span of BOUNDED distribDerivProds
    with bound B = |S|.

    This is a refinement of `iterDerivList_finset_prod_mem_span` that tracks
    the total distribution length. The proof follows the same induction but
    additionally verifies the length bound at each step. -/
theorem iterDerivList_finset_prod_mem_bounded_span {n : ℕ}
    (S : List (Fin n)) (f : Fin L → MvPolynomial (Fin n) ℚ) :
    iterDerivList S (Finset.univ.prod f) ∈
      Submodule.span ℚ (boundedDistribDerivProds Finset.univ f S S.length) := by
  -- Reprove the Leibniz theorem tracking distribution lengths.
  -- The induction adds one derivative per step, maintaining ∑|d(i)| = step count.
  induction S generalizing f with
  | nil =>
    apply Submodule.subset_span
    refine ⟨fun _ => [], fun _ _ hv => absurd hv List.not_mem_nil, ?_, ?_⟩
    · simp [IterDerivHelpers.iterDerivList_nil]
    · simp
  | cons v rest ih =>
    rw [IterDerivHelpers.iterDerivList_cons]
    rw [LeibnizProduct.pderiv_finset_prod Finset.univ f v]
    rw [LeibnizProduct.iterDerivList_finset_sum]
    apply Submodule.sum_mem
    intro k hk
    -- For each k ∈ univ, the summand is iterDerivList rest ((pderiv v (f k)) * (univ.erase k).prod f)
    -- = iterDerivList rest (univ.prod f') where f' = Function.update f k (pderiv v (f k))
    set f' : Fin L → MvPolynomial (Fin n) ℚ :=
      Function.update f k (pderiv v (f k)) with hf'_def
    have hsummand : pderiv v (f k) * (Finset.univ.erase k).prod f = Finset.univ.prod f' := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
      congr 1
      · exact (Function.update_self k (pderiv v (f k)) f).symm
      · apply Finset.prod_congr rfl
        intro j hj
        exact (Function.update_of_ne (Finset.mem_erase.mp hj).1 _ f).symm
    rw [hsummand]
    -- By IH: iterDerivList rest (univ.prod f') ∈ span(bounded rest.length f')
    have ih_f' := ih f'
    -- bounded distributions for f' with bound rest.length can be lifted to
    -- bounded distributions for f with bound (v :: rest).length = rest.length + 1
    suffices h_sub : boundedDistribDerivProds Finset.univ f' rest rest.length ⊆
        boundedDistribDerivProds Finset.univ f (v :: rest) (v :: rest).length by
      exact Submodule.span_mono h_sub ih_f'
    intro g ⟨d, hd_elts, hg_eq, hd_len⟩
    -- g = univ.prod (fun i => iterDerivList (d i) (f' i))
    -- Define d' i = if i = k then v :: d k else d i
    refine ⟨fun i => if i = k then v :: d i else d i, ?_, ?_, ?_⟩
    · -- Elements of d' i are in v :: rest
      intro i w hw
      simp only at hw
      split_ifs at hw with hik
      · simp only [List.mem_cons] at hw ⊢
        rcases hw with rfl | hw'
        · left; rfl
        · right; exact hd_elts i w hw'
      · simp only [List.mem_cons] at ⊢
        right; exact hd_elts i w hw
    · -- g = univ.prod (fun i => iterDerivList (d' i) (f i))
      rw [hg_eq]
      apply Finset.prod_congr rfl
      intro i _
      show iterDerivList (d i) (f' i) =
        iterDerivList (if i = k then v :: d i else d i) (f i)
      split_ifs with hik
      · subst hik
        rw [IterDerivHelpers.iterDerivList_cons]
        show iterDerivList (d i) (f' i) = iterDerivList (d i) (pderiv v (f i))
        congr 1
        exact Function.update_self i (pderiv v (f i)) f
      · show iterDerivList (d i) (f' i) = iterDerivList (d i) (f i)
        congr 1
        exact Function.update_of_ne hik _ f
    · -- ∑|d'(i)| ≤ (v :: rest).length = rest.length + 1
      simp only [List.length_cons]
      -- First simplify (if i = k then v :: d i else d i).length
      have hlength : ∀ i, (if i = k then v :: d i else d i).length =
          (if i = k then 1 else 0) + (d i).length := by
        intro i
        split_ifs with hik
        · simp [List.length_cons]; omega
        · simp
      simp_rw [hlength]
      rw [Finset.sum_add_distrib]
      have h1 : ∑ i ∈ Finset.univ, (if i = k then 1 else 0) = 1 := by
        rw [Finset.sum_ite_eq' Finset.univ k (fun _ => 1)]
        simp [Finset.mem_univ]
      rw [h1]
      omega

/-! ## Part 7: Profile decomposition with bounded distributions

Using the bounded Leibniz span, we can build a profile decomposition where
only bounded profiles (each component ≤ κ) appear. This closes the
InfiniteToFiniteProfileCoverGap. -/

/-- Profile-classified bounded Leibniz set: distributions with total length ≤ |S|
    and a specific derivative-count profile h. -/
def boundedProfileClassifiedSet {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (constraintType : Fin L → ConstraintType)
    (S : List (Fin n))
    (h : ProfileHistogram) :
    Set (MvPolynomial (Fin n) ℚ) :=
  { g | ∃ (d : Fin L → List (Fin n)),
      (∀ i, ∀ v ∈ d i, v ∈ S) ∧
      g = Finset.univ.prod (fun i => iterDerivList (d i) (factors i)) ∧
      derivCountProfile constraintType d = h ∧
      ∑ i : Fin L, (d i).length ≤ S.length }

/-- Every bounded distribDerivProd has a derivative-count profile, so the
    profile-indexed union of bounded classified sets covers bounded distribDerivProds. -/
theorem boundedDistribDerivProds_subset_iUnion_bounded {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (constraintType : Fin L → ConstraintType)
    (S : List (Fin n)) :
    boundedDistribDerivProds Finset.univ factors S S.length ⊆
      ⋃ (h : ProfileHistogram), boundedProfileClassifiedSet factors constraintType S h := by
  intro g ⟨d, hd_elts, hg_eq, hd_len⟩
  rw [Set.mem_iUnion]
  refine ⟨derivCountProfile constraintType d, d, hd_elts, hg_eq, rfl, ?_⟩
  simpa using hd_len

/-- The profile of a bounded distribution is admissible: mass ≤ |S|. -/
theorem boundedProfileClassifiedSet_profile_admissible {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (constraintType : Fin L → ConstraintType)
    (S : List (Fin n))
    (h : ProfileHistogram)
    (g : MvPolynomial (Fin n) ℚ)
    (hg : g ∈ boundedProfileClassifiedSet factors constraintType S h) :
    ProfileAdmissible S.length h := by
  rcases hg with ⟨d, _, _, hprof, hlen⟩
  rw [← hprof]
  exact derivCountProfile_admissible_of_total_le constraintType d (by simpa using hlen)

/-- Post-processed bounded-profile-indexed subspace for a fixed S and shift. -/
noncomputable def boundedProfilePostSpan {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (constraintType : Fin L → ConstraintType)
    (S : List (Fin n))
    (shift : MvPolynomial (Fin n) ℚ)
    (h : ProfileHistogram) :
    Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
  Submodule.span ℚ
    ((fun g => mlProj (shift * g)) '' boundedProfileClassifiedSet factors constraintType S h)

/-- Collecting across all S (of length ≤ κ) and shifts (vars ⊆ S.toFinset).

    Note: the shift is restricted to have vars ⊆ S.toFinset, matching the SPDP
    generator constraint. This ensures the resulting post-span is finite-dimensional
    (since mlProj produces multilinear polynomials on a bounded variable set).

    Without this restriction, the post-span would be infinite-dimensional
    (arbitrary shifts introduce unbounded new variables). -/
noncomputable def allBoundedProfilePostSpan {n L : ℕ}
    (_B : BlockPartition n) (κ _ℓ : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (constraintType : Fin L → ConstraintType)
    (h : ProfileHistogram) :
    Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
  Submodule.span ℚ
    (⋃ (S : List (Fin n)) (_ : S.length ≤ κ)
       (shift : MvPolynomial (Fin n) ℚ) (_ : shift.vars ⊆ S.toFinset),
      (fun g => mlProj (shift * g)) '' boundedProfileClassifiedSet factors constraintType S h)

/-- The bounded profile post-span is contained in the original profile post-span
    (since bounded classified sets are subsets of unrestricted classified sets). -/
theorem allBoundedProfilePostSpan_le_allDerivCountProfilePostSpan {n L : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (constraintType : Fin L → ConstraintType)
    (h : ProfileHistogram) :
    allBoundedProfilePostSpan B κ ℓ factors constraintType h ≤
      allDerivCountProfilePostSpan B κ ℓ factors constraintType h := by
  apply Submodule.span_mono
  intro x hx
  simp only [Set.mem_iUnion, Set.mem_image] at hx ⊢
  obtain ⟨S, _hSlen, shift, _hshiftvars, g, ⟨d, hd_elts, hg_eq, hprof, _hlen⟩, rfl⟩ := hx
  exact ⟨S, shift, g, ⟨d, hd_elts, hg_eq, hprof⟩, rfl⟩

/-- Each SPDP generator lies in the sup of bounded-profile post-spans. -/
theorem spdp_generator_in_bounded_profile_iSup {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (constraintType : Fin L → ConstraintType)
    (S : List (Fin n))
    (shift : MvPolynomial (Fin n) ℚ)
    (B : BlockPartition n) (κ ℓ : ℕ)
    (p : MvPolynomial (Fin n) ℚ)
    (hp : p = Finset.univ.prod factors) :
    mlProj (shift * iterDerivList S p) ∈
      ⨆ (h : ProfileHistogram),
        boundedProfilePostSpan factors constraintType S shift h := by
  rw [hp]
  -- iterDerivList S (∏ factors) ∈ span(bounded distribDerivProds with bound |S|)
  have hLeibniz := iterDerivList_finset_prod_mem_bounded_span S factors
  -- Post-process: mlProj(shift * ·) applied to the span membership
  have hpost := SymmetricPower.mlProj_mul_mem_span_image shift
    (boundedDistribDerivProds Finset.univ factors S S.length)
    (iterDerivList S (Finset.univ.prod factors))
    hLeibniz
  -- The post-processed span ≤ ⨆_h boundedProfilePostSpan
  -- because bounded distribDerivProds ⊆ ⋃_h boundedProfileClassifiedSet
  have hcover : Submodule.span ℚ
      ((fun g => mlProj (shift * g)) '' boundedDistribDerivProds Finset.univ factors S S.length) ≤
      ⨆ (h : ProfileHistogram), boundedProfilePostSpan factors constraintType S shift h := by
    apply Submodule.span_le.mpr
    intro q hq
    rcases hq with ⟨g, hg_mem, rfl⟩
    have hg_class := boundedDistribDerivProds_subset_iUnion_bounded factors constraintType S hg_mem
    rw [Set.mem_iUnion] at hg_class
    obtain ⟨h, hg_h⟩ := hg_class
    apply Submodule.mem_iSup_of_mem h
    apply Submodule.subset_span
    exact ⟨g, hg_h, rfl⟩
  exact hcover hpost

/-- The SPDP subspace is contained in the sup of allBoundedProfilePostSpan
    over all profile histograms. -/
theorem mlBlockedSpdpSubspace_le_allBoundedProfilePostSpan_iSup {n L : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (constraintType : Fin L → ConstraintType)
    (p : MvPolynomial (Fin n) ℚ)
    (hp : p = Finset.univ.prod factors) :
    mlBlockedSpdpSubspace B κ ℓ p ≤
      ⨆ (h : ProfileHistogram), allBoundedProfilePostSpan B κ ℓ factors constraintType h := by
  apply Submodule.span_le.mpr
  intro q hq
  rcases hq with ⟨S, shift, hlen, _hdeg, hvars, _hadm, rfl⟩
  have hmem := spdp_generator_in_bounded_profile_iSup factors constraintType S shift B κ ℓ p hp
  apply (iSup_mono (fun h => ?_) :
    ⨆ h, boundedProfilePostSpan _ _ S shift h ≤ _) hmem
  apply Submodule.span_mono
  intro x hx
  simp only [Set.mem_iUnion, Set.mem_image] at hx ⊢
  obtain ⟨g, hg_mem, rfl⟩ := hx
  exact ⟨S, le_of_eq hlen, shift, hvars, g, hg_mem, rfl⟩

/-- For bounded distributions, the profile has mass ≤ |S|. When |S| = κ,
    this means each component ≤ κ, so the profile is bounded. Therefore
    the sup over all profiles restricts to bounded profiles. -/
theorem allBoundedProfilePostSpan_zero_of_unbounded {n L : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (constraintType : Fin L → ConstraintType)
    (h : ProfileHistogram)
    (hunbounded : ∃ τ, h τ > κ) :
    ∀ (S : List (Fin n)) (shift : MvPolynomial (Fin n) ℚ),
      S.length ≤ κ →
      boundedProfileClassifiedSet factors constraintType S h = ∅ := by
  intro S shift hlen
  ext g
  simp only [Set.mem_empty_iff_false, iff_false]
  intro ⟨d, hd_elts, hg_eq, hprof, hd_len⟩
  obtain ⟨τ, hτ⟩ := hunbounded
  have hadm := derivCountProfile_admissible_of_total_le constraintType d
    (le_trans (by simpa using hd_len) hlen)
  have hτ_le := admissibleProfile_component_le hadm τ
  rw [hprof] at hτ_le
  omega

/-! ## Part 8: Constructing HasFiniteProfileCover

Given the covering by bounded profile subspaces and a within-profile
finrank bound, we assemble HasFiniteProfileCover. -/

/-- The refined within-profile finrank claim for bounded-distribution
    profile subspaces. This is strictly weaker than the original
    WithinProfileFinrankClaim because it uses the bounded classified sets. -/
def BoundedWithinProfileFinrankClaim {n L : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (constraintType : Fin L → ConstraintType) : Prop :=
  ∀ (h : ProfileHistogram),
    Module.Finite ℚ ↥(allBoundedProfilePostSpan B κ ℓ factors constraintType h) ∧
    Module.finrank ℚ ↥(allBoundedProfilePostSpan B κ ℓ factors constraintType h)
      ≤ withinProfileBound κ

/-- Given the bounded within-profile finrank claim, construct HasFiniteProfileCover.

    The proof assembles:
    1. Covering: SPDP ≤ ⨆_h allBoundedProfilePostSpan(h) (proved)
    2. Finite enumeration: ≤ (κ+1)^4 bounded profiles (proved)
    3. Per-profile finrank: ≤ (κ+1)^8 (hypothesis)
    4. The sup over all profiles ≤ sup over bounded profiles
       (because each element is in SOME allBoundedProfilePostSpan) -/
theorem hasFiniteProfileCover_of_boundedWithinProfileFinrank {n L : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (constraintType : Fin L → ConstraintType)
    (p : MvPolynomial (Fin n) ℚ)
    (hp : p = Finset.univ.prod factors)
    (hwithin : BoundedWithinProfileFinrankClaim B κ ℓ factors constraintType) :
    HasFiniteProfileCover B κ ℓ p := by
  -- Enumerate bounded profiles via Fin P
  set P := Fintype.card (BoundedProfile κ)
  let enum := (Fintype.equivFin (BoundedProfile κ)).symm
  -- Define the profile subspaces indexed by Fin P
  let spaces : Fin P → Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
    fun i => allBoundedProfilePostSpan B κ ℓ factors constraintType (enum i).toHistogram
  refine ⟨P, spaces, ?_, ?_, ?_, ?_⟩
  · -- P ≤ profileCount κ
    exact boundedProfile_card_le_profileCount κ
  · -- Each space is finite-dimensional
    intro i; exact (hwithin (enum i).toHistogram).1
  · -- Each space has finrank ≤ withinProfileBound κ
    intro i; exact (hwithin (enum i).toHistogram).2
  · -- SPDP ≤ ⨆ i, spaces i
    -- Directly show each SPDP generator lies in some spaces_i.
    apply Submodule.span_le.mpr
    intro q hq
    rcases hq with ⟨S, shift, hlen, _hdeg, hvars, _hadm, rfl⟩
    -- The generator mlProj(shift * iterDerivList S p) lies in the bounded profile sup
    rw [hp]
    have hLeibniz := iterDerivList_finset_prod_mem_bounded_span S factors
    have hpost := SymmetricPower.mlProj_mul_mem_span_image shift
      (boundedDistribDerivProds Finset.univ factors S S.length)
      (iterDerivList S (Finset.univ.prod factors))
      hLeibniz
    -- Each element of the bounded span has a bounded profile (mass ≤ |S| = κ)
    -- So it lies in allBoundedProfilePostSpan for some bounded profile
    -- which is some spaces_i.
    suffices hsuff : mlProj (shift * iterDerivList S (Finset.univ.prod factors)) ∈
        ⨆ (bp : BoundedProfile κ),
          allBoundedProfilePostSpan B κ ℓ factors constraintType bp.toHistogram by
      -- Convert from ⨆_{bp} to ⨆_{Fin P}
      have hle : ⨆ (bp : BoundedProfile κ),
          allBoundedProfilePostSpan B κ ℓ factors constraintType bp.toHistogram ≤
          ⨆ (i : Fin P), spaces i := by
        apply iSup_le
        intro bp
        let i := (Fintype.equivFin (BoundedProfile κ)) bp
        apply le_trans _ (le_iSup spaces i)
        show allBoundedProfilePostSpan B κ ℓ factors constraintType bp.toHistogram ≤ spaces i
        have : (enum i).toHistogram = bp.toHistogram := by
          show ((Fintype.equivFin (BoundedProfile κ)).symm
            ((Fintype.equivFin (BoundedProfile κ)) bp)).toHistogram = bp.toHistogram
          simp [Equiv.symm_apply_apply]
        rw [← this]
      exact hle hsuff
    -- Now show the generator lies in ⨆_{bp} allBoundedProfilePostSpan
    -- Each distribDerivProd with bounded total length has a bounded profile
    -- (mass ≤ |S| = κ, hence each component ≤ κ)
    -- The post-processed generator is in the span of these, hence in the sup.
    -- Use the intermediate: generator ∈ span of post-processed bounded terms,
    -- and each such term lies in some allBoundedProfilePostSpan(bp).
    apply Submodule.span_le.mpr _ hpost
    intro q' hq'
    rcases hq' with ⟨g, hg_mem, rfl⟩
    -- g ∈ boundedDistribDerivProds, so it has a bounded profile
    rcases hg_mem with ⟨d, hd_elts, hg_eq, hd_len⟩
    -- The profile of d is admissible (mass ≤ |S| = κ)
    have hadm : ProfileAdmissible κ (derivCountProfile constraintType d) := by
      apply derivCountProfile_admissible_of_total_le
      rw [hlen] at hd_len
      simpa using hd_len
    -- Hence each component ≤ κ
    set bp := admissibleToBounded hadm
    apply Submodule.mem_iSup_of_mem bp
    -- mlProj(shift * g) ∈ allBoundedProfilePostSpan B κ ℓ factors constraintType bp.toHistogram
    apply Submodule.subset_span
    simp only [Set.mem_iUnion, Set.mem_image]
    exact ⟨S, le_of_eq hlen, shift, hvars, g,
      ⟨d, hd_elts, hg_eq, rfl, by simpa using hd_len⟩, rfl⟩

/-- BoundedWithinProfileFinrankClaim implies the SPDP rank bound.

    This is the clean reduction: if each bounded-distribution profile subspace
    has finrank ≤ (κ+1)^8, then the total SPDP rank is ≤ (κ+1)^12.

    Once BoundedWithinProfileFinrankClaim is proved for the Cook-Levin
    compiled polynomial, this gives the rank bound without the axiom
    spdp_profile_generators. -/
theorem rank_bound_of_boundedWithinProfileFinrank {n L : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (constraintType : Fin L → ConstraintType)
    (p : MvPolynomial (Fin n) ℚ)
    (hp : p = Finset.univ.prod factors)
    (hwithin : BoundedWithinProfileFinrankClaim B κ ℓ factors constraintType) :
    mlBlockedSpdpRank B κ ℓ p ≤ combinedProfileBound κ :=
  rank_le_combinedBound_of_hasFiniteProfileCover B κ ℓ p
    (hasFiniteProfileCover_of_boundedWithinProfileFinrank B κ ℓ factors constraintType p hp hwithin)

/-! ## Part 9: Arithmetic identities for the profile bounds -/

/-- The within-profile bound ∏_τ C(h(τ)+2,2) ≤ (κ+1)^8 matches the
    withinProfileBound constant. -/
theorem withinProfileBound_eq_pow8 (κ : ℕ) :
    withinProfileBound κ = (κ + 1) ^ 8 := by
  unfold withinProfileBound; rfl

/-- For reference: the combined bound (κ+1)^4 × (κ+1)^8 = (κ+1)^12. -/
theorem combinedBound_factorization (κ : ℕ) :
    profileCount κ * withinProfileBound κ = combinedProfileBound κ := by
  rfl

/-- profileCount matches the bounded profile count. -/
theorem profileCount_eq_pow4 (κ : ℕ) :
    profileCount κ = (κ + 1) ^ 4 := by
  unfold profileCount; rfl

/-! ## Part 10: Module.Finite for allBoundedProfilePostSpan

The generators of allBoundedProfilePostSpan are of the form mlProj(shift * g),
which are multilinear polynomials. Since multilinear polynomials on Fin n
form a finite-dimensional space (dimension 2^n, spanned by mlMonomialBasis),
allBoundedProfilePostSpan is contained in this finite-dimensional space
and hence is itself finite-dimensional.

This establishes the Module.Finite part of BoundedWithinProfileFinrankClaim.
The finrank bound ≤ (κ+1)^8 requires the symmetric power analysis. -/

/-- Every element of mlProj's image is multilinear. -/
theorem mlProj_support_isMultilinear {n : ℕ}
    (p : MvPolynomial (Fin n) ℚ)
    (α : Fin n →₀ ℕ) (hα : α ∈ (mlProj p).support) :
    Finsupp.IsMultilinear α := by
  by_contra h_neg
  have : MvPolynomial.coeff α (mlProj p) = 0 := by
    show (Finsupp.filter (fun β => Finsupp.IsMultilinear β) p) α = 0
    rw [Finsupp.filter_apply]
    exact if_neg h_neg
  exact absurd this (Finsupp.mem_support_iff.mp hα)

/-- mlProj p lies in span(mlMonomialBasis Finset.univ). -/
theorem mlProj_mem_span_mlMonomialBasis {n : ℕ}
    (p : MvPolynomial (Fin n) ℚ) :
    mlProj p ∈ Submodule.span ℚ
      (↑(MlProjFar.mlMonomialBasis (Finset.univ : Finset (Fin n))) :
        Set (MvPolynomial (Fin n) ℚ)) := by
  apply MlProjFar.mlProj_in_span_of_vars_subset
  · exact fun α hα => mlProj_support_isMultilinear p α hα
  · exact fun _ _ => Finset.mem_univ _

/-- allBoundedProfilePostSpan is contained in a finite-dimensional ambient space. -/
theorem allBoundedProfilePostSpan_le_mlMonomialBasis_span {n L : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (constraintType : Fin L → ConstraintType)
    (h : ProfileHistogram) :
    allBoundedProfilePostSpan B κ ℓ factors constraintType h ≤
      Submodule.span ℚ
        (↑(MlProjFar.mlMonomialBasis (Finset.univ : Finset (Fin n))) :
          Set (MvPolynomial (Fin n) ℚ)) := by
  apply Submodule.span_le.mpr
  intro q hq
  simp only [Set.mem_iUnion, Set.mem_image] at hq
  obtain ⟨_S, _hSlen, _shift, _hshiftvars, _g, _hg_mem, rfl⟩ := hq
  exact mlProj_mem_span_mlMonomialBasis _

/-- allBoundedProfilePostSpan is finite-dimensional. -/
instance allBoundedProfilePostSpan_finite {n L : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (constraintType : Fin L → ConstraintType)
    (h : ProfileHistogram) :
    Module.Finite ℚ ↥(allBoundedProfilePostSpan B κ ℓ factors constraintType h) := by
  have hle := allBoundedProfilePostSpan_le_mlMonomialBasis_span B κ ℓ factors constraintType h
  have hfin : Module.Finite ℚ
      (Submodule.span ℚ
        (↑(MlProjFar.mlMonomialBasis (Finset.univ : Finset (Fin n))) :
          Set (MvPolynomial (Fin n) ℚ))) :=
    Module.Finite.span_of_finite ℚ (Finset.finite_toSet _)
  exact Module.Finite.of_injective
    (Submodule.inclusion hle)
    (Submodule.inclusion_injective hle)

/-! ## Part 11: Towards the finrank bound

With Module.Finite established, the remaining challenge is proving
finrank ≤ withinProfileBound κ = (κ+1)^8.

The mathematical argument: for degree-≤-2 factors with bounded profile h,
the classified set has a finite spanning structure controlled by the
symmetric power dimension formula. -/

/-- Degree-2 killing: iterDerivList of a list of length ≥ 3 applied to a
    degree-≤-2 polynomial gives 0. This is key for bounding the classified set. -/
theorem iterDerivList_eq_zero_of_degree2_length3 {n : ℕ}
    (S : List (Fin n)) (f : MvPolynomial (Fin n) ℚ)
    (hf : f.totalDegree ≤ 2) (hS : S.length ≥ 3) :
    iterDerivList S f = 0 :=
  iterDerivList_eq_zero_of_totalDegree_lt S f (by omega)

/-- For degree-≤-2 factors, a distribution where any single factor receives
    ≥ 3 derivatives produces 0 in the product. -/
theorem distribDerivProd_eq_zero_of_overDiff {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (hfactors : ∀ i, (factors i).totalDegree ≤ 2)
    (d : Fin L → List (Fin n))
    (i₀ : Fin L) (hi₀ : (d i₀).length ≥ 3) :
    Finset.univ.prod (fun i => iterDerivList (d i) (factors i)) = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ i₀)
  exact iterDerivList_eq_zero_of_degree2_length3 (d i₀) (factors i₀) (hfactors i₀) hi₀

end WithinProfileBound
