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

/-! ## Part 11a: Factored axiom target for the within-profile finrank bound

With Module.Finite established, the full BoundedWithinProfileFinrankClaim
reduces to the pure finrank inequality. This is a cleaner axiom target
because it separates the "finiteness" (proved) from the "bound" (requires
symmetric power argument). -/

/-- The pure finrank bound: each bounded-distribution profile subspace has
    finrank ≤ withinProfileBound κ = (κ+1)^8.

    This is the REMAINING UNPROVED CONTENT of BoundedWithinProfileFinrankClaim.
    Module.Finite is already established (Part 10).

    The mathematical content: for degree-2 factors with bounded profile h,
    the symmetric power factorization gives
      finrank(allBoundedProfilePostSpan h) ≤ ∏_τ C(h(τ)+2, 2) ≤ (κ+1)^8.

    This requires showing that the span of post-processed locally-bounded
    products factors through ⊗_τ Sym^{h(τ)}(W_τ) where dim(W_τ) ≤ 3. -/
def WithinProfileFinrankBound {n L : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (constraintType : Fin L → ConstraintType) : Prop :=
  ∀ (h : ProfileHistogram),
    Module.finrank ℚ ↥(allBoundedProfilePostSpan B κ ℓ factors constraintType h)
      ≤ withinProfileBound κ

/-- WithinProfileFinrankBound implies BoundedWithinProfileFinrankClaim
    (by combining with the already-proved Module.Finite). -/
theorem boundedWithinProfileFinrankClaim_of_finrankBound {n L : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (constraintType : Fin L → ConstraintType)
    (hbound : WithinProfileFinrankBound B κ ℓ factors constraintType) :
    BoundedWithinProfileFinrankClaim B κ ℓ factors constraintType :=
  fun h => ⟨allBoundedProfilePostSpan_finite B κ ℓ factors constraintType h, hbound h⟩

/-- Direct chain: WithinProfileFinrankBound → SPDP rank ≤ combinedProfileBound.
    This bypasses the axiom spdp_profile_generators entirely once
    WithinProfileFinrankBound is proved for the Cook-Levin compilation. -/
theorem rank_bound_of_withinProfileFinrankBound {n L : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (constraintType : Fin L → ConstraintType)
    (p : MvPolynomial (Fin n) ℚ)
    (hp : p = Finset.univ.prod factors)
    (hbound : WithinProfileFinrankBound B κ ℓ factors constraintType) :
    mlBlockedSpdpRank B κ ℓ p ≤ combinedProfileBound κ :=
  rank_bound_of_boundedWithinProfileFinrank B κ ℓ factors constraintType p hp
    (boundedWithinProfileFinrankClaim_of_finrankBound B κ ℓ factors constraintType hbound)

/-! ## Part 12: Local derivative classification for degree-2 factors

For a degree-≤-2 polynomial f with vars ⊆ {v₁, v₂}, the possible results of
iterDerivList d f for d ⊆ S are:
- |d| = 0: f itself
- |d| = 1: pderiv v f for some v ∈ S  (nonzero only when v ∈ vars(f))
- |d| = 2: pderiv v₁ (pderiv v₂ f) for v₁,v₂ ∈ S  (a constant or zero)
- |d| ≥ 3: 0

The key structural fact: iterDerivList d f depends only on the MULTISET of
variables in d (by commutativity of partial derivatives). For degree-2 f,
the multiset has at most 2 elements. So the local derivative space has
dimension ≤ 1 + |vars(f)| + 1 ≤ 4 (for |vars(f)| ≤ 2). -/

/-- For degree-≤-2 factors, iterDerivList with a list of length > 2 gives 0. -/
theorem iterDerivList_degree2_vanishes_length_gt2 {n : ℕ}
    (d : List (Fin n)) (f : MvPolynomial (Fin n) ℚ)
    (hf : f.totalDegree ≤ 2) (hd : d.length > 2) :
    iterDerivList d f = 0 :=
  iterDerivList_eq_zero_of_totalDegree_lt d f (by omega)

/-- For degree-≤-2 factors, a classified element g is either 0 or is a product
    where each factor gets at most 2 derivatives. In the latter case, each
    iterDerivList(d_i)(f_i) is already determined by the local derivative
    structure of f_i.

    This means the classified set for degree-2 factors is contained in {0}
    together with the set of products of "local derivative results." -/
theorem boundedProfileClassifiedSet_degree2_dichotomy {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (hfactors : ∀ i, (factors i).totalDegree ≤ 2)
    (constraintType : Fin L → ConstraintType)
    (S : List (Fin n))
    (h : ProfileHistogram)
    (g : MvPolynomial (Fin n) ℚ)
    (hg : g ∈ boundedProfileClassifiedSet factors constraintType S h) :
    g = 0 ∨ ∃ (d : Fin L → List (Fin n)),
      (∀ i, ∀ v ∈ d i, v ∈ S) ∧
      g = Finset.univ.prod (fun i => iterDerivList (d i) (factors i)) ∧
      derivCountProfile constraintType d = h ∧
      (∀ i, (d i).length ≤ 2) := by
  rcases hg with ⟨d, hd_elts, hg_eq, hprof, hd_len⟩
  -- Check if any factor gets ≥ 3 derivatives
  by_cases h_all : ∀ i, (d i).length ≤ 2
  · -- All factors get ≤ 2 derivatives: the product is determined by local choices
    right
    exact ⟨d, hd_elts, hg_eq, hprof, h_all⟩
  · -- Some factor gets ≥ 3 derivatives: the product is 0
    left
    push_neg at h_all
    obtain ⟨i₀, hi₀⟩ := h_all
    rw [hg_eq]
    exact distribDerivProd_eq_zero_of_overDiff factors hfactors d i₀ (by omega)

/-- The classified set for degree-2 factors is contained in the span of
    products where each factor contributes at most 2 derivatives.

    Combined with the fact that the zero element is in any span, this shows
    the classified set lies in the span of the "locally bounded" products. -/
noncomputable def locallyBoundedClassifiedSet {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (constraintType : Fin L → ConstraintType)
    (S : List (Fin n))
    (h : ProfileHistogram) :
    Set (MvPolynomial (Fin n) ℚ) :=
  { g | ∃ (d : Fin L → List (Fin n)),
      (∀ i, ∀ v ∈ d i, v ∈ S) ∧
      g = Finset.univ.prod (fun i => iterDerivList (d i) (factors i)) ∧
      derivCountProfile constraintType d = h ∧
      (∀ i, (d i).length ≤ 2) }

/-- For degree-2 factors, the bounded classified set is contained in
    {0} ∪ locallyBoundedClassifiedSet. -/
theorem boundedProfileClassifiedSet_subset_locally_bounded {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (hfactors : ∀ i, (factors i).totalDegree ≤ 2)
    (constraintType : Fin L → ConstraintType)
    (S : List (Fin n))
    (h : ProfileHistogram) :
    boundedProfileClassifiedSet factors constraintType S h ⊆
      {0} ∪ locallyBoundedClassifiedSet factors constraintType S h := by
  intro g hg
  rcases boundedProfileClassifiedSet_degree2_dichotomy factors hfactors constraintType S h g hg with
    h0 | ⟨d, hd_elts, hg_eq, hprof, hd_bound⟩
  · left; exact Set.mem_singleton_iff.mpr h0
  · right; exact ⟨d, hd_elts, hg_eq, hprof, hd_bound⟩

/-- Span of {0} ∪ T equals span of T (since 0 is in every span). -/
theorem span_union_zero_eq {V : Type*} [AddCommGroup V] [Module ℚ V]
    (T : Set V) :
    Submodule.span ℚ ({(0 : V)} ∪ T) = Submodule.span ℚ T := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    rcases hx with h0 | hT
    · rw [Set.mem_singleton_iff.mp h0]; exact Submodule.zero_mem _
    · exact Submodule.subset_span hT
  · exact Submodule.span_mono Set.subset_union_right

/-- For degree-2 factors, the bounded profile post-span for fixed S and shift
    is contained in the span of post-processed locally-bounded classified elements. -/
theorem boundedProfilePostSpan_le_locallyBounded_for_degree2 {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (hfactors : ∀ i, (factors i).totalDegree ≤ 2)
    (constraintType : Fin L → ConstraintType)
    (S : List (Fin n)) (shift : MvPolynomial (Fin n) ℚ)
    (h : ProfileHistogram) :
    boundedProfilePostSpan factors constraintType S shift h ≤
      Submodule.span ℚ
        ((fun g => mlProj (shift * g)) '' locallyBoundedClassifiedSet factors constraintType S h) := by
  apply Submodule.span_le.mpr
  intro x hx
  rcases hx with ⟨g, hg_mem, rfl⟩
  rcases boundedProfileClassifiedSet_degree2_dichotomy factors hfactors constraintType S h g hg_mem with
    h0 | ⟨d, hd_elts, hg_eq, hprof, hd_bound⟩
  · -- g = 0, so mlProj(shift * g) = mlProj(shift * 0) = 0 ∈ any span
    simp [h0]
  · -- g ∈ locallyBoundedClassifiedSet
    exact Submodule.subset_span (Set.mem_image_of_mem _ ⟨d, hd_elts, hg_eq, hprof, hd_bound⟩)

/-! ## Part 13: Post-processing as a linear map

The map mlProj(shift * ·) is a linear map from polynomials to polynomials.
This lets us express the per-S-shift post-span as a linear image,
which is key for finrank arguments. -/

/-- mlProj ∘ (shift * ·) as a linear map. -/
noncomputable def postProcessLinearMap {n : ℕ}
    (shift : MvPolynomial (Fin n) ℚ) :
    MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ :=
  (mlProjLinearMap (Fin n) ℚ).comp (LinearMap.mulLeft ℚ shift)

/-- postProcessLinearMap computes mlProj(shift * ·). -/
theorem postProcessLinearMap_apply {n : ℕ}
    (shift g : MvPolynomial (Fin n) ℚ) :
    postProcessLinearMap shift g = mlProj (shift * g) := by
  simp [postProcessLinearMap, mlProjLinearMap]

/-! ## Part 14: Finite-dimensional per-S-shift post-span

The per-S-shift post-span is finite-dimensional because its generators
are multilinear polynomials (in the image of mlProj). -/

/-- The per-S-shift post-span is contained in the multilinear monomial
    space and hence is finite-dimensional. -/
instance boundedProfilePostSpan_perSShift_finite {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (constraintType : Fin L → ConstraintType)
    (S : List (Fin n))
    (shift : MvPolynomial (Fin n) ℚ)
    (h : ProfileHistogram) :
    Module.Finite ℚ ↥(boundedProfilePostSpan factors constraintType S shift h) := by
  have hle : boundedProfilePostSpan factors constraintType S shift h ≤
      Submodule.span ℚ
        (↑(MlProjFar.mlMonomialBasis (Finset.univ : Finset (Fin n))) :
          Set (MvPolynomial (Fin n) ℚ)) := by
    apply Submodule.span_le.mpr
    intro q hq
    rcases hq with ⟨g, _, rfl⟩
    exact mlProj_mem_span_mlMonomialBasis _
  have hfin : Module.Finite ℚ
      (Submodule.span ℚ
        (↑(MlProjFar.mlMonomialBasis (Finset.univ : Finset (Fin n))) :
          Set (MvPolynomial (Fin n) ℚ))) :=
    Module.Finite.span_of_finite ℚ (Finset.finite_toSet _)
  exact Module.Finite.of_injective
    (Submodule.inclusion hle)
    (Submodule.inclusion_injective hle)

/-! ## Part 15: Reduction of WithinProfileFinrankBound to per-S-shift bounds

We show that if every per-S-shift post-span has bounded finrank, then
WithinProfileFinrankBound holds (provided the shifts are constrained to
lie in a bounded-dimensional space).

The key structural insight: the allBoundedProfilePostSpan is a span of
a union over (S, shift) pairs. When the post-processing is a linear map,
the finrank of the total span can be bounded by the sum of per-S-shift
finranks only if the number of (S, shift) pairs is bounded. In the
Cook-Levin setting, block-admissibility and degree constraints achieve
this; in the abstract setting, the bound requires additional hypotheses.

For the Cook-Levin case, the axiom `spdp_profile_generators` provides
the explicit generators. The structural lemmas in Parts 7-12 reduce the
problem to: within each profile, the symmetric power factorization
collapses the generators to ≤ (κ+1)^8 independent directions. This
symmetric power argument is the content of the axiom. -/

/-- The per-S-shift post-span for degree-2 factors is ≤ the post-span
    of the locally bounded classified set. Combined with a finite
    spanning set for the locally bounded classified set, this gives
    a finrank bound for the per-S-shift case. -/
theorem boundedProfilePostSpan_le_map_locallyBounded {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (hfactors : ∀ i, (factors i).totalDegree ≤ 2)
    (constraintType : Fin L → ConstraintType)
    (S : List (Fin n)) (shift : MvPolynomial (Fin n) ℚ)
    (h : ProfileHistogram) :
    boundedProfilePostSpan factors constraintType S shift h ≤
      Submodule.map (postProcessLinearMap shift)
        (Submodule.span ℚ (locallyBoundedClassifiedSet factors constraintType S h)) := by
  -- The post-span for degree-2 factors is ≤ span of post-processed locally bounded set
  calc boundedProfilePostSpan factors constraintType S shift h
      ≤ Submodule.span ℚ
          ((fun g => mlProj (shift * g)) '' locallyBoundedClassifiedSet factors constraintType S h) :=
        boundedProfilePostSpan_le_locallyBounded_for_degree2
          factors hfactors constraintType S shift h
    _ ≤ Submodule.map (postProcessLinearMap shift)
          (Submodule.span ℚ (locallyBoundedClassifiedSet factors constraintType S h)) := by
        apply Submodule.span_le.mpr
        intro q hq
        rcases hq with ⟨g, hg, rfl⟩
        exact ⟨g, Submodule.subset_span hg, rfl⟩

/-- For degree-2 factors, if the span of the locally bounded classified set
    (for fixed S and profile h) has finrank ≤ N, then the per-S-shift
    post-span has finrank ≤ N (for any shift).

    This reduces the post-span finrank bound to a pure combinatorial
    counting problem on the classified set, independent of the shift. -/
theorem boundedProfilePostSpan_finrank_le_of_locallyBounded_finrank {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (hfactors : ∀ i, (factors i).totalDegree ≤ 2)
    (constraintType : Fin L → ConstraintType)
    (S : List (Fin n)) (shift : MvPolynomial (Fin n) ℚ)
    (h : ProfileHistogram) (N : ℕ)
    (hN : Module.finrank ℚ ↥(Submodule.span ℚ
        (locallyBoundedClassifiedSet factors constraintType S h)) ≤ N) :
    Module.finrank ℚ ↥(boundedProfilePostSpan factors constraintType S shift h) ≤ N := by
  have hle := boundedProfilePostSpan_le_map_locallyBounded
    factors hfactors constraintType S shift h
  have hfin_src : Module.Finite ℚ ↥(Submodule.span ℚ
      (locallyBoundedClassifiedSet factors constraintType S h)) := by
    -- The locally bounded classified set elements are products of degree-≤-2
    -- polynomials (each factor has degree ≤ 2 after ≤ 2 derivatives), so each
    -- product has totalDegree ≤ 2*L. The span lies in restrictTotalDegree,
    -- which is finite-dimensional.
    have hle_deg : Submodule.span ℚ (locallyBoundedClassifiedSet factors constraintType S h) ≤
        MvPolynomial.restrictTotalDegree (Fin n) ℚ (2 * L) := by
      apply Submodule.span_le.mpr
      intro q hq
      rcases hq with ⟨d, _, hg_eq, _, hd_bound⟩
      show q ∈ MvPolynomial.restrictTotalDegree (Fin n) ℚ (2 * L)
      rw [MvPolynomial.mem_restrictTotalDegree, hg_eq]
      calc (Finset.univ.prod (fun i => iterDerivList (d i) (factors i))).totalDegree
          ≤ ∑ i ∈ Finset.univ, (iterDerivList (d i) (factors i)).totalDegree :=
            MvPolynomial.totalDegree_finset_prod _ _
        _ ≤ ∑ _i ∈ Finset.univ, 2 := by
            apply Finset.sum_le_sum
            intro i _
            exact le_trans (totalDegree_iterDerivList_le _ _) (hfactors i)
        _ = 2 * L := by simp [Finset.sum_const, mul_comm]
    exact Module.Finite.of_injective (Submodule.inclusion hle_deg)
      (Submodule.inclusion_injective hle_deg)
  calc Module.finrank ℚ ↥(boundedProfilePostSpan factors constraintType S shift h)
      ≤ Module.finrank ℚ ↥(Submodule.map (postProcessLinearMap shift)
          (Submodule.span ℚ (locallyBoundedClassifiedSet factors constraintType S h))) :=
        Submodule.finrank_mono hle
    _ ≤ Module.finrank ℚ ↥(Submodule.span ℚ
          (locallyBoundedClassifiedSet factors constraintType S h)) :=
        Submodule.finrank_map_le _ _
    _ ≤ N := hN

/-! ## Part 16: Finiteness of bounded classified sets

We show the boundedProfileClassifiedSet for fixed S is finite, by
exhibiting an injection from derivative assignments to a finite type.

Each derivative assignment d : Fin L → List (Fin n) with |d_i| ≤ 2 and
d_i ⊆ S is determined by choosing, for each factor i, a list of at most
2 elements from S. The set of such choices is finite.

We use this to bound the finrank of the per-S-shift post-span. -/

/-- The bounded profile classified set is finite for any fixed S.

    Each element is determined by a derivative assignment d, and the
    set of valid assignments is finite (each d_i is a list of at most
    |S| elements from Fin n, and Fin n is finite). -/
theorem boundedProfileClassifiedSet_finite {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (constraintType : Fin L → ConstraintType)
    (S : List (Fin n))
    (h : ProfileHistogram) :
    Set.Finite (boundedProfileClassifiedSet factors constraintType S h) := by
  -- The classified set is the image of the product map on valid assignments.
  -- We show it's contained in a finite image.
  suffices hfin : Set.Finite { d : Fin L → List (Fin n) |
      (∀ i, ∀ v ∈ d i, v ∈ S) ∧
      derivCountProfile constraintType d = h ∧
      ∑ i : Fin L, (d i).length ≤ S.length } by
    apply Set.Finite.subset (hfin.image
      (fun d => Finset.univ.prod (fun i => iterDerivList (d i) (factors i))))
    intro g hg
    rcases hg with ⟨d, hd1, rfl, hd2, hd3⟩
    exact ⟨d, ⟨hd1, hd2, hd3⟩, rfl⟩
  -- The set of valid d is contained in the set of functions
  -- Fin L → {sublists of S}, which is finite by Finite.pi'.
  -- Each d_i is a list of Fin n of length ≤ |S| (from the total length constraint).
  -- Lists of bounded length over a finite type form a finite set.
  -- The product (Fin L → bounded lists) is then finite.
  have hfin_lists : Set.Finite {l : List (Fin n) | l.length ≤ S.length} :=
    List.finite_length_le (Fin n) S.length
  haveI : Finite {l : List (Fin n) // l.length ≤ S.length} := hfin_lists.to_subtype
  apply Set.Finite.subset
    ((Set.toFinite (Set.univ : Set (Fin L → { l : List (Fin n) // l.length ≤ S.length }))).image
      (fun f i => (f i).val))
  intro d hd
  rcases hd with ⟨hd_elts, _, hd_len⟩
  refine ⟨fun i => ⟨d i, ?_⟩, Set.mem_univ _, funext (fun _ => rfl)⟩
  exact le_trans (Finset.single_le_sum (f := fun i => (d i).length)
    (fun j _ => Nat.zero_le _) (Finset.mem_univ i)) hd_len

/-- The locally bounded classified set is also finite.
    Each d_i has length ≤ 2, and lists of bounded length over Fin n are finite. -/
theorem locallyBoundedClassifiedSet_finite {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (constraintType : Fin L → ConstraintType)
    (S : List (Fin n))
    (h : ProfileHistogram) :
    Set.Finite (locallyBoundedClassifiedSet factors constraintType S h) := by
  suffices hfin : Set.Finite { d : Fin L → List (Fin n) |
      (∀ i, ∀ v ∈ d i, v ∈ S) ∧
      derivCountProfile constraintType d = h ∧
      (∀ i, (d i).length ≤ 2) } by
    apply Set.Finite.subset (hfin.image
      (fun d => Finset.univ.prod (fun i => iterDerivList (d i) (factors i))))
    intro g hg
    rcases hg with ⟨d, hd1, rfl, hd2, hd3⟩
    exact ⟨d, ⟨hd1, hd2, hd3⟩, rfl⟩
  -- Each d_i is a list of Fin n of length ≤ 2.
  have hfin_lists : Set.Finite {l : List (Fin n) | l.length ≤ 2} :=
    List.finite_length_le (Fin n) 2
  haveI : Finite {l : List (Fin n) // l.length ≤ 2} := hfin_lists.to_subtype
  apply Set.Finite.subset
    ((Set.toFinite (Set.univ : Set (Fin L → { l : List (Fin n) // l.length ≤ 2 }))).image
      (fun f i => (f i).val))
  intro d hd
  rcases hd with ⟨_, _, hd_bound⟩
  exact ⟨fun i => ⟨d i, hd_bound i⟩, Set.mem_univ _, funext (fun _ => rfl)⟩

/-! ## Part 17: Using finiteness for finrank bounds

With the classified sets proved finite, we can bound the finrank of the
per-S-shift post-span by the cardinality of the classified set's image. -/

/-- For degree-2 factors, the per-S-shift post-span has finrank bounded by
    the number of locally bounded classified elements.

    Proof: The post-span is contained in the span of the post-processed
    image of the locally bounded classified set (Part 12). The image is
    finite (Part 16). The finrank of the span of a finite set ≤ its
    cardinality (finrank_span_le_card). -/
theorem boundedProfilePostSpan_finrank_le_card_locallyBounded {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (hfactors : ∀ i, (factors i).totalDegree ≤ 2)
    (constraintType : Fin L → ConstraintType)
    (S : List (Fin n)) (shift : MvPolynomial (Fin n) ℚ)
    (h : ProfileHistogram) :
    Module.finrank ℚ ↥(boundedProfilePostSpan factors constraintType S shift h) ≤
      (locallyBoundedClassifiedSet_finite factors constraintType S h).toFinset.card := by
  -- Post-span ≤ span of post-processed locally bounded set (Part 12)
  have hle := boundedProfilePostSpan_le_locallyBounded_for_degree2
    factors hfactors constraintType S shift h
  -- The post-processed image is finite
  have hfin_img := (locallyBoundedClassifiedSet_finite factors constraintType S h).image
    (fun g => mlProj (shift * g))
  haveI : Fintype ↥((fun g => mlProj (shift * g)) ''
      locallyBoundedClassifiedSet factors constraintType S h) := hfin_img.fintype
  -- Give Fintype instances for the finite sets
  haveI : Fintype ↥(locallyBoundedClassifiedSet factors constraintType S h) :=
    (locallyBoundedClassifiedSet_finite factors constraintType S h).fintype
  -- The post-processed image set is finite
  let imgSet := (fun g => mlProj (shift * g)) '' locallyBoundedClassifiedSet factors constraintType S h
  -- Build a Finset that spans the post-span
  let G : Finset (MvPolynomial (Fin n) ℚ) :=
    Finset.image (fun g => mlProj (shift * g))
      (locallyBoundedClassifiedSet_finite factors constraintType S h).toFinset
  have hG_span : boundedProfilePostSpan factors constraintType S shift h ≤
      Submodule.span ℚ (↑G : Set (MvPolynomial (Fin n) ℚ)) := by
    apply le_trans hle
    apply Submodule.span_mono
    intro q hq
    rcases hq with ⟨g, hg, rfl⟩
    simp only [G, Finset.coe_image, Set.mem_image]
    exact ⟨g, (Set.Finite.mem_toFinset _).mpr hg, rfl⟩
  -- finrank(post-span) ≤ finrank(span G) ≤ card G ≤ card of locally bounded set
  calc Module.finrank ℚ ↥(boundedProfilePostSpan factors constraintType S shift h)
      ≤ Module.finrank ℚ ↥(Submodule.span ℚ (↑G : Set (MvPolynomial (Fin n) ℚ))) :=
        Submodule.finrank_mono hG_span
    _ ≤ G.card := finrank_span_finset_le_card G
    _ ≤ (locallyBoundedClassifiedSet_finite factors constraintType S h).toFinset.card :=
        Finset.card_image_le

/-! ## Part 18: Roadmap for completing WithinProfileFinrankBound

### What is proved (Parts 10-17):

1. `allBoundedProfilePostSpan_finite` — the all-S-shift post-span is
   finite-dimensional (submodule of the 2^n-dimensional multilinear space).

2. `boundedProfilePostSpan_le_locallyBounded_for_degree2` — for degree-2
   factors, the per-S-shift post-span ≤ span of post-processed locally
   bounded set.

3. `boundedProfilePostSpan_finrank_le_of_locallyBounded_finrank` —
   the per-S-shift post-span finrank ≤ finrank(span of classified set),
   using the fact that the post-processing is a linear map.

4. `locallyBoundedClassifiedSet_finite` — the classified set is finite.

5. `boundedProfilePostSpan_finrank_le_card_locallyBounded` —
   the per-S-shift finrank ≤ |classified set| (combining 2-4).

### What remains for WithinProfileFinrankBound:

**Per-S-shift bound**: To show finrank(per-S-shift post-span) ≤ (κ+1)^8
for admissible h, one needs:
  |locallyBoundedClassifiedSet| ≤ ∏_τ C(h(τ)+2, 2) ≤ (κ+1)^8

This is the TEMPLATE COUNTING step: the locally bounded classified
set has ≤ ∏_τ C(h(τ)+2, 2) distinct elements. The mathematical
argument is that two assignments d₁, d₂ that produce the same
"local derivative atom" choices for each factor give the same product.
The number of distinct atom-choice tuples is ∏_τ dim(Sym^{h(τ)}(W_τ))
where W_τ is the local derivative space (dim ≤ 3 for degree-2 factors).

**All-S-shift bound**: Even with the per-S-shift bound proved, the
allBoundedProfilePostSpan unions over ALL S and shifts. Bounding
finrank(allBoundedProfilePostSpan) ≤ (κ+1)^8 requires showing that
the results for different (S, shift) pairs are linearly dependent.
In the Cook-Levin setting, the symmetric power factorization
achieves this — the products factor as OUTER PRODUCTS of local atoms,
and the local atoms depend only on the factor structure (not on S).

This is the content of the axiom `spdp_profile_generators`. -/

/-- Symmetric power gap: if the classified set for fixed S has at most
    N elements, then the per-S-shift post-span has finrank ≤ N.
    Combined with the template count N = ∏_τ C(h(τ)+2,2) ≤ (κ+1)^8,
    this gives the per-S-shift version of WithinProfileFinrankBound.

    This theorem packages Parts 14-17 into a clean statement. -/
theorem perSShift_finrank_of_classified_card_bound {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (hfactors : ∀ i, (factors i).totalDegree ≤ 2)
    (constraintType : Fin L → ConstraintType)
    (S : List (Fin n)) (shift : MvPolynomial (Fin n) ℚ)
    (h : ProfileHistogram) (N : ℕ)
    (hcard : (locallyBoundedClassifiedSet_finite factors constraintType S h).toFinset.card ≤ N) :
    Module.finrank ℚ ↥(boundedProfilePostSpan factors constraintType S shift h) ≤ N :=
  le_trans (boundedProfilePostSpan_finrank_le_card_locallyBounded
    factors hfactors constraintType S shift h) hcard

/-! ## Part 19: Multiset-assignment reduction

Two list-assignments that differ only by permuting elements within each
factor produce the same product polynomial. This follows from
`iterDerivList_perm`: iterDerivList is invariant under permutation.

This reduces the cardinality of locallyBoundedClassifiedSet from the
number of list-assignments to the number of multiset-assignments. -/

/-- Two list-assignments that agree on multisets produce the same product. -/
theorem distribDerivProd_eq_of_multiset_eq {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (d₁ d₂ : Fin L → List (Fin n))
    (h_multi : ∀ i, (d₁ i).Perm (d₂ i)) :
    Finset.univ.prod (fun i => iterDerivList (d₁ i) (factors i)) =
    Finset.univ.prod (fun i => iterDerivList (d₂ i) (factors i)) := by
  apply Finset.prod_congr rfl
  intro i _
  exact IterDerivHelpers.iterDerivList_perm (h_multi i) (factors i)

/-- Two elements of locallyBoundedClassifiedSet that come from
    list-assignments d₁, d₂ with d₁ i ~ d₂ i for all i produce
    the same polynomial. This collapses list-ordering redundancy. -/
theorem locallyBoundedClassifiedSet_perm_collapse {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (constraintType : Fin L → ConstraintType)
    (S : List (Fin n))
    (h : ProfileHistogram)
    (d₁ d₂ : Fin L → List (Fin n))
    (h₁ : ∀ i, ∀ v ∈ d₁ i, v ∈ S)
    (h₂ : ∀ i, ∀ v ∈ d₂ i, v ∈ S)
    (hprof₁ : derivCountProfile constraintType d₁ = h)
    (hprof₂ : derivCountProfile constraintType d₂ = h)
    (hb₁ : ∀ i, (d₁ i).length ≤ 2)
    (hb₂ : ∀ i, (d₂ i).length ≤ 2)
    (hperm : ∀ i, (d₁ i).Perm (d₂ i)) :
    Finset.univ.prod (fun i => iterDerivList (d₁ i) (factors i)) =
    Finset.univ.prod (fun i => iterDerivList (d₂ i) (factors i)) :=
  distribDerivProd_eq_of_multiset_eq factors d₁ d₂ hperm

/-! ## Part 21: Local derivative space containment

For degree-2 factors, `iterDerivList d f` with `|d| ≤ 2` lies in the span of
at most 4 elements: {f, ∂_{v₁} f, ∂_{v₂} f, ∂_{v₁}∂_{v₂} f} for the (at most 2)
variables v₁, v₂ in vars(f) ∩ S.

This means the products in locallyBoundedClassifiedSet factor through local
derivative spaces of bounded dimension, which is the basis for the symmetric
power finrank argument. -/

/-- For degree-2 factors with |d| = 1, the result is a single partial derivative. -/
theorem iterDerivList_singleton_eq_pderiv {n : ℕ} {F : Type*} [CommRing F]
    (v : Fin n) (f : MvPolynomial (Fin n) F) :
    iterDerivList [v] f = MvPolynomial.pderiv v f := by
  simp [IterDerivHelpers.iterDerivList_single]

/-- For |d| = 2, the result is a double partial derivative (order doesn't matter
    by pderiv_comm). -/
theorem iterDerivList_pair_eq_pderiv2 {n : ℕ} {F : Type*} [CommRing F]
    (v w : Fin n) (f : MvPolynomial (Fin n) F) :
    iterDerivList [v, w] f = MvPolynomial.pderiv v (MvPolynomial.pderiv w f) := by
  simp only [IterDerivHelpers.iterDerivList_cons, IterDerivHelpers.iterDerivList_nil]
  exact IterDerivHelpers.pderiv_comm w v f

/-- For degree-2 factors, the local derivative space (the set of all possible
    iterDerivList d f for |d| ≤ 2 with d ⊆ S) is contained in the span of
    {f} ∪ {pderiv v f | v ∈ S} ∪ {pderiv v (pderiv w f) | v, w ∈ S}.

    Since |S| ≤ κ, this span has dimension ≤ 1 + κ + κ² ≤ (κ+1)².

    For the Cook-Levin case where each factor has vars of size ≤ 2,
    only derivatives in vars(f) give nonzero results, so the effective
    dimension is ≤ 1 + 2 + 3 = 6 (but often ≤ 4). -/
theorem iterDerivList_in_local_span {n : ℕ}
    (f : MvPolynomial (Fin n) ℚ)
    (S : List (Fin n))
    (d : List (Fin n)) (hd : d.length ≤ 2) (hd_mem : ∀ v ∈ d, v ∈ S) :
    iterDerivList d f ∈ Submodule.span ℚ
      ({f} ∪
       (MvPolynomial.pderiv · f) '' S.toFinset ∪
       (⋃ v ∈ S, ⋃ w ∈ S, {MvPolynomial.pderiv v (MvPolynomial.pderiv w f)}) :
        Set (MvPolynomial (Fin n) ℚ)) := by
  rcases d with _ | ⟨v, _ | ⟨w, rest⟩⟩
  · -- d = []: result is f itself
    apply Submodule.subset_span
    left; left; exact Set.mem_singleton f
  · -- d = [v]: result is pderiv v f
    apply Submodule.subset_span
    left; right
    exact ⟨v, List.mem_toFinset.mpr (hd_mem v (by simp)), rfl⟩
  · -- d = v :: w :: rest, with |d| ≤ 2 means rest = []
    cases rest with
    | nil =>
      -- d = [v, w]: result is pderiv v (pderiv w f)
      apply Submodule.subset_span
      right
      rw [Set.mem_iUnion₂]
      have hv_mem : v ∈ S := hd_mem v (by simp)
      have hw_mem : w ∈ S := hd_mem w (by simp)
      refine ⟨v, hv_mem, ?_⟩
      rw [Set.mem_iUnion₂]
      refine ⟨w, hw_mem, ?_⟩
      rw [Set.mem_singleton_iff]
      exact iterDerivList_pair_eq_pderiv2 v w f
    | cons _ _ =>
      simp [List.length] at hd; omega

/-! ## Part 22: Local derivative space and the span of classified products

Each element of locallyBoundedClassifiedSet is a product ∏_i g_i where
g_i = iterDerivList(d_i)(f_i). By `iterDerivList_in_local_span`, each
g_i lies in a local derivative space W_i (spanned by f_i and its first-
and second-order partial derivatives w.r.t. variables in S).

This means locallyBoundedClassifiedSet ⊆ span of products-of-local-atoms,
and the finrank of that span is bounded by the product of local atom counts.

For degree-2 Cook-Levin factors:
  - Each factor touches ≤ 2 variables
  - Only derivatives in vars(f_i) give nonzero results
  - So the local derivative space for factor i has dimension ≤ 4
    (the factor itself + ≤ 2 first derivs + ≤ 1 mixed second deriv)
  - For undifferentiated factors (d_i = []), the contribution is fixed (f_i)

The symmetric power argument then bounds the finrank of the product span
to ∏_τ C(h(τ)+2, 2) ≤ (κ+1)^8. -/

/-- The local derivative atom set for factor i and derivative list S:
    all possible values of iterDerivList(d)(f_i) for d of length ≤ 2
    with elements from S. This set has ≤ 1 + |S| + |S|² elements. -/
noncomputable def localDerivAtoms {n : ℕ}
    (f : MvPolynomial (Fin n) ℚ) (S : List (Fin n)) :
    Finset (MvPolynomial (Fin n) ℚ) :=
  {f} ∪
  (S.toFinset.image (fun v => MvPolynomial.pderiv v f)) ∪
  ((S.toFinset ×ˢ S.toFinset).image (fun p => MvPolynomial.pderiv p.1 (MvPolynomial.pderiv p.2 f)))

/-- iterDerivList d f with |d| ≤ 2 and d ⊆ S lies in localDerivAtoms. -/
theorem iterDerivList_mem_localDerivAtoms {n : ℕ}
    (f : MvPolynomial (Fin n) ℚ) (S : List (Fin n))
    (d : List (Fin n)) (hd : d.length ≤ 2) (hd_mem : ∀ v ∈ d, v ∈ S) :
    iterDerivList d f ∈ (localDerivAtoms f S : Finset (MvPolynomial (Fin n) ℚ)) := by
  rcases d with _ | ⟨v, _ | ⟨w, rest⟩⟩
  · -- d = []: iterDerivList [] f = f ∈ {f}
    simp [localDerivAtoms, IterDerivHelpers.iterDerivList_nil]
  · -- d = [v]: iterDerivList [v] f = pderiv v f
    simp only [localDerivAtoms, Finset.mem_union, Finset.mem_singleton, Finset.mem_image,
      Finset.mem_product]
    left; right
    exact ⟨v, List.mem_toFinset.mpr (hd_mem v (by simp)), rfl⟩
  · -- d = v :: w :: rest, must have rest = []
    cases rest with
    | nil =>
      -- iterDerivList [v, w] f = pderiv v (pderiv w f)
      have hvw : iterDerivList [v, w] f =
          MvPolynomial.pderiv v (MvPolynomial.pderiv w f) :=
        iterDerivList_pair_eq_pderiv2 v w f
      rw [hvw]
      simp only [localDerivAtoms, Finset.mem_union, Finset.mem_singleton, Finset.mem_image,
        Finset.mem_product]
      right
      exact ⟨(v, w), ⟨List.mem_toFinset.mpr (hd_mem v (by simp)),
        List.mem_toFinset.mpr (hd_mem w (by simp))⟩, rfl⟩
    | cons _ _ =>
      simp [List.length] at hd; omega

/-- The cardinality of localDerivAtoms is bounded by (|S|+1)². -/
theorem localDerivAtoms_card_le {n : ℕ}
    (f : MvPolynomial (Fin n) ℚ) (S : List (Fin n)) :
    (localDerivAtoms f S).card ≤ (S.toFinset.card + 1) ^ 2 := by
  unfold localDerivAtoms
  calc (({f} ∪
      S.toFinset.image (fun v => MvPolynomial.pderiv v f) ∪
      (S.toFinset ×ˢ S.toFinset).image
        (fun p => MvPolynomial.pderiv p.1 (MvPolynomial.pderiv p.2 f))) : Finset _).card
      ≤ 1 + S.toFinset.card + S.toFinset.card ^ 2 := by
        calc _ ≤ ({f} ∪
            S.toFinset.image (fun v => MvPolynomial.pderiv v f)).card +
            ((S.toFinset ×ˢ S.toFinset).image
              (fun p => MvPolynomial.pderiv p.1 (MvPolynomial.pderiv p.2 f))).card :=
              Finset.card_union_le _ _
          _ ≤ (({f} : Finset _).card + (S.toFinset.image (fun v => MvPolynomial.pderiv v f)).card) +
              ((S.toFinset ×ˢ S.toFinset).image
                (fun p => MvPolynomial.pderiv p.1 (MvPolynomial.pderiv p.2 f))).card := by
            gcongr; exact Finset.card_union_le _ _
          _ ≤ (1 + S.toFinset.card) + S.toFinset.card ^ 2 := by
            gcongr
            · simp [Finset.card_singleton]
            · exact Finset.card_image_le
            · calc _ ≤ (S.toFinset ×ˢ S.toFinset).card := Finset.card_image_le
                _ = S.toFinset.card * S.toFinset.card := Finset.card_product _ _
                _ = S.toFinset.card ^ 2 := (sq _).symm
    _ ≤ (S.toFinset.card + 1) ^ 2 := by nlinarith

/-- Each element of locallyBoundedClassifiedSet is a product of local
    derivative atoms: ∏_i a_i where a_i ∈ localDerivAtoms(f_i, S).

    This is a direct consequence of iterDerivList_mem_localDerivAtoms. -/
theorem locallyBoundedClassifiedSet_subset_atom_products {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (constraintType : Fin L → ConstraintType)
    (S : List (Fin n))
    (h : ProfileHistogram)
    (g : MvPolynomial (Fin n) ℚ)
    (hg : g ∈ locallyBoundedClassifiedSet factors constraintType S h) :
    ∃ (atoms : Fin L → MvPolynomial (Fin n) ℚ),
      (∀ i, atoms i ∈ localDerivAtoms (factors i) S) ∧
      g = Finset.univ.prod atoms := by
  rcases hg with ⟨d, hd_elts, hg_eq, _hprof, hd_bound⟩
  refine ⟨fun i => iterDerivList (d i) (factors i), ?_, ?_⟩
  · intro i
    exact iterDerivList_mem_localDerivAtoms (factors i) S (d i) (hd_bound i) (hd_elts i)
  · exact hg_eq

/-- The atom-product spanning set: all products ∏_i a_i where
    a_i ∈ localDerivAtoms(f_i, S). -/
def atomProductSet {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ) (S : List (Fin n)) :
    Set (MvPolynomial (Fin n) ℚ) :=
  { g | ∃ (atoms : Fin L → MvPolynomial (Fin n) ℚ),
      (∀ i, atoms i ∈ localDerivAtoms (factors i) S) ∧
      g = Finset.univ.prod atoms }

/-- The locally bounded classified set is contained in the atom-product set. -/
theorem locallyBoundedClassifiedSet_subset_atomProductSet {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (constraintType : Fin L → ConstraintType)
    (S : List (Fin n))
    (h : ProfileHistogram) :
    locallyBoundedClassifiedSet factors constraintType S h ⊆
      atomProductSet factors S := by
  intro g hg
  exact locallyBoundedClassifiedSet_subset_atom_products factors constraintType S h g hg

/-- The span of locallyBoundedClassifiedSet is contained in the span of
    the atom-product set. -/
theorem span_locallyBounded_le_span_atomProducts {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (constraintType : Fin L → ConstraintType)
    (S : List (Fin n))
    (h : ProfileHistogram) :
    Submodule.span ℚ (locallyBoundedClassifiedSet factors constraintType S h) ≤
      Submodule.span ℚ (atomProductSet factors S) :=
  Submodule.span_mono (locallyBoundedClassifiedSet_subset_atomProductSet
    factors constraintType S h)

/-- The atom-product set is finite (since each localDerivAtoms is finite). -/
theorem atomProductSet_finite {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ) (S : List (Fin n)) :
    Set.Finite (atomProductSet factors S) := by
  -- The atom-product set is the image of the product map on
  -- functions that choose atoms from finite sets.
  -- We show it's finite by expressing it as a subset of a finite image.
  let atomChoices := (i : Fin L) → { a : MvPolynomial (Fin n) ℚ //
    a ∈ localDerivAtoms (factors i) S }
  haveI : Fintype atomChoices := inferInstance
  apply Set.Finite.subset (Set.toFinite (Set.range
    (fun (c : atomChoices) => Finset.univ.prod (fun i => (c i).val))))
  intro g hg
  rcases hg with ⟨atoms, hatoms, rfl⟩
  exact ⟨fun i => ⟨atoms i, hatoms i⟩, rfl⟩

/-- The atom-product set has cardinality ≤ ∏_i |localDerivAtoms(f_i, S)|.

    This follows because atomProductSet is the image of the product map
    on choices from localDerivAtoms, and the image cardinality ≤ domain
    cardinality = ∏_i |localDerivAtoms(f_i, S)|. -/
theorem atomProductSet_card_le {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ) (S : List (Fin n)) :
    (atomProductSet_finite factors S).toFinset.card ≤
      ∏ i : Fin L, (localDerivAtoms (factors i) S).card := by
  -- Express atomProductSet as an image of the product map on atom choices
  let atomChoices := (i : Fin L) → { a : MvPolynomial (Fin n) ℚ //
    a ∈ localDerivAtoms (factors i) S }
  let prodMap : atomChoices → MvPolynomial (Fin n) ℚ :=
    fun c => Finset.univ.prod (fun i => (c i).val)
  -- The atomProductSet is contained in the range of prodMap
  have hrange : atomProductSet factors S ⊆ Set.range prodMap := by
    intro g hg
    rcases hg with ⟨atoms, hatoms, rfl⟩
    exact ⟨fun i => ⟨atoms i, hatoms i⟩, rfl⟩
  -- toFinset.card ≤ card of the range ≤ card of the domain
  have hfin_range : Set.Finite (Set.range prodMap) := Set.finite_range prodMap
  calc (atomProductSet_finite factors S).toFinset.card
      ≤ hfin_range.toFinset.card := by
        apply Set.Finite.toFinset_mono
        exact hrange
    _ ≤ Fintype.card atomChoices := by
        calc _ ≤ Finset.univ.card := by
              apply le_trans (Finset.card_le_card _)
              · exact le_refl _
              · intro x hx
                exact Finset.mem_univ _
          _ = Fintype.card atomChoices := (Finset.card_univ).symm
    _ = ∏ i : Fin L, (localDerivAtoms (factors i) S).card := by
        simp [Fintype.card_pi, Fintype.card_coe]

/-- The per-S-shift post-span finrank is bounded by the product of
    local derivative atom counts: ∏_i |localDerivAtoms(f_i, S)|. -/
theorem perSShift_finrank_le_prod_localDerivAtoms {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (hfactors : ∀ i, (factors i).totalDegree ≤ 2)
    (constraintType : Fin L → ConstraintType)
    (S : List (Fin n)) (shift : MvPolynomial (Fin n) ℚ)
    (h : ProfileHistogram) :
    Module.finrank ℚ ↥(boundedProfilePostSpan factors constraintType S shift h) ≤
      ∏ i : Fin L, (localDerivAtoms (factors i) S).card :=
  le_trans (perSShift_finrank_le_atomProducts factors hfactors constraintType S shift h)
    (atomProductSet_card_le factors S)

/-- Combining with localDerivAtoms_card_le: the per-S-shift post-span finrank
    is bounded by ∏_i (|S.toFinset| + 1)² = ((|S.toFinset| + 1)²)^L. -/
theorem perSShift_finrank_le_S_card_bound {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (hfactors : ∀ i, (factors i).totalDegree ≤ 2)
    (constraintType : Fin L → ConstraintType)
    (S : List (Fin n)) (shift : MvPolynomial (Fin n) ℚ)
    (h : ProfileHistogram) :
    Module.finrank ℚ ↥(boundedProfilePostSpan factors constraintType S shift h) ≤
      (S.toFinset.card + 1) ^ (2 * L) := by
  calc Module.finrank ℚ ↥(boundedProfilePostSpan factors constraintType S shift h)
      ≤ ∏ i : Fin L, (localDerivAtoms (factors i) S).card :=
        perSShift_finrank_le_prod_localDerivAtoms factors hfactors constraintType S shift h
    _ ≤ ∏ _i : Fin L, (S.toFinset.card + 1) ^ 2 := by
        apply Finset.prod_le_prod
        · intro i _; exact Nat.zero_le _
        · intro i _; exact localDerivAtoms_card_le (factors i) S
    _ = ((S.toFinset.card + 1) ^ 2) ^ L := by
        simp [Finset.prod_const, Finset.card_fin]
    _ = (S.toFinset.card + 1) ^ (2 * L) := by ring

/-- The per-S-shift post-span finrank is bounded by the size of the
    atom-product set (which is ≤ ∏_i |localDerivAtoms(f_i, S)|).

    For the Cook-Levin case with degree-2 factors and disjoint variables,
    the atom-product span has finrank equal to the tensor product
    dimension, which by the symmetric power reduction gives ≤ (κ+1)^8.

    The full symmetric power argument is the remaining content of the
    axiom spdp_profile_generators. -/
theorem perSShift_finrank_le_atomProducts {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (hfactors : ∀ i, (factors i).totalDegree ≤ 2)
    (constraintType : Fin L → ConstraintType)
    (S : List (Fin n)) (shift : MvPolynomial (Fin n) ℚ)
    (h : ProfileHistogram) :
    Module.finrank ℚ ↥(boundedProfilePostSpan factors constraintType S shift h) ≤
      (atomProductSet_finite factors S).toFinset.card := by
  have hle : boundedProfilePostSpan factors constraintType S shift h ≤
      Submodule.map (postProcessLinearMap shift)
        (Submodule.span ℚ (atomProductSet factors S)) := by
    calc boundedProfilePostSpan factors constraintType S shift h
        ≤ Submodule.map (postProcessLinearMap shift)
            (Submodule.span ℚ (locallyBoundedClassifiedSet factors constraintType S h)) := by
          exact boundedProfilePostSpan_le_map_locallyBounded
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
    _ ≤ (atomProductSet_finite factors S).toFinset.card := by
        have : Submodule.span ℚ (atomProductSet factors S) =
            Submodule.span ℚ ↑(atomProductSet_finite factors S).toFinset := by
          congr 1
          exact (Set.Finite.coe_toFinset _).symm
        rw [this]
        exact finrank_span_finset_le_card _

end WithinProfileBound
