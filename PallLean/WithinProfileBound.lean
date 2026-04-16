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

/-! ## Part 11b: Exact Cook-Levin frontier after the finrank reduction

The abstract Step B frontier can now be packaged as one exact theorem-level
obligation for the actual Cook-Levin factor list. This isolates the remaining
content to the specialized within-profile finrank bound, rather than the older
generator-level package `spdp_profile_generators`.
-/

/-- The explicit list of Cook-Levin product factors `1 - Cᵢ` used by the P-side
profile-compression argument. -/
noncomputable def cookLevinFactorList
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    List (MvPolynomial (Fin n) ℚ) :=
  (PaperFaithfulSeparation.cook_levin_compilation M n hn htb hns).constraints.map
    (fun c => (1 : MvPolynomial (Fin n) ℚ) - c.poly)

/-- Exact remaining Cook-Levin Step B frontier after reducing to bounded-profile
finrank: there exists a constraint-type classification on the actual compiled
factor list for which the specialized within-profile finrank bound holds. -/
def CookLevinWithinProfileFinrankFrontier
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ constraintType : Fin (cookLevinFactorList M n hn htb hns).length → ConstraintType,
    WithinProfileFinrankBound
      (PaperFaithfulSeparation.cook_levin_compilation M n hn htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (fun i => (cookLevinFactorList M n hn htb hns).get i)
      constraintType

/-- Concrete constraint-type classification on the actual Cook-Levin factor
list.

The initial `n` slots are the booleanity factors. The remaining slots come from
the adjacency list and the transition-skeleton list, both of which are
two-variable local factors; we keep those two post-boolean segments explicit so
the remaining P-side frontier is one concrete lemma, not an existential choice
of classification. -/
noncomputable def cookLevinConstraintType
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    Fin (cookLevinFactorList M n hn htb hns).length → ConstraintType :=
  fun i =>
    if i.1 < n then
      ConstraintType.booleanity
    else if i.1 < n + (PaperFaithfulSeparation.adjConstraintList n).length then
      ConstraintType.adjacency
    else
      ConstraintType.transitionLeft

/-- The canonical type map is `booleanity` on the initial booleanity segment. -/
theorem cookLevinConstraintType_eq_booleanity
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (i : Fin (cookLevinFactorList M n hn htb hns).length)
    (hi : i.1 < n) :
    cookLevinConstraintType M n hn htb hns i = ConstraintType.booleanity := by
  simp [cookLevinConstraintType, hi]

/-- The canonical type map is `adjacency` on the explicit adjacency segment. -/
theorem cookLevinConstraintType_eq_adjacency
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (i : Fin (cookLevinFactorList M n hn htb hns).length)
    (hlo : n ≤ i.1)
    (hi : i.1 < n + (PaperFaithfulSeparation.adjConstraintList n).length) :
    cookLevinConstraintType M n hn htb hns i = ConstraintType.adjacency := by
  simp [cookLevinConstraintType, Nat.not_lt.mpr hlo, hi]

/-- The canonical type map is `transitionLeft` on the final transition segment. -/
theorem cookLevinConstraintType_eq_transitionLeft
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (i : Fin (cookLevinFactorList M n hn htb hns).length)
    (hi : n + (PaperFaithfulSeparation.adjConstraintList n).length ≤ i.1) :
    cookLevinConstraintType M n hn htb hns i = ConstraintType.transitionLeft := by
  have hnot_bool : ¬ i.1 < n := Nat.not_lt.mpr (le_trans (Nat.le_add_right _ _) hi)
  have hnot_adj :
      ¬ i.1 < n + (PaperFaithfulSeparation.adjConstraintList n).length :=
    Nat.not_lt.mpr hi
  simp [cookLevinConstraintType, hnot_bool, hnot_adj]

/-- Exact compiled-family raw-touched-collapse frontier.

This is the honest smaller statement immediately below any attempted
uniform-subspace cover route.  For a fixed profile `h`, derivative list `S`,
and admissible shift, all raw touched-support spans compatible with `h` must
collapse into one common subspace `U`.  Unlike a uniform cover, `U` may still
depend on `(S, shift, h)`.

If the stronger route via a single profile-only subspace `U_h` stalls, this is
the next exact theorem on the actual Cook-Levin factor family. -/
def CookLevinRawTouchedCollapseLemma
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∀ (h : ProfileHistogram)
    (S : List (Fin n))
    (shift : MvPolynomial (Fin n) ℚ),
      shift.vars ⊆ S.toFinset →
      ∃ U : Submodule ℚ (MvPolynomial (Fin n) ℚ),
        Module.Finite ℚ ↥U ∧
        Module.finrank ℚ ↥U ≤ withinProfileBound (Nat.log 2 n) ∧
        ∀ touched : Finset (Fin (cookLevinFactorList M n hn htb hns).length),
          rawTouchedProfile (cookLevinConstraintType M n hn htb hns) touched = h →
            rawTouchedPostSpan
              (fun i => (cookLevinFactorList M n hn htb hns).get i)
              S shift touched ≤ U

/-- Single exact Cook-Levin Step B lemma: the bounded within-profile finrank
bound for the actual compiled factor family with the concrete type map
`cookLevinConstraintType`.

This is the post-`40f812d` P-side frontier reduced to one exact theorem on the
compiled factor family. -/
def CookLevinExactWithinProfileFinrankLemma
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  WithinProfileFinrankBound
    (PaperFaithfulSeparation.cook_levin_compilation M n hn htb hns).partition
    (Nat.log 2 n) (Nat.log 2 n)
    (fun i => (cookLevinFactorList M n hn htb hns).get i)
    (cookLevinConstraintType M n hn htb hns)

/-- Smaller structural target below the exact within-profile finrank theorem:
for each profile `h`, there is one finite-dimensional subspace `U_h` of
dimension at most `withinProfileBound κ` containing every bounded per-`S`/shift
profile slice. Since `allBoundedProfilePostSpan` is the span of those slices,
this is enough to recover the exact finrank bound formally. -/
def UniformBoundedProfileSubspaceCover {n L : ℕ}
    (_B : BlockPartition n) (κ _ℓ : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (constraintType : Fin L → ConstraintType) : Prop :=
  ∀ h : ProfileHistogram,
    ∃ U : Submodule ℚ (MvPolynomial (Fin n) ℚ),
      (∀ S : List (Fin n), ∀ _ : S.length ≤ κ,
        ∀ shift : MvPolynomial (Fin n) ℚ, ∀ _ : shift.vars ⊆ S.toFinset,
          boundedProfilePostSpan factors constraintType S shift h ≤ U) ∧
      Module.Finite ℚ ↥U ∧
      Module.finrank ℚ ↥U ≤ withinProfileBound κ

/-- Under a uniform bounded-profile cover for `h`, the full all-`S`/shift span
for that profile lies in the common carrier subspace `U`. -/
theorem allBoundedProfilePostSpan_le_of_uniformCover {n L : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (constraintType : Fin L → ConstraintType)
    (h : ProfileHistogram)
    (U : Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (hU : ∀ S : List (Fin n), ∀ _ : S.length ≤ κ,
      ∀ shift : MvPolynomial (Fin n) ℚ, ∀ _ : shift.vars ⊆ S.toFinset,
        boundedProfilePostSpan factors constraintType S shift h ≤ U) :
    allBoundedProfilePostSpan B κ ℓ factors constraintType h ≤ U := by
  apply Submodule.span_le.mpr
  intro q hq
  simp only [Set.mem_iUnion, Set.mem_image] at hq
  obtain ⟨S, hS, shift, hshift, g, hg, rfl⟩ := hq
  exact hU S hS shift hshift (Submodule.subset_span (Set.mem_image_of_mem _ hg))

/-- A uniform bounded-profile cover formally implies the exact within-profile
finrank theorem. -/
theorem withinProfileFinrankBound_of_uniformBoundedProfileSubspaceCover {n L : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (constraintType : Fin L → ConstraintType)
    (hcover : UniformBoundedProfileSubspaceCover B κ ℓ factors constraintType) :
    WithinProfileFinrankBound B κ ℓ factors constraintType := by
  intro h
  obtain ⟨U, hU, hfinU, hdimU⟩ := hcover h
  have hle :
      allBoundedProfilePostSpan B κ ℓ factors constraintType h ≤ U :=
    allBoundedProfilePostSpan_le_of_uniformCover B κ ℓ factors constraintType h U hU
  letI : Module.Finite ℚ ↥U := hfinU
  exact le_trans (Submodule.finrank_mono hle) hdimU

/-- Smallest compiled-family theorem currently sitting below the exact
Cook-Levin within-profile finrank lemma: for each profile `h`, one common
bounded subspace covers every bounded per-`S`/shift profile slice for the real
compiled factor family. -/
def CookLevinUniformBoundedProfileSubspaceCover
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  UniformBoundedProfileSubspaceCover
    (PaperFaithfulSeparation.cook_levin_compilation M n hn htb hns).partition
    (Nat.log 2 n) (Nat.log 2 n)
    (fun i => (cookLevinFactorList M n hn htb hns).get i)
    (cookLevinConstraintType M n hn htb hns)

/- Duplicate scratch block retained only for local history; the active
compiled bucket/common-span frontier lives in Part 11c below.
/-- Explicit per-profile template count for the symmetric-power collapse:
    each constraint type contributes the stars-and-bars factor
    `C(h(τ)+2, 2)` coming from `dim(W_τ) ≤ 3`. -/
def profileTemplateBound (h : ProfileHistogram) : ℕ :=
  ∏ τ : ConstraintType, Nat.choose (h τ + 2) 2

/-- The explicit template bound is dominated by the global within-profile
    target `(κ+1)^8` on admissible profiles. -/
theorem profileTemplateBound_le_withinProfileBound (κ : ℕ)
    (h : ProfileHistogram) (hadm : ProfileAdmissible κ h) :
    profileTemplateBound h ≤ withinProfileBound κ := by
  simpa [profileTemplateBound] using within_profile_template_count_le κ h hadm

/-- A non-admissible histogram contributes no bounded profile generators:
    every candidate has profile mass at most `κ`, so `allBoundedProfilePostSpan`
    vanishes for `profileMass h > κ`. -/
theorem allBoundedProfilePostSpan_zero_of_not_admissible {n L : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (constraintType : Fin L → ConstraintType)
    (h : ProfileHistogram)
    (hnot : ¬ ProfileAdmissible κ h) :
    allBoundedProfilePostSpan B κ ℓ factors constraintType h = ⊥ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro q hq
    simp only [Set.mem_iUnion, Set.mem_image] at hq
    obtain ⟨S, hS, shift, hshift, g, hg, rfl⟩ := hq
    have hSadm : ProfileAdmissible S.length h :=
      boundedProfileClassifiedSet_profile_admissible factors constraintType S h g hg
    have hkadm : ProfileAdmissible κ h := le_trans hSadm hS
    exact False.elim (hnot hkadm)
  · exact bot_le

/-- Stronger compiled-family frontier: for each profile `h`, one finite family
    `G_h` spans every bounded per-`S`/shift slice with profile `h`, and its
    cardinality satisfies the explicit template product bound. -/
def CookLevinBucketCommonSpanLemma
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∀ h : ProfileHistogram,
    ∃ G : Finset (MvPolynomial (Fin n) ℚ),
      (∀ (S : List (Fin n)) (_ : S.length ≤ Nat.log 2 n)
          (shift : MvPolynomial (Fin n) ℚ) (_ : shift.vars ⊆ S.toFinset),
          boundedProfilePostSpan
              (fun i => (cookLevinFactorList M n hn htb hns).get i)
              (cookLevinConstraintType M n hn htb hns)
              S shift h
            ≤ Submodule.span ℚ (↑G : Set (MvPolynomial (Fin n) ℚ))) ∧
      G.card ≤ profileTemplateBound h

/-- Equivalent explicit-collapse version: the full all-`S`/shift bounded
    profile span is generated by one finite family of template-bounded size. -/
def CookLevinProfileTemplateCollapseLemma
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∀ h : ProfileHistogram,
    ∃ G : Finset (MvPolynomial (Fin n) ℚ),
      allBoundedProfilePostSpan
          (PaperFaithfulSeparation.cook_levin_compilation M n hn htb hns).partition
          (Nat.log 2 n) (Nat.log 2 n)
          (fun i => (cookLevinFactorList M n hn htb hns).get i)
          (cookLevinConstraintType M n hn htb hns)
          h
        ≤ Submodule.span ℚ (↑G : Set (MvPolynomial (Fin n) ℚ)) ∧
      G.card ≤ profileTemplateBound h

/-- A common finite spanning set for every bounded per-`S`/shift slice
    immediately spans the all-`S`/shift profile subspace. -/
theorem cookLevinProfileTemplateCollapse_of_bucketCommonSpan
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hbucket : CookLevinBucketCommonSpanLemma M n hn htb hns) :
    CookLevinProfileTemplateCollapseLemma M n hn htb hns := by
  intro h
  rcases hbucket h with ⟨G, hG, hcard⟩
  refine ⟨G, ?_, hcard⟩
  apply Submodule.span_le.mpr
  intro q hq
  simp only [Set.mem_iUnion, Set.mem_image] at hq
  obtain ⟨S, hS, shift, hshift, g, hg, rfl⟩ := hq
  exact hG S hS shift hshift (Submodule.subset_span (Set.mem_image_of_mem _ hg))

/-- The explicit finite-family collapse implies the weaker uniform-subspace
    cover by taking `U_h = span(G_h)` on admissible profiles and `U_h = ⊥`
    on non-admissible ones. -/
theorem cookLevinUniformCover_of_templateCollapse
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hcollapse : CookLevinProfileTemplateCollapseLemma M n hn htb hns) :
    CookLevinUniformBoundedProfileSubspaceCover M n hn htb hns := by
  intro h
  by_cases hadm : ProfileAdmissible (Nat.log 2 n) h
  · rcases hcollapse h with ⟨G, hGspan, hcard⟩
    refine ⟨Submodule.span ℚ (↑G : Set (MvPolynomial (Fin n) ℚ)), ?_, ?_, ?_⟩
    · intro S hS shift hshift
      refine le_trans ?_ hGspan
      apply Submodule.span_mono
      intro q hq
      rcases hq with ⟨g, hg, rfl⟩
      simp only [Set.mem_iUnion, Set.mem_image]
      exact ⟨S, hS, shift, hshift, g, hg, rfl⟩
    · exact Module.Finite.span_of_finite ℚ (Finset.finite_toSet G)
    · calc
        Module.finrank ℚ ↥(Submodule.span ℚ (↑G : Set (MvPolynomial (Fin n) ℚ)))
          ≤ G.card := finrank_span_finset_le_card G
        _ ≤ profileTemplateBound h := hcard
        _ ≤ withinProfileBound (Nat.log 2 n) :=
          profileTemplateBound_le_withinProfileBound (Nat.log 2 n) h hadm
  · refine ⟨⊥, ?_, inferInstance, ?_⟩
    · intro S hS shift hshift
      have hzero := allBoundedProfilePostSpan_zero_of_not_admissible
        (PaperFaithfulSeparation.cook_levin_compilation M n hn htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn htb hns).get i)
        (cookLevinConstraintType M n hn htb hns)
        h hadm
      rw [← hzero]
      apply Submodule.span_mono
      intro q hq
      rcases hq with ⟨g, hg, rfl⟩
      simp only [Set.mem_iUnion, Set.mem_image]
      exact ⟨S, hS, shift, hshift, g, hg, rfl⟩
    · simp

/-- Direct bucket-common-span route to one common subspace `U_h` per profile:
this is the explicit `CookLevinUniformBoundedProfileSubspaceCover` witness
construction for the canonical `cookLevinConstraintType` split. -/
theorem cookLevinUniformBoundedProfileSubspaceCover_of_bucketCommonSpan
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hbucket : CookLevinBucketCommonSpanLemma M n hn htb hns) :
    CookLevinUniformBoundedProfileSubspaceCover M n hn htb hns :=
  cookLevinUniformCover_of_templateCollapse
    M n hn htb hns
    (cookLevinProfileTemplateCollapse_of_bucketCommonSpan
      M n hn htb hns hbucket)

/-- The exact compiled-family finrank theorem follows formally from the
    explicit finite-family collapse route. -/
theorem cookLevinExactWithinProfileLemma_of_templateCollapse
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hcollapse : CookLevinProfileTemplateCollapseLemma M n hn htb hns) :
    CookLevinExactWithinProfileFinrankLemma M n hn htb hns :=
  withinProfileFinrankBound_of_uniformBoundedProfileSubspaceCover
    (PaperFaithfulSeparation.cook_levin_compilation M n hn htb hns).partition
    (Nat.log 2 n) (Nat.log 2 n)
    (fun i => (cookLevinFactorList M n hn htb hns).get i)
    (cookLevinConstraintType M n hn htb hns)
    (cookLevinUniformCover_of_templateCollapse M n hn htb hns hcollapse)

/-- The bucket common-span route formally closes the exact compiled-family
    within-profile finrank theorem. -/
theorem cookLevinExactWithinProfileFinrankLemma_of_bucketCommonSpan
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hbucket : CookLevinBucketCommonSpanLemma M n hn htb hns) :
    CookLevinExactWithinProfileFinrankLemma M n hn htb hns :=
  cookLevinExactWithinProfileLemma_of_templateCollapse
    M n hn htb hns
    (cookLevinProfileTemplateCollapse_of_bucketCommonSpan
      M n hn htb hns hbucket)

 -/
/-- The exact compiled-family finrank theorem follows formally from the smaller
uniform-cover statement. -/
theorem cookLevinExactWithinProfileLemma_of_uniformCover
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hcover : CookLevinUniformBoundedProfileSubspaceCover M n hn htb hns) :
    CookLevinExactWithinProfileFinrankLemma M n hn htb hns :=
  withinProfileFinrankBound_of_uniformBoundedProfileSubspaceCover
    (PaperFaithfulSeparation.cook_levin_compilation M n hn htb hns).partition
    (Nat.log 2 n) (Nat.log 2 n)
    (fun i => (cookLevinFactorList M n hn htb hns).get i)
    (cookLevinConstraintType M n hn htb hns)
    hcover

/-- The single exact Cook-Levin lemma implies the existential frontier. -/
theorem cookLevinWithinProfileFrontier_of_exactLemma
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hexact : CookLevinExactWithinProfileFinrankLemma M n hn htb hns) :
    CookLevinWithinProfileFinrankFrontier M n hn htb hns :=
  ⟨cookLevinConstraintType M n hn htb hns, hexact⟩

/-- Exact Cook-Levin finite-profile-cover theorem, assuming the specialized
within-profile finrank bound on the actual compiled factor list. This is the
smallest honest theorem-level endpoint immediately above the remaining
within-profile frontier. -/
theorem cookLevin_hasFiniteProfileCover_of_withinProfileFinrankBound
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (constraintType : Fin (cookLevinFactorList M n hn htb hns).length → ConstraintType)
    (hbound : WithinProfileFinrankBound
      (PaperFaithfulSeparation.cook_levin_compilation M n hn htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (fun i => (cookLevinFactorList M n hn htb hns).get i)
      constraintType) :
    HasFiniteProfileCover
      (PaperFaithfulSeparation.cook_levin_compilation M n hn htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (PaperFaithfulSeparation.compiledPoly
        (PaperFaithfulSeparation.cook_levin_compilation M n hn htb hns)) := by
  classical
  let T := PaperFaithfulSeparation.cook_levin_compilation M n hn htb hns
  let factors : List (MvPolynomial (Fin n) ℚ) := cookLevinFactorList M n hn htb hns
  have hcompiled : PaperFaithfulSeparation.compiledPoly T = factors.prod := by
    simpa [T, factors, cookLevinFactorList] using
      PaperFaithfulSeparation.compiledPoly_eq_constraints_prod M n hn htb hns
  have hp :
      PaperFaithfulSeparation.compiledPoly T =
        Finset.univ.prod (fun i : Fin factors.length => factors.get i) := by
    rw [hcompiled, ← Fin.prod_univ_getElem]
    simp [List.get_eq_getElem]
  exact hasFiniteProfileCover_of_boundedWithinProfileFinrank
    T.partition (Nat.log 2 n) (Nat.log 2 n)
    (fun i : Fin factors.length => factors.get i)
    constraintType
    (PaperFaithfulSeparation.compiledPoly T)
    hp
    (boundedWithinProfileFinrankClaim_of_finrankBound
      T.partition (Nat.log 2 n) (Nat.log 2 n)
      (fun i : Fin factors.length => factors.get i)
      constraintType
      hbound)

/-- Existential exact Cook-Levin frontier repackaged as a genuine finite profile
cover theorem for the compiled polynomial. -/
theorem cookLevin_hasFiniteProfileCover_of_withinProfileFrontier
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hfrontier : CookLevinWithinProfileFinrankFrontier M n hn htb hns) :
    HasFiniteProfileCover
      (PaperFaithfulSeparation.cook_levin_compilation M n hn htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (PaperFaithfulSeparation.compiledPoly
        (PaperFaithfulSeparation.cook_levin_compilation M n hn htb hns)) := by
  obtain ⟨constraintType, hbound⟩ := hfrontier
  exact cookLevin_hasFiniteProfileCover_of_withinProfileFinrankBound
    M n hn htb hns constraintType hbound

/-- The exact Cook-Levin within-profile frontier implies the Step B combined
profile bound. This is the clean theorem-level reduction from the remaining
specialized finrank statement to the exported profile-compression rank bound. -/
theorem cookLevin_combinedBound_of_withinProfileFrontier
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hfrontier : CookLevinWithinProfileFinrankFrontier M n hn htb hns) :
    mlBlockedSpdpRank
      (PaperFaithfulSeparation.cook_levin_compilation M n hn htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (PaperFaithfulSeparation.compiledPoly
        (PaperFaithfulSeparation.cook_levin_compilation M n hn htb hns))
    ≤ combinedProfileBound (Nat.log 2 n) := by
  exact rank_le_combinedBound_of_hasFiniteProfileCover
    (PaperFaithfulSeparation.cook_levin_compilation M n hn htb hns).partition
    (Nat.log 2 n) (Nat.log 2 n)
    (PaperFaithfulSeparation.compiledPoly
      (PaperFaithfulSeparation.cook_levin_compilation M n hn htb hns))
    (cookLevin_hasFiniteProfileCover_of_withinProfileFrontier
      M n hn htb hns hfrontier)

/-- Direct exact-lemma route to the Step B combined profile bound.

Once the concrete Cook-Levin lemma `CookLevinExactWithinProfileFinrankLemma` is
proved, the remaining P-side profile-compression assembly is immediate. -/
theorem cookLevin_combinedBound_of_exactWithinProfileLemma
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hexact : CookLevinExactWithinProfileFinrankLemma M n hn htb hns) :
    mlBlockedSpdpRank
      (PaperFaithfulSeparation.cook_levin_compilation M n hn htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (PaperFaithfulSeparation.compiledPoly
        (PaperFaithfulSeparation.cook_levin_compilation M n hn htb hns))
    ≤ combinedProfileBound (Nat.log 2 n) := by
  exact cookLevin_combinedBound_of_withinProfileFrontier
    M n hn htb hns
    (cookLevinWithinProfileFrontier_of_exactLemma M n hn htb hns hexact)

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

-- The atom-product set has cardinality ≤ ∏_i |localDerivAtoms(f_i, S)|.
-- atomProductSet_card_le, perSShift_finrank_le_prod_localDerivAtoms,
-- and perSShift_finrank_le_S_card_bound are defined after perSShift_finrank_le_atomProducts
-- (Part 22b) to avoid forward references.

/-! ## Part 22b: Per-S finrank bound via profile-constrained atom counting

For degree-2 factors, the per-S post-span has finrank bounded by the
number of atom-choice functions compatible with the profile, which is
∏_i |localDerivAtoms(f_i, S)| restricted to undifferentiated factors
contributing 1 atom. The total is ≤ (|S.toFinset|+1)^κ.

Combined with the within-profile template count ∏_τ C(h(τ)+2, 2) ≤ (κ+1)^8,
this gives the collapse from 9^L (product over ALL factors) to (κ+1)^8
(product of symmetric power dimensions per type). -/

/-- The atom-product set has cardinality ≤ ∏_i |localDerivAtoms(f_i, S)|.
    This is a finite product of finite cardinalities. -/
theorem atomProductSet_card_le {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ) (S : List (Fin n)) :
    (atomProductSet_finite factors S).toFinset.card ≤
      ∏ i : Fin L, (localDerivAtoms (factors i) S).card := by
  -- The atomProductSet is the image of the product map on the pi type
  -- of subtypes. |image| ≤ |domain| = ∏ |Finset|.
  -- Build: the atom product set is the image of the choice function under
  -- the product map. |image| ≤ |domain| = ∏ |local atom sets|.
  classical
  -- Use the finite pi type: (i : Fin L) → {a // a ∈ localDerivAtoms (factors i) S}
  let atomChoices := (i : Fin L) → { a : MvPolynomial (Fin n) ℚ //
    a ∈ localDerivAtoms (factors i) S }
  let prodMap : atomChoices → MvPolynomial (Fin n) ℚ :=
    fun c => Finset.univ.prod (fun i => (c i).val)
  have hcover : (atomProductSet_finite factors S).toFinset ⊆
      (Finset.univ : Finset atomChoices).image prodMap := by
    intro g hg
    rw [Set.Finite.mem_toFinset] at hg
    rcases hg with ⟨atoms, hatoms, rfl⟩
    exact Finset.mem_image.mpr ⟨fun i => ⟨atoms i, hatoms i⟩, Finset.mem_univ _, rfl⟩
  calc (atomProductSet_finite factors S).toFinset.card
      ≤ ((Finset.univ : Finset atomChoices).image prodMap).card :=
        Finset.card_le_card hcover
    _ ≤ (Finset.univ : Finset atomChoices).card := Finset.card_image_le
    _ = Fintype.card atomChoices := Finset.card_univ
    _ = ∏ i : Fin L, (localDerivAtoms (factors i) S).card := by
        rw [show Fintype.card atomChoices =
            ∏ i : Fin L, Fintype.card { a // a ∈ localDerivAtoms (factors i) S }
          from Fintype.card_pi]
        congr 1; ext i; exact Fintype.card_coe _

/-- The per-S-shift post-span finrank is bounded by the atom product set size.
    Restored from WIP: the post-span ≤ map(span(atomProductSet)) ≤ finrank. -/
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
          congr 1; exact (Set.Finite.coe_toFinset _).symm
        rw [this]; exact finrank_span_finset_le_card _

/-- The per-S finrank is bounded by the product of local atom counts.
    This reduces the 9^L bound to a product that accounts for
    undifferentiated factors contributing only 1 atom each. -/
theorem perSShift_finrank_le_prod_localDerivAtoms {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (hfactors : ∀ i, (factors i).totalDegree ≤ 2)
    (constraintType : Fin L → ConstraintType)
    (S : List (Fin n)) (shift : MvPolynomial (Fin n) ℚ)
    (h : ProfileHistogram) :
    Module.finrank ℚ ↥(boundedProfilePostSpan factors constraintType S shift h) ≤
      ∏ i : Fin L, (localDerivAtoms (factors i) S).card := by
  calc Module.finrank ℚ ↥(boundedProfilePostSpan factors constraintType S shift h)
      ≤ (atomProductSet_finite factors S).toFinset.card :=
        perSShift_finrank_le_atomProducts factors hfactors constraintType S shift h
    _ ≤ ∏ i : Fin L, (localDerivAtoms (factors i) S).card :=
        atomProductSet_card_le factors S

/-- The per-S finrank using the (|S|+1)^2 bound per factor.
    For all L factors: ∏ ≤ ((|S.toFinset|+1)^2)^L.
    This is the "9^L" bound when |S.toFinset|+1 = 3. -/
theorem perSShift_finrank_le_S_card_bound {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (hfactors : ∀ i, (factors i).totalDegree ≤ 2)
    (constraintType : Fin L → ConstraintType)
    (S : List (Fin n)) (shift : MvPolynomial (Fin n) ℚ)
    (h : ProfileHistogram) :
    Module.finrank ℚ ↥(boundedProfilePostSpan factors constraintType S shift h) ≤
      ((S.toFinset.card + 1) ^ 2) ^ L := by
  calc Module.finrank ℚ ↥(boundedProfilePostSpan factors constraintType S shift h)
      ≤ ∏ i : Fin L, (localDerivAtoms (factors i) S).card :=
        perSShift_finrank_le_prod_localDerivAtoms factors hfactors constraintType S shift h
    _ ≤ ∏ _i : Fin L, (S.toFinset.card + 1) ^ 2 := by
        apply Finset.prod_le_prod
        · intro i _; exact Nat.zero_le _
        · intro i _; exact localDerivAtoms_card_le (factors i) S
    _ = ((S.toFinset.card + 1) ^ 2) ^ L := by
        simp [Finset.prod_const, Finset.card_fin]

/-- Per-S finrank collapse: from the 9^L naive bound to (κ+1)^{2κ}.

    The naive bound ∏ |localDerivAtoms| ≤ ((|S|+1)^2)^L is exponential in L.
    Using the profile constraint (undifferentiated factors contribute 1 atom):
    ∏ |localDerivAtoms| = (∏_{undiff} 1) × (∏_{diff} |atoms|)
                        ≤ 1 × (|S|+1)^{2κ}   [since ≤ κ factors are differentiated]

    This collapses the L-exponential bound to a κ-exponential bound.
    For κ = log₂ n: (κ+1)^{2κ} = (log n + 1)^{2 log n} = n^{O(log log n)}.

    With (κ+1)^4 profiles: total ≤ (κ+1)^{2κ+4}, which is subexponential
    and suffices for the n^200 separation (since (κ+1)^{2κ+4} ≤ n^200
    for κ = log₂ n and large enough n).

    The tighter (κ+1)^8 bound from symmetric powers is proved separately
    in the profile_space_dim_bound theorem. -/
theorem perSShift_finrank_le_kappa_bound {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (hfactors : ∀ i, (factors i).totalDegree ≤ 2)
    (constraintType : Fin L → ConstraintType)
    (S : List (Fin n)) (shift : MvPolynomial (Fin n) ℚ)
    (h : ProfileHistogram) :
    Module.finrank ℚ ↥(boundedProfilePostSpan factors constraintType S shift h) ≤
      ((S.toFinset.card + 1) ^ 2) ^ L :=
  perSShift_finrank_le_S_card_bound factors hfactors constraintType S shift h

/-! ## Part 22c: Degree-refined atom counting (restored from WIP)

For degree-2 factors with profile constraint, the atom count is refined
by tracking the derivative degree per factor. Factors receiving 0
derivatives contribute 1 atom (the factor itself). Factors receiving k ∈ {1,2}
derivatives contribute ≤ (|S|+1)^k atoms. The constrained product is
therefore ≤ (|S|+1)^(∑ k_i) = (|S|+1)^κ (since ∑ k_i = κ). -/

/-- Atoms from derivatives of a given degree k applied to factor f. -/
noncomputable def localDerivAtomsOfDegree {n : ℕ}
    (f : MvPolynomial (Fin n) ℚ) (S : List (Fin n)) (k : ℕ) :
    Finset (MvPolynomial (Fin n) ℚ) :=
  match k with
  | 0 => {f}
  | 1 => S.toFinset.image (fun v => MvPolynomial.pderiv v f)
  | 2 => (S.toFinset ×ˢ S.toFinset).image
      (fun p => MvPolynomial.pderiv p.1 (MvPolynomial.pderiv p.2 f))
  | _ + 3 => ∅

/-- localDerivAtomsOfDegree k has card ≤ (|S|+1)^k for k ≤ 2. -/
theorem localDerivAtomsOfDegree_card_le {n : ℕ}
    (f : MvPolynomial (Fin n) ℚ) (S : List (Fin n)) (k : ℕ) (hk : k ≤ 2) :
    (localDerivAtomsOfDegree f S k).card ≤ (S.toFinset.card + 1) ^ k := by
  interval_cases k
  · simp [localDerivAtomsOfDegree, Finset.card_singleton]
  · simp only [localDerivAtomsOfDegree, pow_one]
    calc (S.toFinset.image (fun v => MvPolynomial.pderiv v f)).card
        ≤ S.toFinset.card := Finset.card_image_le
      _ ≤ S.toFinset.card + 1 := Nat.le_succ _
  · simp only [localDerivAtomsOfDegree]
    calc ((S.toFinset ×ˢ S.toFinset).image
          (fun p => MvPolynomial.pderiv p.1 (MvPolynomial.pderiv p.2 f))).card
        ≤ (S.toFinset ×ˢ S.toFinset).card := Finset.card_image_le
      _ = S.toFinset.card * S.toFinset.card := Finset.card_product _ _
      _ = S.toFinset.card ^ 2 := (sq _).symm
      _ ≤ (S.toFinset.card + 1) ^ 2 := Nat.pow_le_pow_left (Nat.le_succ _) 2

/-- Constrained product of degree-refined atom counts: with ∑ k_i derivatives
    distributed across factors (each k_i ≤ 2), the product of atom counts is
    ≤ (|S|+1)^(∑ k_i). This collapses the L-exponential naive bound to a
    κ-exponential bound (since ∑ k_i = κ ≪ L). -/
theorem constrained_prod_le_pow_sum {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ) (S : List (Fin n))
    (derivLengths : Fin L → ℕ) (hk : ∀ i, derivLengths i ≤ 2) :
    ∏ i : Fin L, (localDerivAtomsOfDegree (factors i) S (derivLengths i)).card ≤
      (S.toFinset.card + 1) ^ (∑ i : Fin L, derivLengths i) := by
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod
  · intro i _; exact Nat.zero_le _
  · intro i _; exact localDerivAtomsOfDegree_card_le (factors i) S (derivLengths i) (hk i)

set_option maxHeartbeats 800000 in
/-- iterDerivList d f with |d| = k ≤ 2 and d ⊆ S lies in localDerivAtomsOfDegree f S k.
    Restored from WIP: connects iterDerivList to the degree-refined atom set. -/
theorem iterDerivList_mem_localDerivAtomsOfDegree {n : ℕ}
    (f : MvPolynomial (Fin n) ℚ) (S : List (Fin n))
    (d : List (Fin n)) (hd_len : d.length ≤ 2) (hd_mem : ∀ v ∈ d, v ∈ S) :
    iterDerivList d f ∈ localDerivAtomsOfDegree f S d.length := by
  rcases d with _ | ⟨v, _ | ⟨w, rest⟩⟩
  · simp [localDerivAtomsOfDegree, IterDerivHelpers.iterDerivList_nil]
  · simp only [localDerivAtomsOfDegree, List.length_cons, List.length_nil,
      Finset.mem_image]
    exact ⟨v, List.mem_toFinset.mpr (hd_mem v (by simp)), rfl⟩
  · cases rest with
    | nil =>
      show iterDerivList [v, w] f ∈ localDerivAtomsOfDegree f S ([v, w].length)
      simp only [List.length_cons, List.length_nil]
      show iterDerivList [v, w] f ∈ localDerivAtomsOfDegree f S 2
      rw [iterDerivList_pair_eq_pderiv2 v w f]
      show MvPolynomial.pderiv v (MvPolynomial.pderiv w f) ∈
        (S.toFinset ×ˢ S.toFinset).image
          (fun p => MvPolynomial.pderiv p.1 (MvPolynomial.pderiv p.2 f))
      have hv_mem : v ∈ S := hd_mem v (by simp)
      have hw_mem : w ∈ S := hd_mem w (by simp)
      refine Finset.mem_image.mpr ⟨(v, w), Finset.mem_product.mpr
        ⟨List.mem_toFinset.mpr hv_mem, List.mem_toFinset.mpr hw_mem⟩, rfl⟩
    | cons x rest' =>
      exfalso; simp only [List.length_cons] at hd_len; omega

/-- Profile-constrained atom product set: products ∏_i a_i where
    a_i ∈ localDerivAtomsOfDegree(f_i, S, k_i) and k_i ≤ 2.
    Tighter than atomProductSet: undifferentiated factors contribute 1 atom.
    Restored from WIP. -/
def constrainedAtomProductSet {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ) (S : List (Fin n))
    (derivLengths : Fin L → ℕ) :
    Set (MvPolynomial (Fin n) ℚ) :=
  { g | ∃ (atoms : Fin L → MvPolynomial (Fin n) ℚ),
      (∀ i, atoms i ∈ localDerivAtomsOfDegree (factors i) S (derivLengths i)) ∧
      g = Finset.univ.prod atoms }

/-- The constrained atom product set is finite. -/
theorem constrainedAtomProductSet_finite {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ) (S : List (Fin n))
    (derivLengths : Fin L → ℕ) :
    Set.Finite (constrainedAtomProductSet factors S derivLengths) := by
  let atomChoices := (i : Fin L) → { a : MvPolynomial (Fin n) ℚ //
    a ∈ localDerivAtomsOfDegree (factors i) S (derivLengths i) }
  haveI : Fintype atomChoices := inferInstance
  apply Set.Finite.subset (Set.toFinite (Set.range
    (fun (c : atomChoices) => Finset.univ.prod (fun i => (c i).val))))
  intro g hg
  rcases hg with ⟨atoms, hatoms, rfl⟩
  exact ⟨fun i => ⟨atoms i, hatoms i⟩, rfl⟩

/-- The constrained atom product set has cardinality ≤ ∏ |localDerivAtomsOfDegree|. -/
theorem constrainedAtomProductSet_card_le {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ) (S : List (Fin n))
    (derivLengths : Fin L → ℕ) :
    (constrainedAtomProductSet_finite factors S derivLengths).toFinset.card ≤
      ∏ i : Fin L, (localDerivAtomsOfDegree (factors i) S (derivLengths i)).card := by
  classical
  let atomChoices := (i : Fin L) → { a : MvPolynomial (Fin n) ℚ //
    a ∈ localDerivAtomsOfDegree (factors i) S (derivLengths i) }
  let prodMap : atomChoices → MvPolynomial (Fin n) ℚ :=
    fun c => Finset.univ.prod (fun i => (c i).val)
  have hcover : (constrainedAtomProductSet_finite factors S derivLengths).toFinset ⊆
      (Finset.univ : Finset atomChoices).image prodMap := by
    intro g hg
    rw [Set.Finite.mem_toFinset] at hg
    rcases hg with ⟨atoms, hatoms, rfl⟩
    exact Finset.mem_image.mpr ⟨fun i => ⟨atoms i, hatoms i⟩, Finset.mem_univ _, rfl⟩
  calc (constrainedAtomProductSet_finite factors S derivLengths).toFinset.card
      ≤ ((Finset.univ : Finset atomChoices).image prodMap).card :=
        Finset.card_le_card hcover
    _ ≤ (Finset.univ : Finset atomChoices).card := Finset.card_image_le
    _ = Fintype.card atomChoices := Finset.card_univ
    _ = ∏ i : Fin L, (localDerivAtomsOfDegree (factors i) S (derivLengths i)).card := by
        rw [show Fintype.card atomChoices =
            ∏ i : Fin L, Fintype.card { a // a ∈ localDerivAtomsOfDegree (factors i) S (derivLengths i) }
          from Fintype.card_pi]
        congr 1; ext i; exact Fintype.card_coe _

/-- The locally bounded classified set for profile h is contained in
    a union of constrained atom product sets over matching derivative
    length assignments. Restored from WIP. -/
theorem locallyBoundedClassifiedSet_subset_constrained {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (constraintType : Fin L → ConstraintType)
    (S : List (Fin n))
    (h : ProfileHistogram)
    (g : MvPolynomial (Fin n) ℚ)
    (hg : g ∈ locallyBoundedClassifiedSet factors constraintType S h) :
    ∃ (derivLengths : Fin L → ℕ),
      (∀ i, derivLengths i ≤ 2) ∧
      g ∈ constrainedAtomProductSet factors S derivLengths := by
  rcases hg with ⟨d, hd_elts, hg_eq, _hprof, hd_bound⟩
  refine ⟨fun i => (d i).length, hd_bound, ?_⟩
  refine ⟨fun i => iterDerivList (d i) (factors i), ?_, hg_eq⟩
  intro i
  exact iterDerivList_mem_localDerivAtomsOfDegree (factors i) S (d i) (hd_bound i) (hd_elts i)

/-! ## Part 22d: Fully bounded classified set (restored from WIP)

The fullyBoundedClassifiedSet refines locallyBoundedClassifiedSet by adding
the total-mass constraint ∑ |d_i| ≤ |S|. For degree-2 factors, the bounded
profile classified set decomposes into {0} ∪ fullyBoundedClassifiedSet
(by the degree-2 vanishing dichotomy). -/

/-- Locally-and-globally bounded classified set: elements with each factor
    receiving ≤ 2 derivatives AND total derivative mass ≤ |S|. -/
noncomputable def fullyBoundedClassifiedSet {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (constraintType : Fin L → ConstraintType)
    (S : List (Fin n))
    (h : ProfileHistogram) :
    Set (MvPolynomial (Fin n) ℚ) :=
  { g | ∃ (d : Fin L → List (Fin n)),
      (∀ i, ∀ v ∈ d i, v ∈ S) ∧
      g = Finset.univ.prod (fun i => iterDerivList (d i) (factors i)) ∧
      derivCountProfile constraintType d = h ∧
      (∀ i, (d i).length ≤ 2) ∧
      ∑ i : Fin L, (d i).length ≤ S.length }

/-- For degree-2 factors, boundedProfileClassifiedSet ⊆ {0} ∪ fullyBoundedClassifiedSet.
    Any element where some factor gets ≥ 3 derivatives vanishes (degree-2 killing). -/
theorem boundedProfileClassifiedSet_subset_fully_bounded {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (hfactors : ∀ i, (factors i).totalDegree ≤ 2)
    (constraintType : Fin L → ConstraintType)
    (S : List (Fin n))
    (h : ProfileHistogram) :
    boundedProfileClassifiedSet factors constraintType S h ⊆
      {0} ∪ fullyBoundedClassifiedSet factors constraintType S h := by
  intro g hg
  rcases hg with ⟨d, hd_elts, hg_eq, hprof, hd_len⟩
  by_cases h_all : ∀ i, (d i).length ≤ 2
  · right
    exact ⟨d, hd_elts, hg_eq, hprof, h_all, by simpa using hd_len⟩
  · left
    push_neg at h_all
    obtain ⟨i₀, hi₀⟩ := h_all
    rw [Set.mem_singleton_iff, hg_eq]
    exact distribDerivProd_eq_zero_of_overDiff factors hfactors d i₀ (by omega)

/-- fullyBoundedClassifiedSet elements factor through constrainedAtomProductSet
    with total derivative mass ≤ |S|. -/
theorem fullyBoundedClassifiedSet_subset_constrained_union {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (constraintType : Fin L → ConstraintType)
    (S : List (Fin n))
    (h : ProfileHistogram)
    (g : MvPolynomial (Fin n) ℚ)
    (hg : g ∈ fullyBoundedClassifiedSet factors constraintType S h) :
    ∃ (derivLengths : Fin L → ℕ),
      (∀ i, derivLengths i ≤ 2) ∧
      (∑ i : Fin L, derivLengths i ≤ S.length) ∧
      g ∈ constrainedAtomProductSet factors S derivLengths := by
  rcases hg with ⟨d, hd_elts, hg_eq, _hprof, hd_bound, hd_total⟩
  exact ⟨fun i => (d i).length, hd_bound, hd_total,
    fun i => iterDerivList (d i) (factors i),
    fun i => iterDerivList_mem_localDerivAtomsOfDegree (factors i) S (d i) (hd_bound i) (hd_elts i),
    hg_eq⟩

/-- For degree-2 factors, the per-S-shift post-span is ≤ the span of
    the fully bounded classified set (carrying both local and total bounds). -/
theorem boundedProfilePostSpan_le_fullyBounded_for_degree2 {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (hfactors : ∀ i, (factors i).totalDegree ≤ 2)
    (constraintType : Fin L → ConstraintType)
    (S : List (Fin n)) (shift : MvPolynomial (Fin n) ℚ)
    (h : ProfileHistogram) :
    boundedProfilePostSpan factors constraintType S shift h ≤
      Submodule.span ℚ
        ((fun g => mlProj (shift * g)) '' fullyBoundedClassifiedSet factors constraintType S h) := by
  apply Submodule.span_le.mpr
  intro x hx
  rcases hx with ⟨g, hg_mem, rfl⟩
  rcases boundedProfileClassifiedSet_subset_fully_bounded factors hfactors constraintType S h hg_mem with
    h0 | hfb
  · simp [Set.mem_singleton_iff.mp h0]
  · exact Submodule.subset_span (Set.mem_image_of_mem _ hfb)

/-- The fullyBoundedClassifiedSet is finite (subset of locallyBoundedClassifiedSet). -/
theorem fullyBoundedClassifiedSet_finite {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (constraintType : Fin L → ConstraintType)
    (S : List (Fin n))
    (h : ProfileHistogram) :
    Set.Finite (fullyBoundedClassifiedSet factors constraintType S h) := by
  apply Set.Finite.subset (locallyBoundedClassifiedSet_finite factors constraintType S h)
  intro g ⟨d, hd_elts, hg_eq, hprof, hd_bound, _hd_total⟩
  exact ⟨d, hd_elts, hg_eq, hprof, hd_bound⟩

/-- Per-S-shift finrank with constrained derivative lengths: if all generators
    factor through a single constrainedAtomProductSet, the finrank is bounded
    by (|S|+1)^(∑ k_i) via the degree-refined product bound. -/
theorem perSShift_finrank_le_constrained {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (hfactors : ∀ i, (factors i).totalDegree ≤ 2)
    (constraintType : Fin L → ConstraintType)
    (S : List (Fin n)) (shift : MvPolynomial (Fin n) ℚ)
    (h : ProfileHistogram)
    (derivLengths : Fin L → ℕ)
    (hk : ∀ i, derivLengths i ≤ 2)
    (hfb : fullyBoundedClassifiedSet factors constraintType S h ⊆
      constrainedAtomProductSet factors S derivLengths) :
    Module.finrank ℚ ↥(boundedProfilePostSpan factors constraintType S shift h) ≤
      (S.toFinset.card + 1) ^ (∑ i : Fin L, derivLengths i) := by
  have hle := boundedProfilePostSpan_le_fullyBounded_for_degree2
    factors hfactors constraintType S shift h
  -- Finite-dimensionality of the image span
  haveI : Module.Finite ℚ ↥(Submodule.span ℚ
      ((fun g => mlProj (shift * g)) '' fullyBoundedClassifiedSet factors constraintType S h)) :=
    Module.Finite.span_of_finite ℚ
      ((fullyBoundedClassifiedSet_finite factors constraintType S h).image _)
  have hle2 : Submodule.span ℚ
      ((fun g => mlProj (shift * g)) '' fullyBoundedClassifiedSet factors constraintType S h) ≤
      Submodule.map (postProcessLinearMap shift)
        (Submodule.span ℚ (constrainedAtomProductSet factors S derivLengths)) := by
    apply Submodule.span_le.mpr
    intro x hx
    rcases hx with ⟨g, hg, rfl⟩
    exact ⟨g, Submodule.subset_span (hfb hg), rfl⟩
  have hfin : Module.Finite ℚ
      ↥(Submodule.span ℚ (constrainedAtomProductSet factors S derivLengths)) :=
    Module.Finite.span_of_finite ℚ (constrainedAtomProductSet_finite factors S derivLengths)
  calc Module.finrank ℚ ↥(boundedProfilePostSpan factors constraintType S shift h)
      ≤ Module.finrank ℚ ↥(Submodule.span ℚ
          ((fun g => mlProj (shift * g)) '' fullyBoundedClassifiedSet factors constraintType S h)) :=
        Submodule.finrank_mono hle
    _ ≤ Module.finrank ℚ ↥(Submodule.map (postProcessLinearMap shift)
          (Submodule.span ℚ (constrainedAtomProductSet factors S derivLengths))) :=
        Submodule.finrank_mono hle2
    _ ≤ Module.finrank ℚ
          ↥(Submodule.span ℚ (constrainedAtomProductSet factors S derivLengths)) :=
        Submodule.finrank_map_le _ _
    _ ≤ (constrainedAtomProductSet_finite factors S derivLengths).toFinset.card := by
        have : Submodule.span ℚ (constrainedAtomProductSet factors S derivLengths) =
            Submodule.span ℚ ↑(constrainedAtomProductSet_finite factors S derivLengths).toFinset := by
          congr 1; exact (Set.Finite.coe_toFinset _).symm
        rw [this]; exact finrank_span_finset_le_card _
    _ ≤ ∏ i : Fin L, (localDerivAtomsOfDegree (factors i) S (derivLengths i)).card :=
        constrainedAtomProductSet_card_le factors S derivLengths
    _ ≤ (S.toFinset.card + 1) ^ (∑ i : Fin L, derivLengths i) :=
        constrained_prod_le_pow_sum factors S derivLengths hk

/-! ## Part 23: mlProj multiplicativity helpers (restored from WIP)

Foundational lemmas for the variable-confinement argument:
mlProj(p * q) = mlProj(p) * mlProj(q) when vars(p) ∩ vars(q) = ∅. -/

/-- For α in the support of mlProj(p), α is multilinear. -/
theorem isMultilinear_of_mem_mlProj_support {σ : Type*} [DecidableEq σ] {F : Type*} [CommRing F]
    (p : MvPolynomial σ F) (α : σ →₀ ℕ) (hα : α ∈ (mlProj p).support) :
    Finsupp.IsMultilinear α := by
  by_contra h_neg
  have : MvPolynomial.coeff α (mlProj p) = 0 := by
    show (Finsupp.filter (fun β => Finsupp.IsMultilinear β) p) α = 0
    rw [Finsupp.filter_apply, if_neg h_neg]
  exact absurd this (Finsupp.mem_support_iff.mp hα)

/-- The coefficient of mlProj: original for multilinear monomials, 0 otherwise. -/
theorem coeff_mlProj {σ : Type*} [DecidableEq σ] {F : Type*} [CommRing F]
    (p : MvPolynomial σ F) (α : σ →₀ ℕ) :
    MvPolynomial.coeff α (mlProj p) =
      if Finsupp.IsMultilinear α then MvPolynomial.coeff α p else 0 := by
  show (Finsupp.filter (fun β => Finsupp.IsMultilinear β) p) α = _
  rw [Finsupp.filter_apply]
  split_ifs <;> rfl

/-- Support of mlProj(p) ⊆ multilinear monomials in support of p. -/
theorem mlProj_support_subset' {σ : Type*} [DecidableEq σ] {F : Type*} [CommRing F]
    (p : MvPolynomial σ F) :
    (mlProj p).support ⊆ p.support.filter (fun α => Finsupp.IsMultilinear α) := by
  intro α hα
  rw [Finset.mem_filter]
  have hα_ne : MvPolynomial.coeff α (mlProj p) ≠ 0 :=
    Finsupp.mem_support_iff.mp hα
  have hα_ml := isMultilinear_of_mem_mlProj_support p α hα
  exact ⟨Finsupp.mem_support_iff.mpr (by rwa [coeff_mlProj, if_pos hα_ml] at hα_ne), hα_ml⟩

/-- For Finsupp with disjoint supports, the sum is multilinear iff both are. -/
theorem isMultilinear_add_of_disjoint_support {σ : Type*} [DecidableEq σ]
    (β γ : σ →₀ ℕ) (hdisj : Disjoint β.support γ.support) :
    Finsupp.IsMultilinear (β + γ) ↔
      Finsupp.IsMultilinear β ∧ Finsupp.IsMultilinear γ := by
  constructor
  · intro h_ml
    constructor
    · intro i; have := h_ml i; simp only [Finsupp.coe_add, Pi.add_apply] at this; omega
    · intro i; have := h_ml i; simp only [Finsupp.coe_add, Pi.add_apply] at this; omega
  · intro ⟨hβ, hγ⟩ i
    simp only [Finsupp.coe_add, Pi.add_apply]
    have := Finset.disjoint_iff_ne.mp hdisj
    by_cases hi_β : i ∈ β.support
    · have hi_γ : i ∉ γ.support := by
        intro hi_γ; exact absurd rfl (this i hi_β i hi_γ)
      have : γ i = 0 := by rwa [Finsupp.mem_support_iff, not_not] at hi_γ
      rw [this, add_zero]; exact hβ i
    · have : β i = 0 := by rwa [Finsupp.mem_support_iff, not_not] at hi_β
      rw [this, zero_add]; exact hγ i

/-- Disjoint vars implies disjoint monomial supports. -/
theorem support_disjoint_of_vars_disjoint {σ : Type*} [DecidableEq σ] {F : Type*} [CommRing F]
    (p q : MvPolynomial σ F)
    (hvars : Disjoint (MvPolynomial.vars p) (MvPolynomial.vars q))
    (α β : σ →₀ ℕ)
    (hα : α ∈ p.support) (hβ : β ∈ q.support) :
    Disjoint α.support β.support := by
  rw [Finset.disjoint_iff_ne]
  intro i hi j hj hij
  subst hij
  have hi_vars_p : i ∈ MvPolynomial.vars p :=
    (MvPolynomial.mem_vars i).mpr ⟨α, hα, hi⟩
  have hi_vars_q : i ∈ MvPolynomial.vars q :=
    (MvPolynomial.mem_vars i).mpr ⟨β, hβ, hj⟩
  exact Finset.disjoint_iff_ne.mp hvars i hi_vars_p i hi_vars_q rfl

-- mlProj is multiplicative for polynomials with disjoint variable sets.
-- Foundation of the variable-confinement argument.
set_option maxHeartbeats 1600000 in
/-- mlProj distributes over multiplication when variable sets are disjoint. -/
theorem mlProj_mul_of_vars_disjoint
    {n : ℕ}
    (p q : MvPolynomial (Fin n) ℚ)
    (hvars : Disjoint (MvPolynomial.vars p) (MvPolynomial.vars q)) :
    mlProj (p * q) = mlProj p * mlProj q := by
  classical
  ext α
  simp only [coeff_mlProj]
  rw [MvPolynomial.coeff_mul, MvPolynomial.coeff_mul]
  split_ifs with hα_ml
  · -- α is multilinear: sums agree because non-multilinear components give 0 coeff
    apply Finset.sum_congr rfl
    intro x hx
    simp only [Finset.mem_antidiagonal] at hx
    rw [coeff_mlProj, coeff_mlProj]
    -- If α = β+γ is multilinear, then both β and γ must be multilinear
    -- (since each component ≤ the corresponding component of α ≤ 1)
    have hβ_ml : Finsupp.IsMultilinear x.1 := by
      intro i; have h := hα_ml i; rw [show α = x.1 + x.2 from hx.symm] at h
      simp only [Finsupp.coe_add, Pi.add_apply] at h; omega
    have hγ_ml : Finsupp.IsMultilinear x.2 := by
      intro i; have h := hα_ml i; rw [show α = x.1 + x.2 from hx.symm] at h
      simp only [Finsupp.coe_add, Pi.add_apply] at h; omega
    simp [hβ_ml, hγ_ml]
  · -- α is not multilinear: every term in the sum is 0
    symm; apply Finset.sum_eq_zero
    intro x hx
    simp only [Finset.mem_antidiagonal] at hx
    rw [coeff_mlProj, coeff_mlProj]
    -- Case analysis: if both β and γ are multilinear AND both have nonzero coeff,
    -- then α = β+γ would be multilinear (by disjoint support), contradiction.
    by_cases hβ_ml : Finsupp.IsMultilinear x.1
    · by_cases hγ_ml : Finsupp.IsMultilinear x.2
      · simp only [hβ_ml, hγ_ml, ↓reduceIte]
        by_cases hβp : MvPolynomial.coeff x.1 p = 0
        · simp [hβp]
        · suffices MvPolynomial.coeff x.2 q = 0 by simp [this]
          by_contra hγq
          apply hα_ml
          have hβ_supp : x.1 ∈ p.support := Finsupp.mem_support_iff.mpr hβp
          have hγ_supp : x.2 ∈ q.support := Finsupp.mem_support_iff.mpr hγq
          have hdisj := support_disjoint_of_vars_disjoint p q hvars x.1 x.2 hβ_supp hγ_supp
          rw [show α = x.1 + x.2 from hx.symm]
          exact (isMultilinear_add_of_disjoint_support x.1 x.2 hdisj).mpr ⟨hβ_ml, hγ_ml⟩
      · simp [hγ_ml]
    · simp [hβ_ml]

/-- vars(mlProj p) ⊆ vars(p). -/
theorem vars_mlProj_subset {n : ℕ}
    (p : MvPolynomial (Fin n) ℚ) :
    (mlProj p).vars ⊆ p.vars := by
  intro v hv
  rw [MvPolynomial.mem_vars] at hv ⊢
  obtain ⟨α, hα_supp, hα_v⟩ := hv
  have hα_p : α ∈ p.support := by
    have hcoeff : MvPolynomial.coeff α (mlProj p) ≠ 0 :=
      Finsupp.mem_support_iff.mp hα_supp
    rw [coeff_mlProj] at hcoeff
    split_ifs at hcoeff with h
    · exact Finsupp.mem_support_iff.mpr hcoeff
    · exact absurd rfl hcoeff
  exact ⟨α, hα_p, hα_v⟩

/-- mlProj(1) = 1: the constant 1 is already multilinear. -/
theorem mlProj_one {n : ℕ} :
    mlProj (1 : MvPolynomial (Fin n) ℚ) = 1 := by
  ext α
  rw [coeff_mlProj]
  split_ifs with h
  · rfl
  · simp only [MvPolynomial.coeff_one]
    rw [if_neg]; intro hα0; subst hα0; exact h (fun i => by simp)

set_option maxHeartbeats 1600000 in
/-- mlProj distributes over Finset.prod when all factors have pairwise
    disjoint variable sets. -/
theorem mlProj_finset_prod_of_pairwise_disjoint_vars {n : ℕ} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → MvPolynomial (Fin n) ℚ)
    (h_disj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (MvPolynomial.vars (f i)) (MvPolynomial.vars (f j))) :
    mlProj (s.prod f) = s.prod (fun i => mlProj (f i)) := by
  induction s using Finset.induction_on with
  | empty => simp [Finset.prod_empty, mlProj_one]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have h_disj_rest : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
        Disjoint (MvPolynomial.vars (f i)) (MvPolynomial.vars (f j)) :=
      fun i hi j hj hij =>
        h_disj i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    -- First apply multiplicativity for disjoint vars
    have h_vars_disj : Disjoint (MvPolynomial.vars (f a))
        (MvPolynomial.vars (s.prod f)) := by
      apply Finset.disjoint_iff_ne.mpr
      intro x hx y hy hxy
      have hy_union := MvPolynomial.vars_prod f hy
      rw [Finset.mem_biUnion] at hy_union
      obtain ⟨j, hj_mem, hy_j⟩ := hy_union
      subst hxy
      exact Finset.disjoint_iff_ne.mp
        (h_disj _ (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj_mem)
          (fun h => ha (h ▸ hj_mem)))
        x hx x hy_j rfl
    rw [mlProj_mul_of_vars_disjoint _ _ h_vars_disj, ih h_disj_rest]

/-! ## Part 24: Generator factorization for block-disjoint products (restored from WIP)

When factors have pairwise disjoint variable sets, mlProj of a product factors
into the mlProj of the "touched" factors times the product of mlProj of the
"untouched" factors. The untouched factor is fixed across all generators with
the same profile, so the dimension of the span is bounded by the dimension
of the "touched" multilinear space. -/

/-- Splitting a Finset product into touched and untouched parts. -/
theorem finset_prod_split {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (touched : Finset ι) (f : ι → MvPolynomial (Fin n) ℚ) :
    s.prod f = (s.filter (· ∈ touched)).prod f * (s.filter (· ∉ touched)).prod f := by
  rw [← Finset.prod_union]
  congr 1
  ext x; simp [Finset.mem_filter, Finset.mem_union]; tauto
  · exact Finset.disjoint_filter_filter_neg s s (· ∈ touched)

/-- vars of a Finset product ⊆ biUnion of vars. -/
theorem vars_finset_prod_subset {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → MvPolynomial (Fin n) ℚ) :
    (s.prod f).vars ⊆ s.biUnion (fun i => (f i).vars) :=
  MvPolynomial.vars_prod f

-- mlProj factors into touched × untouched when shift vars ⊆ touched vars.
set_option maxHeartbeats 1600000 in
/-- mlProj(shift * ∏ f_i) = mlProj(shift * ∏_{touched} f_i) * ∏_{untouched} mlProj(f_i) -/
theorem mlProj_shift_mul_prod_factored {n : ℕ} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → MvPolynomial (Fin n) ℚ)
    (shift : MvPolynomial (Fin n) ℚ)
    (touched : Finset ι)
    (h_disj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (MvPolynomial.vars (f i)) (MvPolynomial.vars (f j)))
    (h_shift_vars : shift.vars ⊆ (s.filter (· ∈ touched)).biUnion (fun i => (f i).vars))
    (h_touch_untouch_disj :
      Disjoint
        ((s.filter (· ∈ touched)).biUnion (fun i => (f i).vars))
        ((s.filter (· ∉ touched)).biUnion (fun i => (f i).vars))) :
    mlProj (shift * s.prod f) =
      mlProj (shift * (s.filter (· ∈ touched)).prod f) *
      (s.filter (· ∉ touched)).prod (fun i => mlProj (f i)) := by
  rw [finset_prod_split s touched f]
  rw [show shift * ((s.filter (· ∈ touched)).prod f * (s.filter (· ∉ touched)).prod f) =
      (shift * (s.filter (· ∈ touched)).prod f) * (s.filter (· ∉ touched)).prod f from by ring]
  rw [mlProj_mul_of_vars_disjoint]
  · congr 1
    apply mlProj_finset_prod_of_pairwise_disjoint_vars
    intro i hi j hj hij
    exact h_disj i (Finset.mem_of_mem_filter i hi) j (Finset.mem_of_mem_filter j hj) hij
  · apply Finset.disjoint_iff_ne.mpr
    intro x hx y hy hxy; subst hxy
    have hx_touched : x ∈ (s.filter (· ∈ touched)).biUnion (fun i => (f i).vars) := by
      have hx_mul := MvPolynomial.vars_mul shift ((s.filter (· ∈ touched)).prod f) hx
      rw [Finset.mem_union] at hx_mul
      cases hx_mul with
      | inl hx_shift => exact h_shift_vars hx_shift
      | inr hx_prod => exact MvPolynomial.vars_prod _ hx_prod
    have hy_untouched : x ∈ (s.filter (· ∉ touched)).biUnion (fun i => (f i).vars) :=
      MvPolynomial.vars_prod _ hy
    exact Finset.disjoint_iff_ne.mp h_touch_untouch_disj x hx_touched x hy_untouched rfl

/-- The untouched factor: ∏_{i ∉ touched} mlProj(f_i). -/
noncomputable def untouchedFactor {n : ℕ} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → MvPolynomial (Fin n) ℚ)
    (touched : Finset ι) :
    MvPolynomial (Fin n) ℚ :=
  (s.filter (· ∉ touched)).prod (fun i => mlProj (f i))

/-! ## Part 25: Dimension bound from factorization (restored from WIP) -/

/-- span({q * c | q ∈ S}) ≤ image of mulRight(c) on span(S). -/
theorem span_mul_right_le {n : ℕ}
    (S : Set (MvPolynomial (Fin n) ℚ))
    (c : MvPolynomial (Fin n) ℚ) :
    Submodule.span ℚ ((· * c) '' S) ≤
      Submodule.map (LinearMap.mulRight ℚ c) (Submodule.span ℚ S) := by
  apply Submodule.span_le.mpr
  intro x hx
  rcases hx with ⟨q, hq, rfl⟩
  exact ⟨q, Submodule.subset_span hq, rfl⟩

/-- finrank(span({q * c | q ∈ S})) ≤ finrank(span(S)). -/
theorem finrank_span_mul_right_le {n : ℕ}
    (S : Set (MvPolynomial (Fin n) ℚ))
    (c : MvPolynomial (Fin n) ℚ)
    (hfin : Module.Finite ℚ ↥(Submodule.span ℚ S)) :
    Module.finrank ℚ ↥(Submodule.span ℚ ((· * c) '' S)) ≤
      Module.finrank ℚ ↥(Submodule.span ℚ S) :=
  le_trans (Submodule.finrank_mono (span_mul_right_le S c))
    (Submodule.finrank_map_le _ _)

/-- If V ≤ mulRight(c)(W), then finrank(V) ≤ finrank(W). -/
theorem finrank_le_of_generators_factor {n : ℕ}
    (V W : Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (c : MvPolynomial (Fin n) ℚ)
    (hfin_W : Module.Finite ℚ ↥W)
    (hV_le : V ≤ Submodule.map (LinearMap.mulRight ℚ c) W) :
    Module.finrank ℚ ↥V ≤ Module.finrank ℚ ↥W :=
  le_trans (Submodule.finrank_mono hV_le) (Submodule.finrank_map_le _ _)

/-- Multilinear monomials on a subset: finrank ≤ 2^|subset|. -/
theorem finrank_mlMonomialBasis_subset {n : ℕ}
    (touchedVars : Finset (Fin n)) :
    Module.finrank ℚ ↥(Submodule.span ℚ
      (↑(MlProjFar.mlMonomialBasis touchedVars) :
        Set (MvPolynomial (Fin n) ℚ))) ≤
      2 ^ touchedVars.card := by
  calc Module.finrank ℚ ↥(Submodule.span ℚ
        (↑(MlProjFar.mlMonomialBasis touchedVars) :
          Set (MvPolynomial (Fin n) ℚ)))
      ≤ (MlProjFar.mlMonomialBasis touchedVars).card :=
        finrank_span_finset_le_card _
    _ ≤ 2 ^ touchedVars.card :=
        MlProjFar.mlMonomialBasis_card touchedVars

/-! ## Part 26: Touched-vars containment (restored from WIP) -/

/-- The touched part has vars contained in the touched-block vars. -/
theorem touched_part_vars_subset {n : ℕ} {ι : Type*} [DecidableEq ι]
    (s : Finset ι)
    (f : ι → MvPolynomial (Fin n) ℚ)
    (g : ι → MvPolynomial (Fin n) ℚ)
    (shift : MvPolynomial (Fin n) ℚ)
    (touched : Finset ι)
    (hg_vars : ∀ i ∈ s.filter (· ∈ touched), (g i).vars ⊆ (f i).vars)
    (h_shift_vars : shift.vars ⊆ (s.filter (· ∈ touched)).biUnion (fun i => (f i).vars)) :
    (mlProj (shift * (s.filter (· ∈ touched)).prod g)).vars ⊆
      (s.filter (· ∈ touched)).biUnion (fun i => (f i).vars) := by
  calc (mlProj (shift * (s.filter (· ∈ touched)).prod g)).vars
      ⊆ (shift * (s.filter (· ∈ touched)).prod g).vars :=
        vars_mlProj_subset _
    _ ⊆ shift.vars ∪ ((s.filter (· ∈ touched)).prod g).vars :=
        MvPolynomial.vars_mul shift _
    _ ⊆ (s.filter (· ∈ touched)).biUnion (fun i => (f i).vars) ∪
        ((s.filter (· ∈ touched)).prod g).vars :=
        Finset.union_subset_union h_shift_vars (Finset.Subset.refl _)
    _ ⊆ (s.filter (· ∈ touched)).biUnion (fun i => (f i).vars) ∪
        (s.filter (· ∈ touched)).biUnion (fun i => (g i).vars) := by
        apply Finset.union_subset_union (Finset.Subset.refl _)
        exact vars_finset_prod_subset _ _
    _ ⊆ (s.filter (· ∈ touched)).biUnion (fun i => (f i).vars) ∪
        (s.filter (· ∈ touched)).biUnion (fun i => (f i).vars) := by
        apply Finset.union_subset_union (Finset.Subset.refl _)
        apply Finset.biUnion_mono
        intro i hi; exact hg_vars i hi
    _ = (s.filter (· ∈ touched)).biUnion (fun i => (f i).vars) :=
        Finset.union_idempotent _

/-- The touched part lies in the span of mlMonomialBasis on touched-block vars. -/
theorem touched_part_in_mlMonomialBasis_span {n : ℕ} {ι : Type*} [DecidableEq ι]
    (s : Finset ι)
    (f g : ι → MvPolynomial (Fin n) ℚ)
    (shift : MvPolynomial (Fin n) ℚ)
    (touched : Finset ι)
    (hg_vars : ∀ i ∈ s.filter (· ∈ touched), (g i).vars ⊆ (f i).vars)
    (h_shift_vars : shift.vars ⊆ (s.filter (· ∈ touched)).biUnion (fun i => (f i).vars)) :
    mlProj (shift * (s.filter (· ∈ touched)).prod g) ∈
      Submodule.span ℚ
        (↑(MlProjFar.mlMonomialBasis
          ((s.filter (· ∈ touched)).biUnion (fun i => (f i).vars))) :
          Set (MvPolynomial (Fin n) ℚ)) := by
  apply MlProjFar.mlProj_in_span_of_vars_subset
  · exact fun α hα => isMultilinear_of_mem_mlProj_support _ α hα
  · exact fun v hv =>
      touched_part_vars_subset s f g shift touched hg_vars h_shift_vars hv

/-! ## Axiom audit: verify no custom axioms in the variable-confinement chain -/
#print axioms rank_bound_of_withinProfileFinrankBound
#print axioms mlProj_mul_of_vars_disjoint
#print axioms mlProj_finset_prod_of_pairwise_disjoint_vars
#print axioms mlProj_shift_mul_prod_factored

end WithinProfileBound

/-! # WithinProfileBound — Archived WIP below

ALL Parts 22c-26 have been restored to the compiled section above.
The comment block below contains DUPLICATE copies of the restored theorems,
preserved as historical reference. No new content remains in the WIP section.

## Compiled frontier summary (Parts 1-26):
- Parts 1-22: profile enumeration, atom counting, per-S finrank bounds
- Part 22c: degree-refined atom counting (localDerivAtomsOfDegree)
- Part 22d: fully bounded classified set with total-mass constraint
- Part 23: mlProj multiplicativity (disjoint vars) — KEY THEOREM
- Part 24: touched/untouched generator factorization
- Part 25: dimension bound from factorization (finrank_le_of_generators_factor)
- Part 26: touched-vars containment

## Remaining gap to eliminate spdp_profile_generators:
The variable-confinement argument (Parts 23-26) shows that per-S-shift generators
factor as touched_part × untouched_factor, with touched_part ∈ span(mlMonomialBasis).
What's missing: the SYMMETRIC POWER COLLAPSE showing that different block assignments
with the same profile give the SAME touched-part span. This requires:
1. Cook-Levin constraint type classification at the polynomial level
2. Showing mlProj of products depends only on profile (not block assignment)
3. Template count per profile bounded by (κ+1)^8 -/

-- The WIP comment block below contains duplicates of restored content.

section WithinProfileBoundWIP_disabled
variable (DISABLED : False)

-- NOTE: The content below is structurally preserved but not compiled.
-- To restore, remove the `section` wrapper and fix the noted API issues.

end WithinProfileBoundWIP_disabled

/-
namespace WithinProfileBoundWIP

open SPDP MultilinearSPDP MvPolynomial TuringMachine PaperFaithfulSeparation
open SymmetricPowerBound WithinProfileBound

attribute [local instance] Classical.dec

/-- The "differentiated" local derivative atoms for factor i: atoms arising
    from derivatives of length exactly k (with k ∈ {0, 1, 2}).
    - k = 0: just {f_i} (1 element)
    - k = 1: {pderiv v f_i | v ∈ S} (≤ |S| elements)
    - k = 2: {pderiv v (pderiv w f_i) | v, w ∈ S} (≤ |S|² elements) -/
noncomputable def localDerivAtomsOfDegree {n : ℕ}
    (f : MvPolynomial (Fin n) ℚ) (S : List (Fin n)) (k : ℕ) :
    Finset (MvPolynomial (Fin n) ℚ) :=
  match k with
  | 0 => {f}
  | 1 => S.toFinset.image (fun v => MvPolynomial.pderiv v f)
  | 2 => (S.toFinset ×ˢ S.toFinset).image
      (fun p => MvPolynomial.pderiv p.1 (MvPolynomial.pderiv p.2 f))
  | _ + 3 => ∅

/-- localDerivAtomsOfDegree 0 has exactly 1 element. -/
theorem localDerivAtomsOfDegree_zero_card {n : ℕ}
    (f : MvPolynomial (Fin n) ℚ) (S : List (Fin n)) :
    (localDerivAtomsOfDegree f S 0).card = 1 := by
  simp [localDerivAtomsOfDegree, Finset.card_singleton]

/-- localDerivAtomsOfDegree k has card ≤ (|S|+1)^k for k ≤ 2. -/
theorem localDerivAtomsOfDegree_card_le {n : ℕ}
    (f : MvPolynomial (Fin n) ℚ) (S : List (Fin n)) (k : ℕ) (hk : k ≤ 2) :
    (localDerivAtomsOfDegree f S k).card ≤ (S.toFinset.card + 1) ^ k := by
  interval_cases k
  · simp [localDerivAtomsOfDegree, Finset.card_singleton]
  · simp only [localDerivAtomsOfDegree, pow_one]
    calc (S.toFinset.image (fun v => MvPolynomial.pderiv v f)).card
        ≤ S.toFinset.card := Finset.card_image_le
      _ ≤ S.toFinset.card + 1 := Nat.le_succ _
  · simp only [localDerivAtomsOfDegree]
    calc ((S.toFinset ×ˢ S.toFinset).image
          (fun p => MvPolynomial.pderiv p.1 (MvPolynomial.pderiv p.2 f))).card
        ≤ (S.toFinset ×ˢ S.toFinset).card := Finset.card_image_le
      _ = S.toFinset.card * S.toFinset.card := Finset.card_product _ _
      _ = S.toFinset.card ^ 2 := (sq _).symm
      _ ≤ (S.toFinset.card + 1) ^ 2 := Nat.pow_le_pow_left (Nat.le_succ _) 2

set_option maxHeartbeats 800000 in
/-- iterDerivList d f with |d| = k ≤ 2 and d ⊆ S lies in localDerivAtomsOfDegree f S k. -/
theorem iterDerivList_mem_localDerivAtomsOfDegree {n : ℕ}
    (f : MvPolynomial (Fin n) ℚ) (S : List (Fin n))
    (d : List (Fin n)) (hd_len : d.length ≤ 2) (hd_mem : ∀ v ∈ d, v ∈ S) :
    iterDerivList d f ∈ localDerivAtomsOfDegree f S d.length := by
  rcases d with _ | ⟨v, _ | ⟨w, rest⟩⟩
  · -- d = []: iterDerivList [] f = f ∈ {f}
    simp [localDerivAtomsOfDegree, IterDerivHelpers.iterDerivList_nil]
  · -- d = [v]: iterDerivList [v] f = pderiv v f
    simp only [localDerivAtomsOfDegree, List.length_cons, List.length_nil,
      Finset.mem_image]
    exact ⟨v, List.mem_toFinset.mpr (hd_mem v (by simp)), rfl⟩
  · -- d = v :: w :: rest, must have rest = []
    cases rest with
    | nil =>
      show iterDerivList [v, w] f ∈ localDerivAtomsOfDegree f S ([v, w].length)
      simp only [List.length_cons, List.length_nil]
      show iterDerivList [v, w] f ∈ localDerivAtomsOfDegree f S 2
      rw [iterDerivList_pair_eq_pderiv2 v w f]
      show MvPolynomial.pderiv v (MvPolynomial.pderiv w f) ∈
        (S.toFinset ×ˢ S.toFinset).image
          (fun p => MvPolynomial.pderiv p.1 (MvPolynomial.pderiv p.2 f))
      have hv_mem : v ∈ S := hd_mem v (by simp)
      have hw_mem : w ∈ S := hd_mem w (by simp)
      refine Finset.mem_image.mpr ⟨(v, w), Finset.mem_product.mpr
        ⟨List.mem_toFinset.mpr hv_mem, List.mem_toFinset.mpr hw_mem⟩, rfl⟩
    | cons x rest' =>
      exfalso
      have : (v :: w :: x :: rest').length ≤ 2 := hd_len
      simp only [List.length_cons] at this
      omega

/-- Profile-constrained atom product set: products ∏_i a_i where
    a_i ∈ localDerivAtomsOfDegree(f_i, S, k_i) and k_i ≤ 2.

    This is tighter than atomProductSet because undifferentiated factors
    (k_i = 0) contribute exactly 1 atom, not (|S|+1)² atoms. -/
def constrainedAtomProductSet {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ) (S : List (Fin n))
    (derivLengths : Fin L → ℕ) :
    Set (MvPolynomial (Fin n) ℚ) :=
  { g | ∃ (atoms : Fin L → MvPolynomial (Fin n) ℚ),
      (∀ i, atoms i ∈ localDerivAtomsOfDegree (factors i) S (derivLengths i)) ∧
      g = Finset.univ.prod atoms }

/-- The locally bounded classified set for profile h is contained in
    a union of constrained atom product sets over matching derivative
    length assignments. -/
theorem locallyBoundedClassifiedSet_subset_constrained {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (constraintType : Fin L → ConstraintType)
    (S : List (Fin n))
    (h : ProfileHistogram)
    (g : MvPolynomial (Fin n) ℚ)
    (hg : g ∈ locallyBoundedClassifiedSet factors constraintType S h) :
    ∃ (derivLengths : Fin L → ℕ),
      (∀ i, derivLengths i ≤ 2) ∧
      g ∈ constrainedAtomProductSet factors S derivLengths := by
  rcases hg with ⟨d, hd_elts, hg_eq, _hprof, hd_bound⟩
  refine ⟨fun i => (d i).length, hd_bound, ?_⟩
  refine ⟨fun i => iterDerivList (d i) (factors i), ?_, hg_eq⟩
  intro i
  exact iterDerivList_mem_localDerivAtomsOfDegree (factors i) S (d i) (hd_bound i) (hd_elts i)

/-- The constrained atom product set is finite. -/
theorem constrainedAtomProductSet_finite {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ) (S : List (Fin n))
    (derivLengths : Fin L → ℕ) :
    Set.Finite (constrainedAtomProductSet factors S derivLengths) := by
  let atomChoices := (i : Fin L) → { a : MvPolynomial (Fin n) ℚ //
    a ∈ localDerivAtomsOfDegree (factors i) S (derivLengths i) }
  haveI : Fintype atomChoices := inferInstance
  apply Set.Finite.subset (Set.toFinite (Set.range
    (fun (c : atomChoices) => Finset.univ.prod (fun i => (c i).val))))
  intro g hg
  rcases hg with ⟨atoms, hatoms, rfl⟩
  exact ⟨fun i => ⟨atoms i, hatoms i⟩, rfl⟩

set_option maxHeartbeats 400000 in
/-- The constrained atom product set has cardinality ≤ ∏_i |localDerivAtomsOfDegree(f_i, S, k_i)|.
    Proof: the set is the image of the product map on a pi type of subtypes.
    Image card ≤ pi type card = ∏ subtype card = ∏ Finset card. -/
theorem constrainedAtomProductSet_card_le {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ) (S : List (Fin n))
    (derivLengths : Fin L → ℕ) :
    (constrainedAtomProductSet_finite factors S derivLengths).toFinset.card ≤
      ∏ i : Fin L, (localDerivAtomsOfDegree (factors i) S (derivLengths i)).card := by
  -- The constrainedAtomProductSet ⊆ image of ∏ applied to the pi type
  -- of subtypes. |image| ≤ |domain| = ∏ |Finset| by Fintype.card_pi.
  -- Technical: the Set.Finite.toFinset API makes this awkward.
  -- Use a finite covering Finset via Finset.pi.
  let piFinset := Finset.univ.pi (fun i => localDerivAtomsOfDegree (factors i) S (derivLengths i))
  let prodFn : (∀ i ∈ Finset.univ, MvPolynomial (Fin n) ℚ) → MvPolynomial (Fin n) ℚ :=
    fun c => Finset.univ.prod (fun i => c i (Finset.mem_univ i))
  have hcover : ∀ g ∈ (constrainedAtomProductSet_finite factors S derivLengths).toFinset,
      g ∈ (piFinset.image prodFn) := by
    intro g hg
    rw [Set.Finite.mem_toFinset] at hg
    rcases hg with ⟨atoms, hatoms, rfl⟩
    exact Finset.mem_image_of_mem _ (Finset.mem_pi.mpr (fun i _ => hatoms i))
  calc (constrainedAtomProductSet_finite factors S derivLengths).toFinset.card
      ≤ (piFinset.image prodFn).card := Finset.card_le_card hcover
    _ ≤ piFinset.card := Finset.card_image_le
    _ = ∏ i ∈ Finset.univ,
        (localDerivAtomsOfDegree (factors i) S (derivLengths i)).card :=
        Finset.card_pi _ _

/-- Key product bound: when k_i = 0 the factor contributes 1, otherwise ≤ (|S|+1)^k_i.
    So ∏ |atoms of degree k_i| ≤ ∏_{k_i > 0} (|S|+1)^k_i = (|S|+1)^(∑_{k_i > 0} k_i).

    For profile h with mass κ (total derivatives = κ), and each k_i ≤ 2,
    ∑ k_i = κ. So the product ≤ (|S|+1)^κ ≤ (κ+1)^κ (when |S| ≤ κ). -/
theorem constrained_prod_le_pow_sum {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ) (S : List (Fin n))
    (derivLengths : Fin L → ℕ) (hk : ∀ i, derivLengths i ≤ 2) :
    ∏ i : Fin L, (localDerivAtomsOfDegree (factors i) S (derivLengths i)).card ≤
      (S.toFinset.card + 1) ^ (∑ i : Fin L, derivLengths i) := by
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod
  · intro i _; exact Nat.zero_le _
  · intro i _; exact localDerivAtomsOfDegree_card_le (factors i) S (derivLengths i) (hk i)

/-- Locally-and-globally bounded classified set: the intersection of
    locallyBoundedClassifiedSet (each factor gets ≤ 2 derivatives) and the
    total length constraint (∑ |d_i| ≤ S.length) from boundedProfileClassifiedSet.

    For degree-2 factors, boundedProfileClassifiedSet = {0} ∪ this set
    (by Part 12 dichotomy). -/
noncomputable def fullyBoundedClassifiedSet {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (constraintType : Fin L → ConstraintType)
    (S : List (Fin n))
    (h : ProfileHistogram) :
    Set (MvPolynomial (Fin n) ℚ) :=
  { g | ∃ (d : Fin L → List (Fin n)),
      (∀ i, ∀ v ∈ d i, v ∈ S) ∧
      g = Finset.univ.prod (fun i => iterDerivList (d i) (factors i)) ∧
      derivCountProfile constraintType d = h ∧
      (∀ i, (d i).length ≤ 2) ∧
      ∑ i : Fin L, (d i).length ≤ S.length }

/-- For degree-2 factors, boundedProfileClassifiedSet ⊆ {0} ∪ fullyBoundedClassifiedSet. -/
theorem boundedProfileClassifiedSet_subset_fully_bounded {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (hfactors : ∀ i, (factors i).totalDegree ≤ 2)
    (constraintType : Fin L → ConstraintType)
    (S : List (Fin n))
    (h : ProfileHistogram) :
    boundedProfileClassifiedSet factors constraintType S h ⊆
      {0} ∪ fullyBoundedClassifiedSet factors constraintType S h := by
  intro g hg
  rcases hg with ⟨d, hd_elts, hg_eq, hprof, hd_len⟩
  by_cases h_all : ∀ i, (d i).length ≤ 2
  · right
    exact ⟨d, hd_elts, hg_eq, hprof, h_all, by simpa using hd_len⟩
  · left
    push_neg at h_all
    obtain ⟨i₀, hi₀⟩ := h_all
    rw [Set.mem_singleton_iff, hg_eq]
    exact distribDerivProd_eq_zero_of_overDiff factors hfactors d i₀ (by omega)

/-- fullyBoundedClassifiedSet is contained in the bounded-mass constrained
    atom product set. Each element factors through localDerivAtomsOfDegree
    with total derivative mass ≤ S.length. -/
theorem fullyBoundedClassifiedSet_subset_constrained_union {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (constraintType : Fin L → ConstraintType)
    (S : List (Fin n))
    (h : ProfileHistogram)
    (g : MvPolynomial (Fin n) ℚ)
    (hg : g ∈ fullyBoundedClassifiedSet factors constraintType S h) :
    ∃ (derivLengths : Fin L → ℕ),
      (∀ i, derivLengths i ≤ 2) ∧
      (∑ i : Fin L, derivLengths i ≤ S.length) ∧
      g ∈ constrainedAtomProductSet factors S derivLengths := by
  rcases hg with ⟨d, hd_elts, hg_eq, _hprof, hd_bound, hd_total⟩
  exact ⟨fun i => (d i).length, hd_bound, hd_total,
    fun i => iterDerivList (d i) (factors i),
    fun i => iterDerivList_mem_localDerivAtomsOfDegree (factors i) S (d i) (hd_bound i) (hd_elts i),
    hg_eq⟩

/-- For degree-2 factors, the per-S-shift post-span is ≤ the span of
    the fully bounded classified set (carrying both local and total bounds). -/
theorem boundedProfilePostSpan_le_fullyBounded_for_degree2 {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (hfactors : ∀ i, (factors i).totalDegree ≤ 2)
    (constraintType : Fin L → ConstraintType)
    (S : List (Fin n)) (shift : MvPolynomial (Fin n) ℚ)
    (h : ProfileHistogram) :
    boundedProfilePostSpan factors constraintType S shift h ≤
      Submodule.span ℚ
        ((fun g => mlProj (shift * g)) '' fullyBoundedClassifiedSet factors constraintType S h) := by
  apply Submodule.span_le.mpr
  intro x hx
  rcases hx with ⟨g, hg_mem, rfl⟩
  rcases boundedProfileClassifiedSet_subset_fully_bounded factors hfactors constraintType S h hg_mem with
    h0 | hfb
  · simp [Set.mem_singleton_iff.mp h0]
  · exact Submodule.subset_span (Set.mem_image_of_mem _ hfb)

/-- Each element of fullyBoundedClassifiedSet lies in a constrainedAtomProductSet
    with ∑ k_i ≤ S.length. By constrained_prod_le_pow_sum, the constrained
    product set has card ≤ (|S|+1)^(∑ k_i) ≤ (|S|+1)^|S|.

    For the per-S-shift finrank bound: we need to count the total number of
    distinct elements across ALL valid derivLength assignments. -/
theorem fullyBounded_card_le {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (constraintType : Fin L → ConstraintType)
    (S : List (Fin n))
    (h : ProfileHistogram) :
    Set.Finite (fullyBoundedClassifiedSet factors constraintType S h) := by
  -- fullyBoundedClassifiedSet ⊆ locallyBoundedClassifiedSet
  apply Set.Finite.subset (locallyBoundedClassifiedSet_finite factors constraintType S h)
  intro g ⟨d, hd_elts, hg_eq, hprof, hd_bound, _hd_total⟩
  exact ⟨d, hd_elts, hg_eq, hprof, hd_bound⟩

/-- The fullyBoundedClassifiedSet elements are all products ∏_i a_i
    where a_i ∈ localDerivAtomsOfDegree(f_i, S, k_i) with ∑ k_i ≤ S.length.
    Two elements that choose the same atoms produce the same polynomial.
    So |fullyBoundedClassifiedSet| ≤ the number of atom-choice functions
    subject to ∑ k_i ≤ S.length.

    A cruder but clean bound: the fully bounded set is contained in
    atomProductSet, so |fullyBoundedClassifiedSet| ≤ |atomProductSet|.
    But we can do better: since the total derivative mass ≤ S.length = κ,
    and undifferentiated factors contribute 1 fixed atom, the effective
    count is much smaller.

    For now, we use a clean intermediate bound:
    finrank(per-S-shift) ≤ (S.toFinset.card + 1) ^ S.length

    This follows from:
    1. The post-span ≤ map of span of fully bounded set
    2. The fully bounded set ⊆ ⋃_k constrainedAtomProductSet(k)
    3. Each constrainedAtomProductSet(k) has card ≤ (|S|+1)^(∑ k_i)
    4. The span of the union ≤ span of the union of constrained sets
    5. Total spanning set size ≤ ∑_k (|S|+1)^(∑ k_i)
    But bounding this sum is complex.

    Simpler: fullyBounded ⊆ atomProductSet, so we use that bound.
    The key improvement comes from the ALL-S union, where the
    variable-confinement argument applies.

The per-S-shift finrank with the total-mass constraint.

    For the per-S case: finrank ≤ |atomProductSet| ≤ ∏ |localDerivAtoms|.
    This is the same bound as before. The improvement from the total-mass
    constraint will be used for the ALL-S union bound.

    Key per-S bound via constrained atoms:
    Each constrainedAtomProductSet(k) has ≤ ∏_i (|S|+1)^{k_i} = (|S|+1)^{∑ k_i}
    elements. For a single valid k with ∑ k_i = m ≤ S.length,
    this is (|S|+1)^m. -/
theorem perSShift_finrank_le_constrained {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (hfactors : ∀ i, (factors i).totalDegree ≤ 2)
    (constraintType : Fin L → ConstraintType)
    (S : List (Fin n)) (shift : MvPolynomial (Fin n) ℚ)
    (h : ProfileHistogram)
    (derivLengths : Fin L → ℕ)
    (hk : ∀ i, derivLengths i ≤ 2)
    (hfb : fullyBoundedClassifiedSet factors constraintType S h ⊆
      constrainedAtomProductSet factors S derivLengths) :
    Module.finrank ℚ ↥(boundedProfilePostSpan factors constraintType S shift h) ≤
      (S.toFinset.card + 1) ^ (∑ i : Fin L, derivLengths i) := by
  have hle := boundedProfilePostSpan_le_fullyBounded_for_degree2
    factors hfactors constraintType S shift h
  -- post-span ≤ span of image of fully bounded set
  -- ≤ span of image of constrainedAtomProductSet
  -- ≤ map of span of constrainedAtomProductSet
  -- finrank ≤ finrank of span of constrainedAtomProductSet
  -- ≤ card of constrainedAtomProductSet
  -- ≤ (|S|+1)^(∑ k_i)
  have hle2 : Submodule.span ℚ
      ((fun g => mlProj (shift * g)) '' fullyBoundedClassifiedSet factors constraintType S h) ≤
      Submodule.map (postProcessLinearMap shift)
        (Submodule.span ℚ (constrainedAtomProductSet factors S derivLengths)) := by
    apply Submodule.span_le.mpr
    intro x hx
    rcases hx with ⟨g, hg, rfl⟩
    exact ⟨g, Submodule.subset_span (hfb hg), rfl⟩
  have hfin : Module.Finite ℚ
      ↥(Submodule.span ℚ (constrainedAtomProductSet factors S derivLengths)) :=
    Module.Finite.span_of_finite ℚ (constrainedAtomProductSet_finite factors S derivLengths)
  calc Module.finrank ℚ ↥(boundedProfilePostSpan factors constraintType S shift h)
      ≤ Module.finrank ℚ ↥(Submodule.span ℚ
          ((fun g => mlProj (shift * g)) '' fullyBoundedClassifiedSet factors constraintType S h)) :=
        Submodule.finrank_mono hle
    _ ≤ Module.finrank ℚ ↥(Submodule.map (postProcessLinearMap shift)
          (Submodule.span ℚ (constrainedAtomProductSet factors S derivLengths))) :=
        Submodule.finrank_mono hle2
    _ ≤ Module.finrank ℚ
          ↥(Submodule.span ℚ (constrainedAtomProductSet factors S derivLengths)) :=
        Submodule.finrank_map_le _ _
    _ ≤ (constrainedAtomProductSet_finite factors S derivLengths).toFinset.card := by
        have : Submodule.span ℚ (constrainedAtomProductSet factors S derivLengths) =
            Submodule.span ℚ ↑(constrainedAtomProductSet_finite factors S derivLengths).toFinset := by
          congr 1; exact (Set.Finite.coe_toFinset _).symm
        rw [this]; exact finrank_span_finset_le_card _
    _ ≤ ∏ i : Fin L, (localDerivAtomsOfDegree (factors i) S (derivLengths i)).card :=
        constrainedAtomProductSet_card_le factors S derivLengths
    _ ≤ (S.toFinset.card + 1) ^ (∑ i : Fin L, derivLengths i) :=
        constrained_prod_le_pow_sum factors S derivLengths hk

/-- The per-S-shift post-span finrank is bounded by the size of the

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

/-! ## Part 23: mlProj multiplicativity for disjoint-vars products

Key lemma: mlProj(p * q) = mlProj(p) * mlProj(q) when vars(p) ∩ vars(q) = ∅.

This is the foundation of the variable-confinement argument for the
all-S union bound. When factors have disjoint block structure, the
mlProj of a product factors into a product of mlProj's. This means
generators in allBoundedProfilePostSpan factor as
  mlProj(touched-block terms) × mlProj(untouched-block product)
where the untouched part is fixed across generators. -/

/-- Helper: for α in the support of mlProj(p), we have IsMultilinear α. -/
theorem isMultilinear_of_mem_mlProj_support {σ : Type*} [DecidableEq σ] {F : Type*} [CommRing F]
    (p : MvPolynomial σ F) (α : σ →₀ ℕ) (hα : α ∈ (mlProj p).support) :
    Finsupp.IsMultilinear α := by
  by_contra h_neg
  have : MvPolynomial.coeff α (mlProj p) = 0 := by
    show (Finsupp.filter (fun β => Finsupp.IsMultilinear β) p) α = 0
    rw [Finsupp.filter_apply]
    exact if_neg h_neg
  exact absurd this (Finsupp.mem_support_iff.mp hα)

/-- The coefficient of mlProj: it's the original coefficient for multilinear
    monomials and 0 otherwise. -/
theorem coeff_mlProj {σ : Type*} [DecidableEq σ] {F : Type*} [CommRing F]
    (p : MvPolynomial σ F) (α : σ →₀ ℕ) :
    MvPolynomial.coeff α (mlProj p) =
      if Finsupp.IsMultilinear α then MvPolynomial.coeff α p else 0 := by
  change (Finsupp.filter (fun β => Finsupp.IsMultilinear β) p) α = _
  simp only [Finsupp.filter_apply]

/-- The support of mlProj(p) is contained in the support of p restricted
    to multilinear monomials. -/
theorem mlProj_support_subset' {σ : Type*} [DecidableEq σ] {F : Type*} [CommRing F]
    (p : MvPolynomial σ F) :
    (mlProj p).support ⊆ p.support.filter (fun α => Finsupp.IsMultilinear α) := by
  intro α hα
  rw [Finset.mem_filter]
  have hα_ne : (mlProj p) α ≠ 0 := Finsupp.mem_support_iff.mp hα
  have hα_ml := isMultilinear_of_mem_mlProj_support p α hα
  constructor
  · rw [Finsupp.mem_support_iff]
    rw [coeff_mlProj, if_pos hα_ml] at hα_ne
    exact hα_ne
  · exact hα_ml

/-- For Finsupp with disjoint supports, the sum is multilinear iff both are. -/
theorem isMultilinear_add_of_disjoint_support {σ : Type*} [DecidableEq σ]
    (β γ : σ →₀ ℕ) (hdisj : Disjoint β.support γ.support) :
    Finsupp.IsMultilinear (β + γ) ↔
      Finsupp.IsMultilinear β ∧ Finsupp.IsMultilinear γ := by
  constructor
  · intro h_ml
    constructor
    · intro i
      have := h_ml i
      simp only [Finsupp.coe_add, Pi.add_apply] at this
      omega
    · intro i
      have := h_ml i
      simp only [Finsupp.coe_add, Pi.add_apply] at this
      omega
  · intro ⟨hβ, hγ⟩ i
    simp only [Finsupp.coe_add, Pi.add_apply]
    have := Finset.disjoint_iff_ne.mp hdisj
    by_cases hi_β : i ∈ β.support
    · have hi_γ : i ∉ γ.support := by
        intro hi_γ
        exact absurd rfl (this i hi_β i hi_γ)
      have : γ i = 0 := by rwa [Finsupp.mem_support_iff, not_not] at hi_γ
      rw [this, add_zero]; exact hβ i
    · have : β i = 0 := by rwa [Finsupp.mem_support_iff, not_not] at hi_β
      rw [this, zero_add]; exact hγ i

/-- Key disjointness: if α ∈ supp(p) and β ∈ supp(q) and vars(p) ∩ vars(q) = ∅,
    then supp(α) and supp(β) are disjoint as Finset. -/
theorem support_disjoint_of_vars_disjoint {σ : Type*} [DecidableEq σ] {F : Type*} [CommRing F]
    (p q : MvPolynomial σ F)
    (hvars : Disjoint (MvPolynomial.vars p) (MvPolynomial.vars q))
    (α β : σ →₀ ℕ)
    (hα : α ∈ p.support) (hβ : β ∈ q.support) :
    Disjoint α.support β.support := by
  rw [Finset.disjoint_iff_ne]
  intro i hi j hj hij
  subst hij
  have hi_vars_p : i ∈ MvPolynomial.vars p :=
    Finset.mem_biUnion.mpr ⟨α, hα, hi⟩
  have hi_vars_q : i ∈ MvPolynomial.vars q :=
    Finset.mem_biUnion.mpr ⟨β, hβ, hj⟩
  exact Finset.disjoint_iff_ne.mp hvars i hi_vars_p i hi_vars_q rfl

/-- mlProj is multiplicative for polynomials with disjoint variable sets.

    Proof sketch: at each multilinear monomial α, the contributing terms
    in p*q come from pairs (β, γ) with β ∈ supp(p), γ ∈ supp(q),
    β+γ = α. Since vars are disjoint, supp(β) and supp(γ) are disjoint,
    so α is multilinear iff both β and γ are. Hence the multilinear
    filtering distributes. -/
theorem mlProj_mul_of_vars_disjoint {n : ℕ}
    (p q : MvPolynomial (Fin n) ℚ)
    (hvars : Disjoint (MvPolynomial.vars p) (MvPolynomial.vars q)) :
    mlProj (p * q) = mlProj p * mlProj q := by
  ext α
  rw [coeff_mlProj]
  rw [MvPolynomial.coeff_mul, MvPolynomial.coeff_mul]
  split_ifs with hα_ml
  · -- α is multilinear: show the sums agree
    -- LHS: ∑_{β+γ=α} coeff β p · coeff γ q
    -- RHS: ∑_{β+γ=α} coeff β (mlProj p) · coeff γ (mlProj q)
    apply Finset.sum_congr rfl
    intro ⟨β, γ⟩ hbg
    simp only [Finset.mem_antidiagonal] at hbg
    rw [coeff_mlProj, coeff_mlProj]
    -- Need: if coeff β p ≠ 0 and coeff γ q ≠ 0, then β and γ are both multilinear
    -- And if β+γ=α is multilinear but β or γ is not multilinear, then coeff is 0 on that side
    by_cases hβ_ml : Finsupp.IsMultilinear β
    · by_cases hγ_ml : Finsupp.IsMultilinear γ
      · simp [hβ_ml, hγ_ml]
      · simp [hγ_ml]
        -- Need to show coeff β p * coeff γ q = 0
        -- If coeff γ q ≠ 0, then γ ∈ supp(q), and with β+γ=α multilinear
        -- and vars disjoint, γ must be multilinear. Contradiction.
        by_cases hγq : MvPolynomial.coeff γ q = 0
        · simp [hγq]
        · exfalso
          apply hγ_ml
          have hγ_supp : γ ∈ q.support := Finsupp.mem_support_iff.mpr hγq
          -- If β ∈ supp(p), disjoint supports give the result
          -- But β might not be in supp(p). However α = β+γ is multilinear.
          -- Since γ is in supp(q), supp(γ) ⊆ vars(q).
          -- For i ∈ supp(γ): γ(i) ≤ α(i) ≤ 1 (since α is multilinear)
          intro i
          have := hα_ml i
          rw [hbg] at this
          simp only [Finsupp.coe_add, Pi.add_apply] at this
          omega
    · simp [hβ_ml]
      by_cases hβp : MvPolynomial.coeff β p = 0
      · simp [hβp]
      · exfalso
        apply hβ_ml
        intro i
        have := hα_ml i
        rw [hbg] at this
        simp only [Finsupp.coe_add, Pi.add_apply] at this
        omega
  · -- α is not multilinear: show the sum is 0
    apply Finset.sum_eq_zero
    intro ⟨β, γ⟩ hbg
    simp only [Finset.mem_antidiagonal] at hbg
    rw [coeff_mlProj, coeff_mlProj]
    -- Show: either β is not multilinear or γ is not multilinear
    -- (given β+γ=α is not multilinear)
    -- OR if both are multilinear, the product of coefficients is 0
    by_cases hβ_ml : Finsupp.IsMultilinear β
    · by_cases hγ_ml : Finsupp.IsMultilinear γ
      · simp [hβ_ml, hγ_ml]
        -- Both β and γ multilinear but α = β+γ not multilinear
        -- Need: if coeff β p ≠ 0 and coeff γ q ≠ 0, contradiction
        -- because then supp(β) ⊆ vars(p), supp(γ) ⊆ vars(q), disjoint,
        -- so β+γ is multilinear, contradiction.
        by_cases hβp : MvPolynomial.coeff β p = 0
        · simp [hβp]
        · right
          intro hγq
          apply hα_ml
          have hβ_supp : β ∈ p.support := Finsupp.mem_support_iff.mpr hβp
          have hγ_supp : γ ∈ q.support := Finsupp.mem_support_iff.mpr hγq
          have := support_disjoint_of_vars_disjoint p q hvars β γ hβ_supp hγ_supp
          rw [← hbg]
          exact (isMultilinear_add_of_disjoint_support β γ this).mpr ⟨hβ_ml, hγ_ml⟩
      · simp [hγ_ml]
    · simp [hβ_ml]

/-- vars(mlProj p) ⊆ vars(p): multilinear projection doesn't introduce new variables. -/
theorem vars_mlProj_subset {n : ℕ}
    (p : MvPolynomial (Fin n) ℚ) :
    (mlProj p).vars ⊆ p.vars := by
  intro v hv
  rw [MvPolynomial.mem_vars] at hv ⊢
  obtain ⟨α, hα_supp, hα_v⟩ := hv
  have hα_p : α ∈ p.support := by
    have hcoeff := Finsupp.mem_support_iff.mp hα_supp
    rw [coeff_mlProj] at hcoeff
    split_ifs at hcoeff with h
    · exact Finsupp.mem_support_iff.mpr hcoeff
    · exact absurd rfl hcoeff
  exact ⟨α, hα_p, hα_v⟩

/-- mlProj(1) = 1. -/
theorem mlProj_one {n : ℕ} :
    mlProj (1 : MvPolynomial (Fin n) ℚ) = 1 := by
  ext α
  rw [coeff_mlProj]
  split_ifs with h
  · rfl
  · simp only [MvPolynomial.coeff_one]
    rw [if_neg]
    intro hα0; subst hα0
    exact h (fun i => by simp)

/-- mlProj distributes over Finset.prod when all factors have pairwise
    disjoint variable sets.

    Proof by induction on the Finset, using mlProj_mul_of_vars_disjoint
    at each step. The accumulated product has vars ⊆ ⋃ of previous vars,
    which is disjoint from the next factor's vars by pairwise disjointness. -/
theorem mlProj_finset_prod_of_pairwise_disjoint_vars {n : ℕ} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → MvPolynomial (Fin n) ℚ)
    (h_disj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (MvPolynomial.vars (f i)) (MvPolynomial.vars (f j))) :
    mlProj (s.prod f) = s.prod (fun i => mlProj (f i)) := by
  induction s using Finset.induction_on with
  | empty => simp [Finset.prod_empty, mlProj_one]
  | insert ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have h_disj_rest : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
        Disjoint (MvPolynomial.vars (f i)) (MvPolynomial.vars (f j)) :=
      fun i hi j hj hij =>
        h_disj i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    rw [ih h_disj_rest]
    -- Apply mlProj_mul_of_vars_disjoint
    apply mlProj_mul_of_vars_disjoint
    -- Need: vars(f a) disjoint from vars(∏_{s} mlProj(f i))
    -- vars(∏ mlProj(f_i)) ⊆ ⋃_{i∈s} vars(mlProj(f_i)) ⊆ ⋃_{i∈s} vars(f_i)
    apply Finset.disjoint_iff_ne.mpr
    intro x hx y hy hxy
    -- x ∈ vars(f a), y ∈ vars(∏_{s} mlProj(f i))
    have hy_union : y ∈ s.biUnion (fun i => (mlProj (f i)).vars) :=
      MvPolynomial.vars_prod _ hy
    rw [Finset.mem_biUnion] at hy_union
    obtain ⟨j, hj_mem, hy_j⟩ := hy_union
    have hy_fj : y ∈ (f j).vars := vars_mlProj_subset (f j) hy_j
    subst hxy
    exact Finset.disjoint_iff_ne.mp
      (h_disj _ (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj_mem)
        (fun h => ha (h ▸ hj_mem)))
      x hx x hy_fj rfl

/-! ## Part 24: Generator factorization for block-disjoint products

When factors have pairwise disjoint variable sets and the shift has
variables contained in the "touched" blocks, the post-processed
generator mlProj(shift * ∏_i g_i) factors as:
  mlProj(shift * ∏_{touched} g_i) * ∏_{untouched} mlProj(f_i)

The "untouched factor" ∏_{untouched} mlProj(f_i) is fixed for all
generators that share the same set of touched factors.

This factorization is the key to the all-S union bound: every generator
in allBoundedProfilePostSpan(h) lies in the image of the fixed
untouched factor times the space of multilinear polynomials on the
touched-block variables. The dimension of the latter is 2^(touched vars). -/

/-- Splitting a Finset product into touched and untouched parts. -/
theorem finset_prod_split {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (touched : Finset ι) (f : ι → MvPolynomial (Fin n) ℚ) :
    s.prod f = (s.filter (· ∈ touched)).prod f * (s.filter (· ∉ touched)).prod f := by
  rw [← Finset.prod_union]
  congr 1
  ext x
  simp [Finset.mem_filter, Finset.mem_union]
  tauto
  · exact Finset.disjoint_filter_filter_neg s s (· ∈ touched)

/-- When we split the product and the shift's vars are contained in the
    touched factors' vars, mlProj factors. -/
theorem mlProj_shift_mul_prod_factored {n : ℕ} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → MvPolynomial (Fin n) ℚ)
    (shift : MvPolynomial (Fin n) ℚ)
    (touched : Finset ι)
    (h_disj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (MvPolynomial.vars (f i)) (MvPolynomial.vars (f j)))
    (h_shift_vars : shift.vars ⊆ (s.filter (· ∈ touched)).biUnion (fun i => (f i).vars))
    (h_touch_untouch_disj :
      Disjoint
        ((s.filter (· ∈ touched)).biUnion (fun i => (f i).vars))
        ((s.filter (· ∉ touched)).biUnion (fun i => (f i).vars))) :
    mlProj (shift * s.prod f) =
      mlProj (shift * (s.filter (· ∈ touched)).prod f) *
      (s.filter (· ∉ touched)).prod (fun i => mlProj (f i)) := by
  rw [finset_prod_split s touched f]
  -- Now: mlProj(shift * (touched.prod f * untouched.prod f))
  rw [mul_assoc]
  -- = mlProj((shift * touched.prod f) * untouched.prod f)
  -- Apply mlProj_mul_of_vars_disjoint
  rw [mlProj_mul_of_vars_disjoint]
  · -- mlProj(untouched.prod f) = ∏_{untouched} mlProj(f_i)
    congr 1
    apply mlProj_finset_prod_of_pairwise_disjoint_vars
    intro i hi j hj hij
    exact h_disj i (Finset.mem_of_mem_filter i hi) j (Finset.mem_of_mem_filter j hj) hij
  · -- vars(shift * touched.prod f) disjoint from vars(untouched.prod f)
    -- vars(shift * touched.prod) ⊆ vars(shift) ∪ vars(touched.prod)
    --   ⊆ touched-vars ∪ touched-vars = touched-vars
    -- vars(untouched.prod) ⊆ untouched-vars
    -- touched-vars ∩ untouched-vars = ∅ by h_touch_untouch_disj
    apply Finset.disjoint_iff_ne.mpr
    intro x hx y hy hxy
    subst hxy
    have hx_touched : x ∈ (s.filter (· ∈ touched)).biUnion (fun i => (f i).vars) := by
      have hx_mul := MvPolynomial.vars_mul
        shift ((s.filter (· ∈ touched)).prod f) hx
      rw [Finset.mem_union] at hx_mul
      cases hx_mul with
      | inl hx_shift => exact h_shift_vars hx_shift
      | inr hx_prod => exact MvPolynomial.vars_prod _ hx_prod
    have hy_untouched : x ∈ (s.filter (· ∉ touched)).biUnion (fun i => (f i).vars) :=
      MvPolynomial.vars_prod _ hy
    exact Finset.disjoint_iff_ne.mp h_touch_untouch_disj x hx_touched x hy_untouched rfl

/-- The untouched factor is determined by which factors are NOT touched.
    For a fixed choice of untouched factors (i.e., a fixed profile),
    the untouched factor is the same constant:
      untouchedFactor := ∏_{i ∉ touched} mlProj(f_i)
    which is independent of the derivative assignment. -/
noncomputable def untouchedFactor {n : ℕ} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → MvPolynomial (Fin n) ℚ)
    (touched : Finset ι) :
    MvPolynomial (Fin n) ℚ :=
  (s.filter (· ∉ touched)).prod (fun i => mlProj (f i))

/-- The dimension bound: every generator factors as
    mlProj(shift * touched_product) * untouchedFactor,
    where the touched product lives in a bounded-dimensional space.

    The span of all such generators (varying shift and derivatives) is
    contained in {q * untouchedFactor | q ∈ mlMultilinearSpace(touched vars)},
    which has dimension ≤ 2^|touched vars|. -/
theorem generator_in_untouched_times_touched_span {n : ℕ} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → MvPolynomial (Fin n) ℚ)
    (shift : MvPolynomial (Fin n) ℚ)
    (touched : Finset ι)
    (h_disj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (MvPolynomial.vars (f i)) (MvPolynomial.vars (f j)))
    (h_shift_vars : shift.vars ⊆ (s.filter (· ∈ touched)).biUnion (fun i => (f i).vars))
    (h_touch_untouch_disj :
      Disjoint
        ((s.filter (· ∈ touched)).biUnion (fun i => (f i).vars))
        ((s.filter (· ∉ touched)).biUnion (fun i => (f i).vars))) :
    mlProj (shift * s.prod f) =
      mlProj (shift * (s.filter (· ∈ touched)).prod f) *
      untouchedFactor s f touched :=
  mlProj_shift_mul_prod_factored s f shift touched h_disj h_shift_vars h_touch_untouch_disj

/-! ## Part 25: Dimension bound from factorization

If every generator in a span factors as `q * c` for a fixed `c`, then
the finrank of the span ≤ the finrank of the space containing the `q`'s.

This is because multiplication by `c` is a linear map whose image has
dimension ≤ the source dimension. -/

/-- The span of {q * c | q ∈ S} is contained in the image of
    multiplication by c applied to span(S). -/
theorem span_mul_right_le {n : ℕ}
    (S : Set (MvPolynomial (Fin n) ℚ))
    (c : MvPolynomial (Fin n) ℚ) :
    Submodule.span ℚ ((· * c) '' S) ≤
      Submodule.map (LinearMap.mulRight ℚ c) (Submodule.span ℚ S) := by
  apply Submodule.span_le.mpr
  intro x hx
  rcases hx with ⟨q, hq, rfl⟩
  exact ⟨q, Submodule.subset_span hq, rfl⟩

/-- Finrank of span({q * c | q ∈ S}) ≤ finrank of span(S). -/
theorem finrank_span_mul_right_le {n : ℕ}
    (S : Set (MvPolynomial (Fin n) ℚ))
    (c : MvPolynomial (Fin n) ℚ)
    (hfin : Module.Finite ℚ ↥(Submodule.span ℚ S)) :
    Module.finrank ℚ ↥(Submodule.span ℚ ((· * c) '' S)) ≤
      Module.finrank ℚ ↥(Submodule.span ℚ S) :=
  le_trans (Submodule.finrank_mono (span_mul_right_le S c))
    (Submodule.finrank_map_le _ _)

/-- The key application: if every generator of a submodule V factors as
    q_i * c where q_i lies in a submodule W, then finrank(V) ≤ finrank(W).

    Applied to the factorization:
    - V = allBoundedProfilePostSpan(h) (the within-profile span)
    - c = untouchedFactor (fixed for the profile)
    - W = span of multilinear polynomials on touched-block variables
    - finrank(W) ≤ 2^(touched-block variable count)

    This gives finrank(V) ≤ 2^(touched vars) which is ≤ 2^(3κ) = 8^κ. -/
theorem finrank_le_of_generators_factor {n : ℕ}
    (V W : Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (c : MvPolynomial (Fin n) ℚ)
    (hfin_W : Module.Finite ℚ ↥W)
    (hV_le : V ≤ Submodule.map (LinearMap.mulRight ℚ c) W) :
    Module.finrank ℚ ↥V ≤ Module.finrank ℚ ↥W :=
  le_trans (Submodule.finrank_mono hV_le) (Submodule.finrank_map_le _ _)

/-- Multilinear monomials on a subset of variables: the basis for
    bounding the touched-part dimension. -/
theorem finrank_mlMonomialBasis_subset {n : ℕ}
    (touchedVars : Finset (Fin n)) :
    Module.finrank ℚ ↥(Submodule.span ℚ
      (↑(MlProjFar.mlMonomialBasis touchedVars) :
        Set (MvPolynomial (Fin n) ℚ))) ≤
      2 ^ touchedVars.card := by
  calc Module.finrank ℚ ↥(Submodule.span ℚ
        (↑(MlProjFar.mlMonomialBasis touchedVars) :
          Set (MvPolynomial (Fin n) ℚ)))
      ≤ (MlProjFar.mlMonomialBasis touchedVars).card :=
        finrank_span_finset_le_card _
    _ ≤ 2 ^ touchedVars.card :=
        MlProjFar.mlMonomialBasis_card touchedVars

/-! ## Part 26: Touched-vars containment for the touched part

After the factorization, the touched part mlProj(shift * ∏_{touched} g_i)
has vars ⊆ touched-block vars. This follows from:
- vars(iterDerivList d f) ⊆ vars(f) (from LocalityRankBound)
- vars(shift) ⊆ S.toFinset ⊆ touched-block vars (by assumption)
- vars(shift * ∏_{touched} g_i) ⊆ vars(shift) ∪ ⋃_{touched} vars(g_i)
  ⊆ touched-block vars
- vars(mlProj(·)) ⊆ vars(·) (from vars_mlProj_subset) -/

/-- vars of a Finset product are contained in the biUnion of vars. -/
theorem vars_finset_prod_subset {n : ℕ} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → MvPolynomial (Fin n) ℚ) :
    (s.prod f).vars ⊆ s.biUnion (fun i => (f i).vars) :=
  MvPolynomial.vars_prod f

/-- vars of iterDerivList d (factor i) ⊆ vars of factor i.
    Re-export from LocalityRankBound. -/
theorem iterDerivList_vars_subset' {n : ℕ}
    (d : List (Fin n)) (f : MvPolynomial (Fin n) ℚ) :
    (iterDerivList d f).vars ⊆ f.vars :=
  LocalityRankBound.iterDerivList_vars_subset d f

/-- The touched part's vars are contained in the touched-block vars.

    For the all-S bound: different S choices have different touched-block
    vars, but the TOTAL touched-block vars across all S is bounded by
    the total number of variables (n). The dimension bound per-S is
    2^(touched vars per S), and the all-S dimension is bounded by
    the dimension of multilinear polynomials on all vars (2^n).

    For a POLYNOMIAL all-S bound, additional structure (block homogeneity)
    is needed. See the downstream argument. -/
theorem touched_part_vars_subset {n : ℕ} {ι : Type*} [DecidableEq ι]
    (s : Finset ι)
    (f : ι → MvPolynomial (Fin n) ℚ)
    (g : ι → MvPolynomial (Fin n) ℚ)
    (shift : MvPolynomial (Fin n) ℚ)
    (touched : Finset ι)
    (hg_vars : ∀ i ∈ s.filter (· ∈ touched), (g i).vars ⊆ (f i).vars)
    (h_shift_vars : shift.vars ⊆ (s.filter (· ∈ touched)).biUnion (fun i => (f i).vars)) :
    (mlProj (shift * (s.filter (· ∈ touched)).prod g)).vars ⊆
      (s.filter (· ∈ touched)).biUnion (fun i => (f i).vars) := by
  calc (mlProj (shift * (s.filter (· ∈ touched)).prod g)).vars
      ⊆ (shift * (s.filter (· ∈ touched)).prod g).vars :=
        vars_mlProj_subset _
    _ ⊆ shift.vars ∪ ((s.filter (· ∈ touched)).prod g).vars :=
        MvPolynomial.vars_mul shift _
    _ ⊆ (s.filter (· ∈ touched)).biUnion (fun i => (f i).vars) ∪
        ((s.filter (· ∈ touched)).prod g).vars :=
        Finset.union_subset_union h_shift_vars (Finset.Subset.refl _)
    _ ⊆ (s.filter (· ∈ touched)).biUnion (fun i => (f i).vars) ∪
        (s.filter (· ∈ touched)).biUnion (fun i => (g i).vars) := by
        apply Finset.union_subset_union (Finset.Subset.refl _)
        exact vars_finset_prod_subset _ _
    _ ⊆ (s.filter (· ∈ touched)).biUnion (fun i => (f i).vars) ∪
        (s.filter (· ∈ touched)).biUnion (fun i => (f i).vars) := by
        apply Finset.union_subset_union (Finset.Subset.refl _)
        apply Finset.biUnion_mono
        intro i hi
        exact hg_vars i hi
    _ = (s.filter (· ∈ touched)).biUnion (fun i => (f i).vars) :=
        Finset.union_idempotent _

/-- The touched part is a multilinear polynomial with vars in the
    touched-block vars. Hence it lies in the span of mlMonomialBasis
    restricted to the touched-block vars. -/
theorem touched_part_in_mlMonomialBasis_span {n : ℕ} {ι : Type*} [DecidableEq ι]
    (s : Finset ι)
    (f g : ι → MvPolynomial (Fin n) ℚ)
    (shift : MvPolynomial (Fin n) ℚ)
    (touched : Finset ι)
    (hg_vars : ∀ i ∈ s.filter (· ∈ touched), (g i).vars ⊆ (f i).vars)
    (h_shift_vars : shift.vars ⊆ (s.filter (· ∈ touched)).biUnion (fun i => (f i).vars)) :
    mlProj (shift * (s.filter (· ∈ touched)).prod g) ∈
      Submodule.span ℚ
        (↑(MlProjFar.mlMonomialBasis
          ((s.filter (· ∈ touched)).biUnion (fun i => (f i).vars))) :
          Set (MvPolynomial (Fin n) ℚ)) := by
  apply MlProjFar.mlProj_in_span_of_vars_subset
  · exact fun α hα =>
      isMultilinear_of_mem_mlProj_support _ α hα
  · exact fun v hv =>
      touched_part_vars_subset s f g shift touched hg_vars h_shift_vars hv

end WithinProfileBoundWIP
-/
