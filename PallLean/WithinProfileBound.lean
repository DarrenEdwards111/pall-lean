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
import Mathlib.Tactic

namespace WithinProfileBound

open SPDP MultilinearSPDP MvPolynomial TuringMachine PaperFaithfulSeparation
open SymmetricPowerBound

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

/-! ## Part 6: Alternative reduction via the product_leibniz_profile_cover route

Rather than fighting the infinite-to-finite sup issue, we note that
the existing `product_leibniz_profile_cover` theorem (proved from the axiom)
already provides the right finite cover. The goal of this file is to show
the ARITHMETIC bounds that reduce the axiom to a clean within-profile claim.

The key result: given ANY finite family of ≤ (κ+1)^4 subspaces, each with
finrank ≤ (κ+1)^8, covering the SPDP subspace, the rank bound follows.
This is already proved as `spdp_rank_of_finite_profile_cover_and_bound`. -/

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

end WithinProfileBound
