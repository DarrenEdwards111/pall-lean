/-
  WithinProfileBound.lean — Finite enumeration of bounded profiles

  Proves that the set of profiles with each component ≤ κ is finite
  with cardinality ≤ (κ+1)^4, providing the profile COUNT ingredient
  for HasFiniteProfileCover.
-/
import PallLean.SymmetricPowerBound
import Mathlib.Tactic

namespace WithinProfileBound

open SPDP MultilinearSPDP MvPolynomial TuringMachine PaperFaithfulSeparation
open SymmetricPowerBound

/-! ## Finite enumeration of bounded profiles

A bounded profile h : ConstraintType → ℕ has each component h(τ) ≤ κ.
Since ConstraintType has 4 elements, the number of bounded profiles is
at most (κ+1)^4, matching profileCount κ. -/

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

/-! ## Admissible profiles are bounded -/

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

/-! ## Derivative-count profiles from Leibniz terms are admissible

For actual Leibniz terms from the expansion of iterDerivList S (∏ factors),
each derivative in S is assigned to exactly one factor. The total number of
derivative assignments equals |S|. So the profile mass = |S|.

For SPDP generators with |S| = κ, the profile is admissible (mass = κ ≤ κ). -/

/-- The derivative-count profile of a distribution with total length ≤ κ is admissible.
    Already proved in SymmetricPowerBound.lean as derivCountProfile_admissible_of_total_le. -/
theorem derivCountProfile_bounded_of_total_le {L n κ : ℕ}
    (constraintType : Fin L → ConstraintType)
    (d : Fin L → List (Fin n))
    (htotal : ∑ i : Fin L, (d i).length ≤ κ) :
    ∀ τ, (derivCountProfile constraintType d) τ ≤ κ :=
  admissible_implies_bounded (derivCountProfile_admissible_of_total_le constraintType d htotal)

/-! ## Within-profile template count (arithmetic)

For a fixed profile h with 4 types and local interface dimension 3,
the within-profile template count is:
  ∏_τ C(h(τ)+2, 2) ≤ ∏_τ (h(τ)+1)^2 ≤ (κ+1)^8

Already proved as profileDimBound_le_withinProfileBound. We re-export it here
for reference. -/

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

/-! ## Packaging: bounded profile family with count bound

We package the bounded profiles into a Fin-indexed family suitable for
use in HasFiniteProfileCover. -/

/-- There exists a surjection from Fin ((κ+1)^4) onto bounded profiles
    (or rather, an indexed family covering all bounded profiles). -/
theorem exists_fin_surjection_boundedProfile (κ : ℕ) :
    ∃ (P : ℕ) (f : Fin P → BoundedProfile κ),
      P ≤ profileCount κ ∧ Function.Surjective f := by
  refine ⟨Fintype.card (BoundedProfile κ),
    fun i => (Fintype.equivFin (BoundedProfile κ)).symm i,
    boundedProfile_card_le_profileCount κ,
    (Fintype.equivFin (BoundedProfile κ)).symm.surjective⟩

/-- The allDerivCountProfilePostSpan indexed by bounded profiles covers
    the entire allDerivCountProfilePostSpan indexed by ALL profiles,
    provided we restrict to admissible profiles (which are bounded).

    Specifically: for any admissible profile h, there exists a bounded profile bp
    with bp.toHistogram = h. -/
theorem admissible_profile_in_bounded_range {κ : ℕ} {h : ProfileHistogram}
    (hadm : ProfileAdmissible κ h) :
    ∃ bp : BoundedProfile κ, bp.toHistogram = h :=
  ⟨admissibleToBounded hadm, rfl⟩

end WithinProfileBound
