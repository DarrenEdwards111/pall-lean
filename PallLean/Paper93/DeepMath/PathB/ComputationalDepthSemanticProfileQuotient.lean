import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSemanticOverlapTransferNoGo

/-!
# Semantic profile quotient for residual fixed-modulus gates

The duplicate-parity no-go shows that syntactic overlap must be measured only after residual gates are quotiented by
their semantics.  For a fixed modulus `m`, the natural residual profile is

> `(free support, shifted residue target) : Finset Var × Fin m`.

This file proves the exact finite counting laws for that quotient.

* duplicate gates disappear because profiles are stored in a `Finset` image;
* the number of residual profiles is at most `m` times the number of distinct residual supports;
* for parity (`m=2`), each residual support contributes at most two semantic profiles;
* quotient-level incidence is bounded by `profile-count · #live`, so duplicate multiplicity no longer creates fake
  overlap surplus;
* consequently, a large post-quotient profile family forces many distinct residual supports.  The next compression
  question is therefore no longer gate deduplication but whether those supports have low linear rank / few observer
  cells after restriction.

The file deliberately does not claim that the profile pair is a complete semantic invariant for arbitrary mixed
circuits.  It is the exact invariant for a single fixed-modulus count-residue gate after its fixed inputs have been
absorbed into the shifted target.
-/

namespace PallLean.Paper93.DeepMath.PathB.SemanticProfileQuotient

open Finset

variable {Gate Var : Type} [DecidableEq Gate] [DecidableEq Var]

/-- Residual fixed-modulus profile: free support plus shifted target residue. -/
abbrev ResidualProfile (Var : Type) (m : ℕ) := Finset Var × Fin m

/-- Distinct residual supports represented by the gate family. -/
def residualSupportSet (gates : Finset Gate) (freeSupport : Gate → Finset Var) : Finset (Finset Var) :=
  gates.image freeSupport

/-- Semantic quotient of the gate family by residual support and shifted target. -/
def residualProfileSet {m : ℕ} (gates : Finset Gate) (freeSupport : Gate → Finset Var)
    (shiftedTarget : Gate → Fin m) : Finset (ResidualProfile Var m) :=
  gates.image (fun g => (freeSupport g, shiftedTarget g))

/-- Every realized profile lies in `distinct-supports × all-residues`. -/
theorem residualProfileSet_subset_product {m : ℕ} (gates : Finset Gate)
    (freeSupport : Gate → Finset Var) (shiftedTarget : Gate → Fin m) :
    residualProfileSet gates freeSupport shiftedTarget
      ⊆ (residualSupportSet gates freeSupport).product (Finset.univ : Finset (Fin m)) := by
  intro p hp
  obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hp
  apply Finset.mem_product.mpr
  constructor
  · exact Finset.mem_image.mpr ⟨g, hg, rfl⟩
  · exact Finset.mem_univ _

/-- **Semantic profile bound (proved).**  Fixed modulus permits at most `m` shifted targets per distinct residual
support. -/
theorem residualProfileSet_card_le {m : ℕ} (gates : Finset Gate)
    (freeSupport : Gate → Finset Var) (shiftedTarget : Gate → Fin m) :
    (residualProfileSet gates freeSupport shiftedTarget).card
      ≤ m * (residualSupportSet gates freeSupport).card := by
  calc
    (residualProfileSet gates freeSupport shiftedTarget).card
        ≤ ((residualSupportSet gates freeSupport).product
            (Finset.univ : Finset (Fin m))).card :=
          card_le_card (residualProfileSet_subset_product gates freeSupport shiftedTarget)
    _ = m * (residualSupportSet gates freeSupport).card := by
          simp [Nat.mul_comm]

/-- Parity has at most two shifted-target profiles per distinct residual support. -/
theorem parity_profileSet_card_le (gates : Finset Gate) (freeSupport : Gate → Finset Var)
    (shiftedTarget : Gate → Fin 2) :
    (residualProfileSet gates freeSupport shiftedTarget).card
      ≤ 2 * (residualSupportSet gates freeSupport).card :=
  residualProfileSet_card_le gates freeSupport shiftedTarget

/-- Incidence measured after semantic quotienting: each residual profile is charged once. -/
def quotientIncidence {m : ℕ} (gates : Finset Gate) (freeSupport : Gate → Finset Var)
    (shiftedTarget : Gate → Fin m) (live : Finset Var) : ℕ :=
  ∑ p ∈ residualProfileSet gates freeSupport shiftedTarget, (p.1 ∩ live).card

/-- Quotient incidence is bounded by profile count times the live-variable budget. -/
theorem quotientIncidence_le_profiles_mul_live {m : ℕ} (gates : Finset Gate)
    (freeSupport : Gate → Finset Var) (shiftedTarget : Gate → Fin m) (live : Finset Var) :
    quotientIncidence gates freeSupport shiftedTarget live
      ≤ (residualProfileSet gates freeSupport shiftedTarget).card * live.card := by
  unfold quotientIncidence
  calc
    (∑ p ∈ residualProfileSet gates freeSupport shiftedTarget, (p.1 ∩ live).card)
        ≤ ∑ _p ∈ residualProfileSet gates freeSupport shiftedTarget, live.card := by
          apply sum_le_sum
          intro p hp
          exact card_le_card inter_subset_right
    _ = (residualProfileSet gates freeSupport shiftedTarget).card * live.card := by simp

/-- Combining the two bounds removes arbitrary duplicate multiplicity: quotient incidence is controlled by modulus,
distinct supports, and live variables only. -/
theorem quotientIncidence_le_mod_support_live {m : ℕ} (gates : Finset Gate)
    (freeSupport : Gate → Finset Var) (shiftedTarget : Gate → Fin m) (live : Finset Var) :
    quotientIncidence gates freeSupport shiftedTarget live
      ≤ (m * (residualSupportSet gates freeSupport).card) * live.card := by
  exact le_trans (quotientIncidence_le_profiles_mul_live gates freeSupport shiftedTarget live)
    (Nat.mul_le_mul_right live.card (residualProfileSet_card_le gates freeSupport shiftedTarget))

/-- A large semantic quotient forces many distinct supports; duplicate-target variation alone cannot explain it. -/
theorem support_count_large_of_profile_count_large {m r : ℕ} (gates : Finset Gate)
    (freeSupport : Gate → Finset Var) (shiftedTarget : Gate → Fin m)
    (hlarge : m * r < (residualProfileSet gates freeSupport shiftedTarget).card) :
    r < (residualSupportSet gates freeSupport).card := by
  have hbound := residualProfileSet_card_le gates freeSupport shiftedTarget
  nlinarith

end PallLean.Paper93.DeepMath.PathB.SemanticProfileQuotient

#print axioms PallLean.Paper93.DeepMath.PathB.SemanticProfileQuotient.residualProfileSet_card_le
#print axioms PallLean.Paper93.DeepMath.PathB.SemanticProfileQuotient.quotientIncidence_le_mod_support_live
#print axioms PallLean.Paper93.DeepMath.PathB.SemanticProfileQuotient.support_count_large_of_profile_count_large
