import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSemanticProfileQuotient
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ParityRankCardinality

/-!
# Semantic-profile to rank transfer for residual parity gates

After quotienting duplicate residual gates by `(free support, shifted target)`, distinct shifted targets still do not
create new linear observer dimensions.  A residual parity layer is an affine translate of its unshifted parity map.
This file proves that translation preserves the reachable-state cardinality, hence the residual observer has exactly
`2^rank` states.

This is the rigorous bridge from the semantic quotient to the existing rank route.  It also identifies the remaining
open step precisely: force the rank of the restricted support map to fall faster than the number of queried bits, or
factor the resulting affine state space without enumerating every branch.
-/

namespace PallLean.Paper93.DeepMath.PathB.SemanticProfileRankTransfer

open scoped Classical
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ACC0ParityConstraintRealization
open PallLean.Paper93.DeepMath.PathB.ACC0ParityRankCardinality

variable {n k : ℕ}

/-- A residual parity observer: the parity vector plus the residues contributed by already-fixed inputs. -/
def shiftedParityVector (S : Fin k → Finset (Fin n)) (shift : Fin k → ZMod 2)
    (x : Fin n → Bool) : Fin k → ZMod 2 :=
  parityVector S x + shift

/-- Translation by the shifted residue gives an equivalence between unshifted and residual reachable states. -/
noncomputable def shiftedRangeEquiv (S : Fin k → Finset (Fin n)) (shift : Fin k → ZMod 2) :
    Set.range (shiftedParityVector S shift) ≃ Set.range (parityVector S) where
  toFun y := by
    refine ⟨y.1 - shift, ?_⟩
    obtain ⟨x, hx⟩ := y.2
    refine ⟨x, ?_⟩
    rw [← hx]
    simp [shiftedParityVector]
  invFun y := by
    refine ⟨y.1 + shift, ?_⟩
    obtain ⟨x, hx⟩ := y.2
    refine ⟨x, ?_⟩
    rw [← hx]
    rfl
  left_inv y := by
    apply Subtype.ext
    simp
  right_inv y := by
    apply Subtype.ext
    simp

/-- **Affine shifts preserve the number of reachable parity observer states (proved).** -/
theorem shifted_reachable_card_eq (S : Fin k → Finset (Fin n)) (shift : Fin k → ZMod 2) :
    Nat.card (Set.range (shiftedParityVector S shift)) = Nat.card (Set.range (parityVector S)) :=
  Nat.card_congr (shiftedRangeEquiv S shift)

/-- **Semantic-profile/rank transfer (proved).**  Shifted residual targets do not increase observer complexity: the
reachable residual state space has exactly `2^rank` states. -/
theorem shifted_reachable_card (S : Fin k → Finset (Fin n)) (shift : Fin k → ZMod 2) :
    Nat.card (Set.range (shiftedParityVector S shift)) =
      2 ^ Module.finrank (ZMod 2) (LinearMap.range (parityLinMap S)) := by
  rw [shifted_reachable_card_eq]
  exact parity_reachable_card S

/-- If the linear rank is at most `r`, the residual semantic observer has at most `2^r` reachable states. -/
theorem shifted_reachable_card_le_of_rank_le (S : Fin k → Finset (Fin n)) (shift : Fin k → ZMod 2)
    (r : ℕ) (hrank : Module.finrank (ZMod 2) (LinearMap.range (parityLinMap S)) ≤ r) :
    Nat.card (Set.range (shiftedParityVector S shift)) ≤ 2 ^ r := by
  rw [shifted_reachable_card S shift]
  exact Nat.pow_le_pow_right (by norm_num) hrank

end PallLean.Paper93.DeepMath.PathB.SemanticProfileRankTransfer

#print axioms PallLean.Paper93.DeepMath.PathB.SemanticProfileRankTransfer.shifted_reachable_card_eq
#print axioms PallLean.Paper93.DeepMath.PathB.SemanticProfileRankTransfer.shifted_reachable_card
#print axioms PallLean.Paper93.DeepMath.PathB.SemanticProfileRankTransfer.shifted_reachable_card_le_of_rank_le
