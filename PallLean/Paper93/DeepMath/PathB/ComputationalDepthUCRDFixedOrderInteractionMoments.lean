import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUCRDFanoutSemanticSpanAudit

/-!
# UCRD fixed-order contextual interaction moments

The semantic-span audit charged a node linearly for the number of contexts it
can serve.  A natural next invariant is higher contextual interaction: charge
quadratically for pair interactions, cubically for triples, and generally by a
fixed power.

For order parameter `p`, this file defines the `(p+1)`-st moments

```text
  contextualMoment_p = sum_g mult(g)^(p+1)
  semanticMoment_p   = sum_g depCard(g)^(p+1).
```

It proves, uniformly for every fixed `p`,

```text
  k*b <= contextualMoment_p <= semanticMoment_p
      <= n^(p+1) * |gates|.
```

Thus every fixed-order interaction moment is a valid fan-out-aware UCRD
currency, but every one loses the matching polynomial input-width factor.  At
pair order the global straddler has contextual moment `4`, semantic moment
`16`, and one gate; it saturates the `n^2 * size` ceiling.

## Honest scope

This closes the entire family of fixed-degree polynomial penalties as a
shortcut.  Raising the interaction order does not defeat a global node; it
raises both the charge and the universal width ceiling by the same power.  A
surviving invariant must therefore be non-fixed-order/non-polynomial, or must
prove a SAT-specific incompatibility preventing one global wire from realizing
all of the charged interactions.  Neither conclusion is claimed here.
-/

namespace PallLean.Paper93.DeepMath.PathB.UCRDFixedOrderInteractionMoments

open scoped BigOperators
open PallLean.Paper93.DeepMath.PathB.TheReasonShared
open PallLean.Paper93.DeepMath.PathB.EntanglementRuler
open PallLean.Paper93.DeepMath.PathB.UCRDFanoutSemanticSpanAudit

variable {k b n : ℕ}

/-- The `(p+1)`-st moment of contextual usefulness multiplicity. -/
def contextualInteractionMoment (C : EntangledTower k b n) (p : ℕ) : ℕ :=
  ∑ g ∈ C.gates, (mult (toShared C) g) ^ (p + 1)

/-- The `(p+1)`-st moment of genuine semantic dependency span. -/
def semanticInteractionMoment (C : EntangledTower k b n) (p : ℕ) : ℕ :=
  ∑ g ∈ C.gates, ((depSet C g).card) ^ (p + 1)

/-- Every natural number is at most any positive power of itself. -/
theorem self_le_pow_succ (a p : ℕ) : a ≤ a ^ (p + 1) := by
  by_cases ha : a = 0
  · simp [ha]
  have hapos : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha
  have hp : 1 ≤ a ^ p := Nat.one_le_pow p a hapos
  calc
    a = a * 1 := by simp
    _ ≤ a * a ^ p := Nat.mul_le_mul_left a hp
    _ = a ^ (p + 1) := by rw [pow_succ, Nat.mul_comm]

/-- Ordinary contextual-use mass is below every positive interaction moment. -/
theorem contextualUseMass_le_interactionMoment
    (C : EntangledTower k b n) (p : ℕ) :
    contextualUseMass C ≤ contextualInteractionMoment C p := by
  unfold contextualUseMass contextualInteractionMoment
  exact Finset.sum_le_sum (fun g _ ↦ self_le_pow_succ _ p)

/-- The semantic ruler lifts monotonically to every fixed interaction order. -/
theorem contextualMoment_le_semanticMoment
    (C : EntangledTower k b n) (p : ℕ) :
    contextualInteractionMoment C p ≤ semanticInteractionMoment C p := by
  unfold contextualInteractionMoment semanticInteractionMoment
  exact Finset.sum_le_sum
    (fun g _ ↦ Nat.pow_le_pow_left (mult_le_depCard C g) (p + 1))

/-- The semantic `(p+1)`-moment is at most width-to-that-power times DAG size. -/
theorem semanticMoment_le_widthPow_mul_size
    (C : EntangledTower k b n) (p : ℕ) :
    semanticInteractionMoment C p ≤ n ^ (p + 1) * C.gates.card := by
  unfold semanticInteractionMoment
  calc
    (∑ g ∈ C.gates, (depSet C g).card ^ (p + 1))
        ≤ C.gates.card • (n ^ (p + 1)) :=
      Finset.sum_le_card_nsmul C.gates
        (fun g ↦ (depSet C g).card ^ (p + 1)) (n ^ (p + 1))
        (fun g _ ↦ Nat.pow_le_pow_left (depSet_card_le_inputWidth C g) (p + 1))
    _ = n ^ (p + 1) * C.gates.card := by simp [Nat.mul_comm]

/-- **All fixed-order interaction moments, one theorem.**  Higher contextual
moments survive arbitrary fan-out, but their circuit-size cash-out loses the
same power of input width. -/
theorem fixedOrderInteraction_chain (C : EntangledTower k b n) (p : ℕ) :
    k * b ≤ contextualInteractionMoment C p ∧
    contextualInteractionMoment C p ≤ semanticInteractionMoment C p ∧
    semanticInteractionMoment C p ≤ n ^ (p + 1) * C.gates.card := by
  exact ⟨le_trans (demand_le_contextualUseMass C)
      (contextualUseMass_le_interactionMoment C p),
    contextualMoment_le_semanticMoment C p,
    semanticMoment_le_widthPow_mul_size C p⟩

/-- Pair-interaction order (`p=1`) on the global straddler: one gate serves two
contexts, so its contextual second moment is `2^2 = 4`. -/
theorem straddle_contextualPairMoment :
    contextualInteractionMoment straddleExample 1 = 4 := by decide

/-- The same global gate depends on four inputs, so its semantic second moment
is `4^2 = 16`. -/
theorem straddle_semanticPairMoment :
    semanticInteractionMoment straddleExample 1 = 16 := by decide

/-- Pairwise interaction still saturates the universal width-squared ceiling
with a one-gate DAG. -/
theorem straddle_pairMoment_ceiling_exact :
    semanticInteractionMoment straddleExample 1 =
      4 ^ 2 * straddleExample.gates.card := by
  rw [straddle_semanticPairMoment]
  decide

end PallLean.Paper93.DeepMath.PathB.UCRDFixedOrderInteractionMoments

#print axioms PallLean.Paper93.DeepMath.PathB.UCRDFixedOrderInteractionMoments.contextualMoment_le_semanticMoment
#print axioms PallLean.Paper93.DeepMath.PathB.UCRDFixedOrderInteractionMoments.semanticMoment_le_widthPow_mul_size
#print axioms PallLean.Paper93.DeepMath.PathB.UCRDFixedOrderInteractionMoments.fixedOrderInteraction_chain
#print axioms PallLean.Paper93.DeepMath.PathB.UCRDFixedOrderInteractionMoments.straddle_pairMoment_ceiling_exact
