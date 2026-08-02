import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUCRDFixedOrderInteractionMoments

/-!
# UCRD node-local potential wall

Fixed powers are not special.  Suppose a proposed fan-out invariant charges a
shared DAG node only through a monotone scalar potential `Phi(span)`, where
`span` is the number of contexts/variables the node semantically serves.
Allow `Phi` to be arbitrary: polynomial, exponential, input-dependent, or a
non-fixed interaction order.

This file proves the universal node-local wall:

```text
  k*b <= sum_g Phi(mult(g))
      <= sum_g Phi(depCard(g))
      <= Phi(n) * |gates|,
```

provided only that `Phi` is monotone and dominates the identity.  The first
two inequalities make it a sound contextual-reconstruction currency; the last
one shows why it cannot by itself lower-bound ordinary DAG size.  A global node
may sit at `span = n` and consume the entire allowance `Phi(n)` once.

The exponential specialization `Phi(s)=2^s` is proved explicitly.  The
one-gate straddler has semantic charge `2^4=16` and exactly saturates
`Phi(n)*size`.  Thus moving from fixed polynomial moments to non-polynomial
local penalties does not solve mass production.

## Honest scope

This is a general no-go theorem for **node-local span potentials**, not for all
possible invariants.  A surviving UCRD invariant must depend on incompatibility
between several nodes/contexts, pathwise recomputation, or a global obstruction
that is not a sum of independent functions of each node's span.
-/

namespace PallLean.Paper93.DeepMath.PathB.UCRDNodeLocalPotentialWall

open scoped BigOperators
open PallLean.Paper93.DeepMath.PathB.TheReasonShared
open PallLean.Paper93.DeepMath.PathB.EntanglementRuler
open PallLean.Paper93.DeepMath.PathB.UCRDFanoutSemanticSpanAudit

variable {k b n : ℕ}

/-- A node-local contextual potential, applied to witness multiplicity. -/
def contextualPotential (C : EntangledTower k b n) (Phi : ℕ → ℕ) : ℕ :=
  ∑ g ∈ C.gates, Phi (mult (toShared C) g)

/-- The matching semantic potential, applied to genuine dependency span. -/
def semanticPotential (C : EntangledTower k b n) (Phi : ℕ → ℕ) : ℕ :=
  ∑ g ∈ C.gates, Phi (depSet C g).card

/-- If the potential dominates identity, it dominates ordinary contextual-use
mass. -/
theorem contextualUseMass_le_potential
    (C : EntangledTower k b n) (Phi : ℕ → ℕ)
    (hdom : ∀ s, s ≤ Phi s) :
    contextualUseMass C ≤ contextualPotential C Phi := by
  unfold contextualUseMass contextualPotential
  exact Finset.sum_le_sum (fun g _ ↦ hdom _)

/-- Monotonicity transports the semantic ruler through an arbitrary node-local
potential. -/
theorem contextualPotential_le_semanticPotential
    (C : EntangledTower k b n) (Phi : ℕ → ℕ)
    (hmono : Monotone Phi) :
    contextualPotential C Phi ≤ semanticPotential C Phi := by
  unfold contextualPotential semanticPotential
  exact Finset.sum_le_sum (fun g _ ↦ hmono (mult_le_depCard C g))

/-- Universal node-local ceiling: every node has span at most input width, so
every node costs at most `Phi(n)`. -/
theorem semanticPotential_le_nodeCeiling
    (C : EntangledTower k b n) (Phi : ℕ → ℕ)
    (hmono : Monotone Phi) :
    semanticPotential C Phi ≤ Phi n * C.gates.card := by
  unfold semanticPotential
  calc
    (∑ g ∈ C.gates, Phi (depSet C g).card) ≤ C.gates.card • Phi n :=
      Finset.sum_le_card_nsmul C.gates (fun g ↦ Phi (depSet C g).card) (Phi n)
        (fun g _ ↦ hmono (depSet_card_le_inputWidth C g))
    _ = Phi n * C.gates.card := by simp [Nat.mul_comm]

/-- **The node-local potential wall.**  Every monotone identity-dominating
charge is a sound UCRD currency, but its DAG-size bridge loses exactly the
single-global-node allowance `Phi(n)`. -/
theorem nodeLocalPotential_chain
    (C : EntangledTower k b n) (Phi : ℕ → ℕ)
    (hmono : Monotone Phi) (hdom : ∀ s, s ≤ Phi s) :
    k * b ≤ contextualPotential C Phi ∧
    contextualPotential C Phi ≤ semanticPotential C Phi ∧
    semanticPotential C Phi ≤ Phi n * C.gates.card := by
  exact ⟨le_trans (demand_le_contextualUseMass C)
      (contextualUseMass_le_potential C Phi hdom),
    contextualPotential_le_semanticPotential C Phi hmono,
    semanticPotential_le_nodeCeiling C Phi hmono⟩

/-! ## Exponential/non-polynomial calibration -/

/-- Exponential semantic-span charge. -/
def exponentialPotential (s : ℕ) : ℕ := 2 ^ s

theorem exponentialPotential_monotone : Monotone exponentialPotential := by
  intro a c hac
  exact Nat.pow_le_pow_right (by norm_num) hac

theorem identity_le_exponentialPotential (s : ℕ) :
    s ≤ exponentialPotential s :=
  Nat.lt_two_pow_self.le

/-- Even exponential local interaction has the same node-local wall. -/
theorem exponentialPotential_chain (C : EntangledTower k b n) :
    k * b ≤ contextualPotential C exponentialPotential ∧
    contextualPotential C exponentialPotential ≤
      semanticPotential C exponentialPotential ∧
    semanticPotential C exponentialPotential ≤ 2 ^ n * C.gates.card := by
  simpa [exponentialPotential] using
    nodeLocalPotential_chain C exponentialPotential
      exponentialPotential_monotone identity_le_exponentialPotential

/-- The global straddler's exponential semantic charge is `2^4=16`. -/
theorem straddle_exponentialSemanticPotential :
    semanticPotential straddleExample exponentialPotential = 16 := by decide

/-- One global node exactly saturates the exponential node-local ceiling. -/
theorem straddle_exponentialCeiling_exact :
    semanticPotential straddleExample exponentialPotential =
      exponentialPotential 4 * straddleExample.gates.card := by
  rw [straddle_exponentialSemanticPotential]
  decide

end PallLean.Paper93.DeepMath.PathB.UCRDNodeLocalPotentialWall

#print axioms PallLean.Paper93.DeepMath.PathB.UCRDNodeLocalPotentialWall.contextualPotential_le_semanticPotential
#print axioms PallLean.Paper93.DeepMath.PathB.UCRDNodeLocalPotentialWall.semanticPotential_le_nodeCeiling
#print axioms PallLean.Paper93.DeepMath.PathB.UCRDNodeLocalPotentialWall.nodeLocalPotential_chain
#print axioms PallLean.Paper93.DeepMath.PathB.UCRDNodeLocalPotentialWall.straddle_exponentialCeiling_exact
