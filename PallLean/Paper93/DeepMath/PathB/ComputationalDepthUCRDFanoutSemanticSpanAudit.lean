import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUCRDPointerFormulaNonAmortization
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPartitionCrossing

/-!
# UCRD fan-out audit: semantic span is the unconditional DAG currency

Formula topology forbids sharing outright.  A DAG does not, so counting gates
cannot support the same direct sum.  The correct fan-out-aware quantity is a
node's **semantic span**: how many private variables/contexts its wire function
actually depends on.

This file proves the complete unconditional chain for an `EntangledTower`:

```text
context demand k*b
  <= contextual-use mass (sum of witness multiplicities)
  <= semantic fan-out tax (sum of dependency-set sizes)
  <= n * number of gates.
```

The middle inequality is semantic, not syntactic: witnessing a private bubble
forces real dependence on a variable in that bubble, and disjoint bubbles give
distinct dependencies.  Thus arbitrary DAG fan-out is charged without any
`readK` assumption.

The final inequality is also the decisive audit.  A single global node may
span all `n` input coordinates, so semantic-span tax can be `n` times circuit
size.  The existing two-bubble straddler has one gate, is useful in both
contexts, and saturates the width-times-size ceiling.  Consequently semantic
span crosses the tree-to-DAG wall, but only yields
`k*b <= n*size`; it does not yet give a superpolynomial circuit lower bound.
Any separating continuation must prove that SAT's relevant shared nodes pay
more than ordinary input dependency, or that their useful spans cannot all be
simultaneously amortized.
-/

namespace PallLean.Paper93.DeepMath.PathB.UCRDFanoutSemanticSpanAudit

open scoped BigOperators
open PallLean.Paper93.DeepMath.PathB.TheReasonShared
open PallLean.Paper93.DeepMath.PathB.EntanglementRuler

variable {k b n : ℕ}

/-- Total contextual usefulness of all DAG nodes, counting a node once for
each private bubble in which it is a semantic witness. -/
def contextualUseMass (C : EntangledTower k b n) : ℕ :=
  ∑ g ∈ C.gates, mult (toShared C) g

/-- The fan-out-aware UCRD charge: sum of the genuine input-dependency spans
of the shared nodes. -/
def semanticFanoutTax (C : EntangledTower k b n) : ℕ :=
  ∑ g ∈ C.gates, (depSet C g).card

/-- Context demand is below contextual-use mass.  This is the incidence
direct sum before any sharing is discounted. -/
theorem demand_le_contextualUseMass (C : EntangledTower k b n) :
    k * b ≤ contextualUseMass C := by
  unfold contextualUseMass
  calc
    k * b ≤ ∑ i, ((toShared C).witness i).card :=
      kb_le_witness_sum (toShared C)
    _ = ∑ g ∈ C.gates, mult (toShared C) g := by
      simpa [toShared] using incidence_count (toShared C)

/-- Every useful context consumes a distinct unit of semantic span.  Unlike a
syntactic fan-out bound, this holds for arbitrary DAG sharing. -/
theorem contextualUseMass_le_semanticFanoutTax (C : EntangledTower k b n) :
    contextualUseMass C ≤ semanticFanoutTax C := by
  unfold contextualUseMass semanticFanoutTax
  exact Finset.sum_le_sum (fun g _ ↦ mult_le_depCard C g)

/-- **Fan-out-aware direct sum.**  No `readK`, locality, or tree premise is
needed: all contextual reconstruction demand is paid by semantic dependency
span. -/
theorem fanoutAware_direct_sum (C : EntangledTower k b n) :
    k * b ≤ semanticFanoutTax C :=
  le_trans (demand_le_contextualUseMass C)
    (contextualUseMass_le_semanticFanoutTax C)

/-- A node can depend on at most all `n` input coordinates. -/
theorem depSet_card_le_inputWidth (C : EntangledTower k b n) (g : ℕ) :
    (depSet C g).card ≤ n := by
  calc
    (depSet C g).card ≤ (Finset.univ : Finset (Fin n)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = n := by simp

/-- The semantic fan-out tax is at most input width times DAG size. -/
theorem semanticFanoutTax_le_width_mul_size (C : EntangledTower k b n) :
    semanticFanoutTax C ≤ n * C.gates.card := by
  unfold semanticFanoutTax
  calc
    (∑ g ∈ C.gates, (depSet C g).card) ≤ C.gates.card • n :=
      Finset.sum_le_card_nsmul C.gates (fun g ↦ (depSet C g).card) n
        (fun g _ ↦ depSet_card_le_inputWidth C g)
    _ = n * C.gates.card := by simp [Nat.mul_comm]

/-- **Exact unconditional DAG cash-out.**  Semantic span removes the external
reuse hypothesis, but the price is an input-width factor. -/
theorem dag_contextual_reconstruction_bound (C : EntangledTower k b n) :
    k * b ≤ n * C.gates.card :=
  le_trans (fanoutAware_direct_sum C)
    (semanticFanoutTax_le_width_mul_size C)

/-! ## The global straddler saturates the escape -/

/-- The one shared straddler is useful in both private contexts. -/
theorem straddle_contextualUseMass :
    contextualUseMass straddleExample = 2 := by decide

/-- Its one wire genuinely depends on all four input coordinates. -/
theorem straddle_semanticFanoutTax :
    semanticFanoutTax straddleExample = 4 := by decide

/-- The global node calibrates both sides: demand/use mass is `2`, while its
semantic span and the width-times-size ceiling are both `4`; circuit size is
still only `1`. -/
theorem straddle_chain_exact :
    2 * 1 = contextualUseMass straddleExample ∧
    contextualUseMass straddleExample = 2 ∧
    semanticFanoutTax straddleExample = 4 * straddleExample.gates.card := by
  constructor
  · simpa using straddle_contextualUseMass.symm
  constructor
  · exact straddle_contextualUseMass
  · rw [straddle_semanticFanoutTax]
    decide

end PallLean.Paper93.DeepMath.PathB.UCRDFanoutSemanticSpanAudit

#print axioms PallLean.Paper93.DeepMath.PathB.UCRDFanoutSemanticSpanAudit.fanoutAware_direct_sum
#print axioms PallLean.Paper93.DeepMath.PathB.UCRDFanoutSemanticSpanAudit.semanticFanoutTax_le_width_mul_size
#print axioms PallLean.Paper93.DeepMath.PathB.UCRDFanoutSemanticSpanAudit.dag_contextual_reconstruction_bound
#print axioms PallLean.Paper93.DeepMath.PathB.UCRDFanoutSemanticSpanAudit.straddle_chain_exact
