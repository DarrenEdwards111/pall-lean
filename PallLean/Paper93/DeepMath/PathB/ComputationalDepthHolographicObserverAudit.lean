import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDimensionUpperBound
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDimensionFullRank
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPRamanujanQueryMERACompiler

/-!
# Holographic observer audit: cuts, boundary rank, and the compiler frontier

This file tests the proposed holographic-observer route in the smallest rigorous model that captures its
three relevant ingredients:

* a bulk computation is observed through a boundary cut `S`;
* the information crossing that cut is measured by the span of its residual boundary behaviours;
* changing from circuits/machines to "holographic encodings" is represented by a semantics-preserving
  wrapper around the underlying representation.

The result is deliberately an adversarial audit, not a separation claim.

1. **Cheap-cut collapse.**  If every boundary cut is admissible, the empty cut has residual rank at most
   one for every function.
2. **Easy-function false positive.**  Equality has full exponential residual rank on its intended balanced
   boundary block, despite being easy to compute.
3. **Encoding minimisation is unchanged by relabelling.**  A faithful holographic wrapper has a bounded-cost
   realisation exactly when the underlying representation model does.  Consequently, minimising over all
   equivalent holographic encodings does not discharge the machine-completeness quantifier; it merely restates
   minimum representation complexity.

The repository's existing bounded-MERA model supplies a genuine restricted positive result.  The final theorem
re-exports its exact frontier: expander routing alone cannot manufacture exact bounded-MERA transcripts for a
SAT decider.  The missing machine-to-MERA compiler is the load-bearing unproved content.

Nothing here proves a new circuit lower bound or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.HolographicObserverAudit

open PallLean.Paper93.DeepMath.PathB.DimensionRestrictionObserver
open PallLean.Paper93.DeepMath.PathB.DimensionUpperBound
open PallLean.Paper93.DeepMath.PathB.DimensionFullRank

/-! ## Test 1: unrestricted holographic cuts collapse -/

/-- The residual-span boundary charge seen through a proposed holographic boundary cut. -/
noncomputable def cutBoundary {K : Type*} [Field K] {n : Nat}
    (S : Finset (Fin n)) (f : (Fin n → Bool) → K) : Nat :=
  dimResiduals S f

/-- **Cheap-cut no-go.**  If all cuts are admissible, every function has a boundary cut of charge at most one.
The witness is the empty boundary. -/
theorem exists_cheap_holographic_cut {K : Type*} [Field K] {n : Nat}
    (f : (Fin n → Bool) → K) :
    ∃ S : Finset (Fin n), cutBoundary S f ≤ 1 := by
  simpa [cutBoundary] using unrestricted_min_trivial f

/-! ## Test 2: a large structured boundary does not imply hardness -/

/-- **Easy-function false-positive calibration.**  Equality has `2^k` independent behaviours across its
balanced boundary block.  Thus a large maximum or selected-cut boundary is not, by itself, a computation-time
lower bound. -/
theorem equality_has_exponential_structured_boundary {K : Type*} [Field K] {k : Nat} :
    2 ^ k ≤ Module.finrank K
      (Submodule.span K (Set.range (DimensionFullRank.resVec K k))) :=
  eqFun_dim_ge

/-! ## Test 3: a faithful holographic wrapper does not remove minimisation -/

/-- An arbitrary representation model: circuits, machines, tensor networks, or another finite encoding. -/
structure RepresentationModel (Input Output : Type*) where
  Rep : Type*
  eval : Rep → Input → Output
  cost : Rep → Nat

/-- A semantics-preserving holographic presentation of an underlying representation.

No extra computational power is inserted: `bulk` is the represented computation, while `projection` records
boundary metadata.  The cost remains the genuine bulk representation cost. -/
structure HolographicEncoding {Input Output : Type*}
    (R : RepresentationModel Input Output) where
  bulk : R.Rep
  boundaryMetadata : Nat

namespace HolographicEncoding

variable {Input Output : Type*} {R : RepresentationModel Input Output}

def eval (H : HolographicEncoding R) : Input → Output := R.eval H.bulk

def cost (H : HolographicEncoding R) : Nat := R.cost H.bulk

/-- Every underlying representation has a faithful holographic presentation (with trivial boundary metadata). -/
def ofRep (r : R.Rep) : HolographicEncoding R where
  bulk := r
  boundaryMetadata := 0

@[simp] theorem eval_ofRep (r : R.Rep) : eval (ofRep r) = R.eval r := rfl
@[simp] theorem cost_ofRep (r : R.Rep) : cost (ofRep r) = R.cost r := rfl

end HolographicEncoding

/-- A function has an implementation of cost at most `B` in the underlying model. -/
def HasRepresentationAtMost {Input Output : Type*}
    (R : RepresentationModel Input Output) (f : Input → Output) (B : Nat) : Prop :=
  ∃ r : R.Rep, R.eval r = f ∧ R.cost r ≤ B

/-- The same bounded-cost question after adding a faithful holographic presentation. -/
def HasHolographicEncodingAtMost {Input Output : Type*}
    (R : RepresentationModel Input Output) (f : Input → Output) (B : Nat) : Prop :=
  ∃ H : HolographicEncoding R,
    HolographicEncoding.eval H = f ∧ HolographicEncoding.cost H ≤ B

/-- **Relabelling/circularity audit.**  Minimising over faithful holographic encodings is exactly the original
minimum-representation problem.  A holographic presentation can expose useful geometry, but the wrapper alone
cannot prove the required lower bound. -/
theorem holographic_minimisation_iff_representation_minimisation
    {Input Output : Type*} (R : RepresentationModel Input Output)
    (f : Input → Output) (B : Nat) :
    HasHolographicEncodingAtMost R f B ↔ HasRepresentationAtMost R f B := by
  constructor
  · rintro ⟨H, heval, hcost⟩
    exact ⟨H.bulk, heval, hcost⟩
  · rintro ⟨r, heval, hcost⟩
    exact ⟨HolographicEncoding.ofRep r, heval, hcost⟩

/-! ## Existing bounded-MERA result and the honest frontier -/

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPNFrameDynamicMERAHolonomy
open PallLean.Paper93.DeepMath.PathB.PvsNPRamanujanQueryMERACompiler

/-- Expander geometry supplies real routing combinatorics, but it cannot supply exact bounded-MERA transcripts
for an arbitrary SAT decider.  This is the precise machine-completeness obstruction in the existing holographic
model. -/
theorem expander_geometry_does_not_supply_the_compiler
    {U : MachineModel} {D : DecisionMachine U} (M : MERAFamily)
    (layouts : ∀ n, RamanujanExpanderQueryLayout n)
    (hD : DecidesSAT U D) :
    ¬ (∀ n, Nonempty (RamanujanMERAQueryTranscript (n := n) D M)) :=
  expander_layout_does_not_supply_MERA_transcripts M layouts hD

end PallLean.Paper93.DeepMath.PathB.HolographicObserverAudit

#print axioms PallLean.Paper93.DeepMath.PathB.HolographicObserverAudit.exists_cheap_holographic_cut
#print axioms PallLean.Paper93.DeepMath.PathB.HolographicObserverAudit.equality_has_exponential_structured_boundary
#print axioms PallLean.Paper93.DeepMath.PathB.HolographicObserverAudit.holographic_minimisation_iff_representation_minimisation
#print axioms PallLean.Paper93.DeepMath.PathB.HolographicObserverAudit.expander_geometry_does_not_supply_the_compiler
