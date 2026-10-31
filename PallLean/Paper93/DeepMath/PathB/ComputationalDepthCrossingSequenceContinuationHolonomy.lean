import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTraceDynamicsContinuationBridge
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingSequenceBridge

/-!
# Crossing sequences carry continuation-complete holonomy only at their real capacity

The trace-dynamics connector makes the semantic obligation precise: a boundary
signature must be prefix-stable and reconstruct the answer under every future
suffix.  The crossing-sequence bridge makes the physical capacity precise: a
width-`w` sequence over `q` control states has only `q^w` possible values.

This file composes those two independently proved statements.  If a genuine
continuation-complete trace signature factors through a crossing-sequence-shaped
view, and `2^r` residual outcomes are semantically separated by future suffixes,
then the crossing sequence must satisfy

```text
2^r <= q^w.
```

This is the non-circular capacity bridge for the restricted crossing-sequence
representation.  The remaining unrestricted theorem is deliberately not assumed:
one must still derive this representation from a hypothetical polynomial SAT
solver's physical crossings and prove that it exposes the hard residuals through
bounded width.  General machines can move information through other cuts or
reorganise it, so polynomial time alone does not provide that factorisation.
-/

namespace PallLean.Paper93.DeepMath.PathB.CrossingSequenceContinuationHolonomy

open PvsNPRunIndexedFaithfulTPhi
open PvsNPRunIndexedFaithfulTPhi.ActualDecisionRun
open ContinuationCompleteDynamicHolonomy
open ContinuationCompleteDynamicHolonomy.ContinuationCompleteBank
open TraceDynamicsContinuationBridge
open TraceDynamicsContinuationBridge.TraceContinuationFactorization
open BoundaryDebt
open CrossingSequenceBridge

variable {C Suf State : Type*}

/-- A continuation-complete actual trace signature represented by a width-`w`
crossing-sequence word over `q` control states.  The structure records the exact
factorisation obligation; it does not claim that every machine supplies one. -/
structure CrossingSequenceTraceFactorization
    [Inhabited Suf]
    (R : ActualDecisionRun (C × Suf) State) (g w q : Nat) where
  trace : TraceContinuationFactorization R g
  crossingView : C → (Fin w → Fin q)
  crossingDeterminesSignature :
    ∀ x y, crossingView x = crossingView y →
      trace.toContinuationCompleteBank.prefixSignature x =
        trace.toContinuationCompleteBank.prefixSignature y

namespace CrossingSequenceTraceFactorization

/-- If different residual labels can be distinguished by some future suffix,
then equal physical crossing histories force equal residual labels. -/
theorem crossingView_faithful [Inhabited Suf]
    {R : ActualDecisionRun (C × Suf) State} {g w q r : Nat}
    (F : CrossingSequenceTraceFactorization R g w q)
    (residual : C → Fin (2 ^ r))
    (hsemantic : ∀ x y, residual x ≠ residual y →
      ∃ s, R.finalAnswer (x, s) ≠ R.finalAnswer (y, s)) :
    ∀ x y, F.crossingView x = F.crossingView y → residual x = residual y := by
  intro x y hview
  by_contra hres
  obtain ⟨s, hs⟩ := hsemantic x y hres
  have hsig := F.crossingDeterminesSignature x y hview
  exact hs
    (F.trace.toContinuationCompleteBank.signatureFaithful x y hsig s)

/-- **Restricted adaptive-rereading capacity theorem.**  A surjective family of
`2^r` future-distinguishable residuals cannot factor through fewer than `2^r`
crossing histories.  Since a width-`w`, `q`-state history has cardinality `q^w`,
we obtain `2^r <= q^w`. -/
theorem residual_capacity_le_crossing_capacity
    [Fintype C] [DecidableEq C] [Inhabited Suf]
    {R : ActualDecisionRun (C × Suf) State} {g w q r : Nat}
    (F : CrossingSequenceTraceFactorization R g w q)
    (residual : C → Fin (2 ^ r))
    (hsurj : Function.Surjective residual)
    (hsemantic : ∀ x y, residual x ≠ residual y →
      ∃ s, R.finalAnswer (x, s) ≠ R.finalAnswer (y, s)) :
    2 ^ r ≤ q ^ w := by
  classical
  have hfaithful := F.crossingView_faithful residual hsemantic
  have hzero :
      debtCount (residualFooling residual) F.crossingView = 0 := by
    apply correct_view_zero_debt
    intro p hp
    rw [residualFooling, Finset.mem_filter] at hp
    intro hview
    exact hp.2 (hfaithful p.1 p.2 hview)
  have hdebt := crossingSequence_forces_debt residual hsurj F.crossingView
  rw [hzero] at hdebt
  omega

/-- Contrapositive form: below the residual capacity, no such physical
continuation-complete crossing factorisation exists. -/
theorem no_factorization_below_residual_capacity
    [Fintype C] [DecidableEq C] [Inhabited Suf]
    {R : ActualDecisionRun (C × Suf) State} {g w q r : Nat}
    (residual : C → Fin (2 ^ r))
    (hsurj : Function.Surjective residual)
    (hsemantic : ∀ x y, residual x ≠ residual y →
      ∃ s, R.finalAnswer (x, s) ≠ R.finalAnswer (y, s))
    (hgap : q ^ w < 2 ^ r) :
    ¬ Nonempty (CrossingSequenceTraceFactorization R g w q) := by
  rintro ⟨F⟩
  exact (Nat.not_le_of_lt hgap)
    (F.residual_capacity_le_crossing_capacity residual hsurj hsemantic)

end CrossingSequenceTraceFactorization

end PallLean.Paper93.DeepMath.PathB.CrossingSequenceContinuationHolonomy

#print axioms PallLean.Paper93.DeepMath.PathB.CrossingSequenceContinuationHolonomy.CrossingSequenceTraceFactorization.crossingView_faithful
#print axioms PallLean.Paper93.DeepMath.PathB.CrossingSequenceContinuationHolonomy.CrossingSequenceTraceFactorization.residual_capacity_le_crossing_capacity
#print axioms PallLean.Paper93.DeepMath.PathB.CrossingSequenceContinuationHolonomy.CrossingSequenceTraceFactorization.no_factorization_below_residual_capacity
