import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUCRDContextualQuotientCurvatureAudit
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMachineSemantics

/-!
# Polynomial-observer quotient-curvature no-go

The contextual-quotient audit exhibits genuine curvature from one local bit per
bubble.  This file asks whether ordinary deterministic polynomial computation
forbids that phenomenon.  It does not.

We model an observer with one context-independent encoded state and a
context-dependent decoder.  The observer carries an explicit step counter and
a repository-standard polynomial budget.  A three-state, constant-work
observer retains the underlying point injectively, then decodes one Boolean bit
according to the current bubble.  Its induced quotient is exactly the curved
triangle quotient.

Therefore the proposed P-side conservation statement
"every polynomial observer induces a globally flat contextual quotient" is
false.  Even requiring a single global internal state, exact/injective storage,
and constant work does not repair it: context-dependent readout alone creates
curvature.  Any viable forcing theorem must constrain the operational decoder
or future-query semantics, not merely runtime, memory, or state uniformity.
-/

namespace PallLean.Paper93.DeepMath.PathB.UCRDPolynomialObserverCurvatureNoGo

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.UCRDContextualQuotientCurvatureAudit

universe u v w z

/-- A deterministic observer with one globally encoded state and
context-dependent readout, together with explicit polynomial work accounting. -/
structure PolynomialContextObserver
    (Context : Type u) (Point : Type v) (State : Type w) (Code : Type z) where
  encode : Point → State
  decode : Context → State → Code
  inputSize : Point → Nat
  steps : Context → Point → Nat
  budget : Nat → Nat
  polyBudget : IsPolynomialBudget budget
  steps_le_budget : ∀ i x, steps i x ≤ budget (inputSize x)

/-- The observer-visible label after global encoding and contextual readout. -/
def PolynomialContextObserver.label
    {Context : Type u} {Point : Type v} {State : Type w} {Code : Type z}
    (O : PolynomialContextObserver Context Point State Code) :
    Context → Point → Code :=
  fun i x ↦ O.decode i (O.encode x)

/-- Equality of contextually decoded outputs is the induced observer quotient. -/
def PolynomialContextObserver.inducedQuotient
    {Context : Type u} {Point : Type v} {State : Type w} {Code : Type z}
    {visible : Context → Point → Prop}
    (O : PolynomialContextObserver Context Point State Code) :
    ContextualQuotient visible :=
  quotientOfLabels O.label

/-- A constant budget is polynomial in the repository's concrete sense. -/
theorem constantOne_isPolynomialBudget :
    IsPolynomialBudget (fun _ : Nat ↦ 1) := by
  refine ⟨0, 1, ?_⟩
  intro n
  simp

/-- The curved observer retains the complete underlying point as its global
state; only its one-bit readout changes with context. -/
def trianglePolynomialObserver :
    PolynomialContextObserver TriangleContext TrianglePoint TrianglePoint Bool where
  encode := id
  decode := triangleLabel
  inputSize := fun _ ↦ 1
  steps := fun _ _ ↦ 1
  budget := fun _ ↦ 1
  polyBudget := constantOne_isPolynomialBudget
  steps_le_budget := by intro i x; rfl

theorem triangleObserver_encode_injective :
    Function.Injective trianglePolynomialObserver.encode := by
  intro x y h
  exact h

theorem triangleObserver_constant_work
    (i : TriangleContext) (x : TrianglePoint) :
    trianglePolynomialObserver.steps i x = 1 := by
  rfl

theorem triangleObserver_inducedQuotient_eq :
    trianglePolynomialObserver.inducedQuotient
        (visible := triangleVisible) = triangleQuotient := by
  rfl

/-- **Polynomial-observer curvature counterexample.**  A deterministic
constant-work observer with injective global storage has a genuinely non-flat
contextual quotient. -/
theorem polynomialObserver_with_curvature_exists :
    ∃ O : PolynomialContextObserver
        TriangleContext TrianglePoint TrianglePoint Bool,
      Function.Injective O.encode ∧
      HasQuotientCurvature
        (O.inducedQuotient (visible := triangleVisible)) := by
  refine ⟨trianglePolynomialObserver, triangleObserver_encode_injective, ?_⟩
  rw [triangleObserver_inducedQuotient_eq]
  exact triangle_hasQuotientCurvature

/-- The naive P-side forcing law is false already on the fixed triangle cover. -/
theorem not_all_polynomialObservers_flat :
    ¬ (∀ O : PolynomialContextObserver
          TriangleContext TrianglePoint TrianglePoint Bool,
        GloballyRealizable
          (O.inducedQuotient (visible := triangleVisible))) := by
  intro hflat
  exact triangle_hasQuotientCurvature
    (by
      rw [← triangleObserver_inducedQuotient_eq]
      exact hflat trianglePolynomialObserver)

end PallLean.Paper93.DeepMath.PathB.UCRDPolynomialObserverCurvatureNoGo

#print axioms PallLean.Paper93.DeepMath.PathB.UCRDPolynomialObserverCurvatureNoGo.constantOne_isPolynomialBudget
#print axioms PallLean.Paper93.DeepMath.PathB.UCRDPolynomialObserverCurvatureNoGo.triangleObserver_encode_injective
#print axioms PallLean.Paper93.DeepMath.PathB.UCRDPolynomialObserverCurvatureNoGo.polynomialObserver_with_curvature_exists
#print axioms PallLean.Paper93.DeepMath.PathB.UCRDPolynomialObserverCurvatureNoGo.not_all_polynomialObservers_flat
