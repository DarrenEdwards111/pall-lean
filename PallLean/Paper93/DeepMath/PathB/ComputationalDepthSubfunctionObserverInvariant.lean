import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRung5FormulaVariableAccessLowerBounds

/-!
# Subfunction-count observer invariant

**STATUS: SUPERPOLYNOMIAL-CAPABLE INVARIANT SCHEMA, NOT A NEW NC¹/TC⁰ LOWER BOUND.**

The variable-presence observer invariant has a linear ceiling: it can prove that
every variable is touched, but not super-polynomial lower bounds.  This file
adapts the observer layer to a stronger invariant: the number of distinct
residual/subfunctions exposed by a split of the input variables.

Subfunction count is a classic lower-bound resource because it can grow
exponentially.  This file proves that fact for the equality-split function:
its residual family has size `2^n`.  It also provides the generic transfer theorem:
if every model computing a target must have capacity at least the target's
subfunction count, and the available budget is below a required subfunction
lower bound, then no such model exists.

The missing frontier theorem for NC¹/TC⁰/width-5 BP is exactly the model-specific
capacity upper bound/preservation theorem.  The invariant here is capable of
super-polynomial values; it does not by itself prove that strong models have
small capacity.
-/

namespace PallLean.Paper93.DeepMath.PathB

open Finset

/-! ## Subfunction count -/

/-- Residual function obtained by fixing the left-side assignment. -/
def residualFunction (Left Right : Type)
    (F : (Left -> Bool) -> (Right -> Bool) -> Bool)
    (a : Left -> Bool) : (Right -> Bool) -> Bool :=
  fun b => F a b

/-- The finite set of residual functions exposed by all left-side assignments. -/
noncomputable def subfunctionSet (Left Right : Type)
    [Fintype Left] [DecidableEq Left]
    (F : (Left -> Bool) -> (Right -> Bool) -> Bool) :
    Finset ((Right -> Bool) -> Bool) := by
  classical
  exact (Finset.univ : Finset (Left -> Bool)).image (residualFunction Left Right F)

/-- Number of distinct residual functions. -/
noncomputable def subfunctionCount (Left Right : Type)
    [Fintype Left] [DecidableEq Left]
    (F : (Left -> Bool) -> (Right -> Bool) -> Bool) : Nat :=
  (subfunctionSet Left Right F).card

/-- If the residual map is injective, the subfunction count equals the number of
left-side assignments. -/
theorem subfunctionCount_eq_card_of_residual_injective
    (Left Right : Type) [Fintype Left] [DecidableEq Left]
    (F : (Left -> Bool) -> (Right -> Bool) -> Bool)
    (hinj : Function.Injective (residualFunction Left Right F)) :
    subfunctionCount Left Right F = Fintype.card (Left -> Bool) := by
  classical
  unfold subfunctionCount subfunctionSet
  calc
    ((Finset.univ : Finset (Left -> Bool)).image
        (residualFunction Left Right F)).card
        = (Finset.univ : Finset (Left -> Bool)).card := by
          exact Finset.card_image_of_injective _ (fun _ _ h => hinj h)
    _ = Fintype.card (Left -> Bool) := by simp

/-! ## Exponential example: equality split -/

/-- Equality across the split: the right assignment must equal the left
assignment.  Its residuals are singleton indicators, one per left assignment. -/
def equalitySplitFunction (α : Type) [DecidableEq (α -> Bool)] :
    (α -> Bool) -> (α -> Bool) -> Bool :=
  fun a b => decide (a = b)

/-- The equality-split residual map is injective. -/
theorem equalitySplit_residual_injective
    (α : Type) [DecidableEq (α -> Bool)] :
    Function.Injective
      (residualFunction α α (equalitySplitFunction α)) := by
  intro a a' h
  by_contra hne
  have hneq : a' ≠ a := by
    intro h'
    exact hne h'.symm
  have hval := congrFun h a
  simp [residualFunction, equalitySplitFunction, hneq] at hval

/-- Equality split has one distinct residual for every left assignment. -/
theorem subfunctionCount_equalitySplit
    (α : Type) [Fintype α] [DecidableEq α] [DecidableEq (α -> Bool)] :
    subfunctionCount α α (equalitySplitFunction α) =
      Fintype.card (α -> Bool) :=
  subfunctionCount_eq_card_of_residual_injective α α
    (equalitySplitFunction α)
    (equalitySplit_residual_injective α)

/-- For `n` Boolean variables on each side, equality split has `2^n` residual
subfunctions.  This shows the invariant has exponential range. -/
theorem subfunctionCount_equalitySplit_fin (n : Nat) :
    subfunctionCount (Fin n) (Fin n) (equalitySplitFunction (Fin n)) = 2 ^ n := by
  classical
  rw [subfunctionCount_equalitySplit]
  simp

/-! ## Observer transfer from subfunction lower bounds -/

/-- A model-capacity preservation statement for subfunction lower bounds.

`Capacity M` is the number of residual behaviours the model can expose.  The hard
part for any real model is the `capacity_sound` field: proving that computing the
target forces the model to expose at least the target's subfunction count, while
separately bounding `Capacity M` by a small budget. -/
structure SubfunctionCapacityPreservation
    (Model Left Right : Type) [Fintype Left] [DecidableEq Left]
    (Target : (Left -> Bool) -> (Right -> Bool) -> Bool)
    (Computes : Model -> Prop)
    (Capacity : Model -> Nat)
    (required budget : Nat) : Prop where
  lower_bound : required <= subfunctionCount Left Right Target
  capacity_sound : forall M : Model, Computes M -> subfunctionCount Left Right Target <= Capacity M
  budget_le : forall M : Model, Capacity M <= budget

/-- Generic subfunction observer transfer: if the model budget is below the
required subfunction count, no model computes the target. -/
theorem no_model_of_subfunction_capacity_gap
    {Model Left Right : Type} [Fintype Left] [DecidableEq Left]
    {Target : (Left -> Bool) -> (Right -> Bool) -> Bool}
    {Computes : Model -> Prop}
    {Capacity : Model -> Nat}
    {required budget : Nat}
    (Pres : SubfunctionCapacityPreservation
      Model Left Right Target Computes Capacity required budget)
    (hgap : budget < required) :
    Not (exists M : Model, Computes M) := by
  rintro ⟨M, hM⟩
  have hreq : required <= Capacity M :=
    Nat.le_trans Pres.lower_bound (Pres.capacity_sound M hM)
  have hbud : Capacity M <= budget := Pres.budget_le M
  exact Nat.not_lt_of_ge (Nat.le_trans hreq hbud) hgap

/-! ## Super-polynomial budget separation schema -/

/-- A numerical function eventually exceeds every polynomial `n^k`. -/
def SuperPolynomialLowerBound (lower : Nat -> Nat) : Prop :=
  forall k : Nat, exists N : Nat, forall n : Nat, N <= n -> n ^ k < lower n

/-- If a required lower bound is super-polynomial and a budget is bounded by one
polynomial, then eventually the budget is below the requirement. -/
theorem eventually_budget_lt_of_superPolynomial
    (required budget : Nat -> Nat) {k : Nat}
    (hsuper : SuperPolynomialLowerBound required)
    (hbudget : forall n : Nat, budget n <= n ^ k) :
    exists N : Nat, forall n : Nat, N <= n -> budget n < required n := by
  rcases hsuper k with ⟨N, hN⟩
  exact ⟨N, fun n hn => Nat.lt_of_le_of_lt (hbudget n) (hN n hn)⟩

/-- Family-level consequence: once subfunction preservation is available at each
input length, a super-polynomial required count beats any polynomial budget
eventually.  This is still conditional on the model-specific preservation
statement `Pres`. -/
theorem eventually_no_model_of_superPolynomial_subfunction_gap
    (required budget : Nat -> Nat) {k : Nat}
    (hsuper : SuperPolynomialLowerBound required)
    (hbudget : forall n : Nat, budget n <= n ^ k)
    {Model Left Right : Nat -> Type}
    [forall n, Fintype (Left n)] [forall n, DecidableEq (Left n)]
    {Target : forall n, (Left n -> Bool) -> (Right n -> Bool) -> Bool}
    {Computes : forall n, Model n -> Prop}
    {Capacity : forall n, Model n -> Nat}
    (Pres : forall n : Nat,
      SubfunctionCapacityPreservation
        (Model n) (Left n) (Right n) (Target n) (Computes n) (Capacity n)
        (required n) (budget n)) :
    exists N : Nat, forall n : Nat, N <= n ->
      Not (exists M : Model n, Computes n M) := by
  rcases eventually_budget_lt_of_superPolynomial required budget hsuper hbudget with
    ⟨N, hN⟩
  exact ⟨N, fun n hn => no_model_of_subfunction_capacity_gap (Pres n) (hN n hn)⟩

/-! ## Frontier target package -/

/-- The super-polynomial observer frontier: the invariant is now strong enough
to express super-polynomial lower bounds.  What remains open for strong models is
proving their subfunction capacity is polynomially bounded for an explicit hard
target. -/
structure SubfunctionObserverFrontier : Prop where
  exponential_example : forall n : Nat,
    subfunctionCount (Fin n) (Fin n) (equalitySplitFunction (Fin n)) = 2 ^ n
  transfer :
    forall {Model Left Right : Type} [Fintype Left] [DecidableEq Left]
      {Target : (Left -> Bool) -> (Right -> Bool) -> Bool}
      {Computes : Model -> Prop}
      {Capacity : Model -> Nat}
      {required budget : Nat},
      SubfunctionCapacityPreservation
        Model Left Right Target Computes Capacity required budget ->
      budget < required ->
      Not (exists M : Model, Computes M)
  eventual_superpoly_gap :
    forall (required budget : Nat -> Nat) {k : Nat},
      SuperPolynomialLowerBound required ->
      (forall n : Nat, budget n <= n ^ k) ->
      exists N : Nat, forall n : Nat, N <= n -> budget n < required n

/-- Completed subfunction observer frontier layer. -/
theorem subfunctionObserverFrontier : SubfunctionObserverFrontier where
  exponential_example := subfunctionCount_equalitySplit_fin
  transfer := by
    intro Model Left Right hLeft hDec Target Computes Capacity required budget Pres hgap
    exact no_model_of_subfunction_capacity_gap Pres hgap
  eventual_superpoly_gap := by
    intro required budget k hsuper hbudget
    exact eventually_budget_lt_of_superPolynomial required budget hsuper hbudget

/-! ## Kernel-only trace -/

#print axioms subfunctionCount_eq_card_of_residual_injective
#print axioms equalitySplit_residual_injective
#print axioms subfunctionCount_equalitySplit
#print axioms subfunctionCount_equalitySplit_fin
#print axioms no_model_of_subfunction_capacity_gap
#print axioms eventually_budget_lt_of_superPolynomial
#print axioms eventually_no_model_of_superPolynomial_subfunction_gap
#print axioms subfunctionObserverFrontier

end PallLean.Paper93.DeepMath.PathB
