import PallLean.Paper93.DeepMath.PathB.ComputationalDepthObserverInvariantTransfer

/-!
# Rung 5 toy lower bounds

**STATUS: TOY RESTRICTED LOWER BOUNDS, NOT TC⁰/NC¹/width-5 BP BREAKTHROUGHS.**

This file proves deliberately weakened rung-5 lower bounds.  The point is to
stress-test the observer invariant on models that are weak enough to defeat
honestly:

* input-blind threshold circuits cannot compute parity on a nonempty input set;
* input-blind NC¹/formulas cannot compute parity on a nonempty input set;
* the existing width-1 branching-program and one-configuration space kernels are
  bundled with these toy endpoints.

These are not lower bounds for TC⁰, NC¹, width-5 branching programs, or real
bounded-space computation.  They are small, checked models where the invariant
really does rule the model out.
-/

namespace PallLean.Paper93.DeepMath.PathB

set_option linter.unusedVariables false

/-! ## Generic input-blind toy model -/

/-- A model is input-blind if its Boolean output is independent of the input. -/
def InputBlind {α Model : Type} (eval : Model -> (α -> Bool) -> Bool)
    (M : Model) : Prop :=
  forall σ τ : α -> Bool, eval M σ = eval M τ

/-- No input-blind model can compute parity on a nonempty input set. -/
theorem no_inputBlind_computes_parity
    {Model : Type} {n : Nat}
    (eval : Model -> (Fin n -> Bool) -> Bool)
    (i : Fin n) :
    Not (exists M : Model,
      InputBlind eval M /\
      (forall σ : Fin n -> Bool, eval M σ = parityFunction n σ)) := by
  rintro ⟨M, hblind, hcomp⟩
  have hsame := hblind (falseInput n) (oneHotInput i)
  have hdiff := parityFunction_falseInput_ne_oneHotInput i
  exact hdiff (by
    rw [hcomp (falseInput n), hcomp (oneHotInput i)] at hsame
    exact hsame)

/-! ## Toy TC⁰: input-blind threshold circuits -/

/-- Input-blind threshold circuits: a deliberately weak toy subclass of TC⁰. -/
def InputBlindThresholdCircuit {n : Nat} (C : ThresholdCircuitSyntax n) : Prop :=
  forall σ τ : Fin n -> Bool, C.eval σ = C.eval τ

/-- Input-blind threshold circuits cannot compute parity on nonempty inputs. -/
theorem no_inputBlindThresholdCircuit_computes_parity
    {n : Nat} (i : Fin n) :
    Not (exists C : ThresholdCircuitSyntax n,
      InputBlindThresholdCircuit C /\ C.Computes (parityFunction n)) := by
  exact no_inputBlind_computes_parity
    (fun (C : ThresholdCircuitSyntax n) σ => C.eval σ) i

/-- Input-blind TC⁰ lower-bound interface: for a nonempty input set, every
claimed lower bound holds vacuously for the input-blind subclass.  The content is
`no_inputBlindThresholdCircuit_computes_parity`. -/
def InputBlindTC0SizeLowerBoundAt (n depthBound lower : Nat) : Prop :=
  forall C : ThresholdCircuitSyntax n,
    InputBlindThresholdCircuit C ->
    C.Computes (parityFunction n) ->
    C.depth <= depthBound ->
    lower <= C.size

/-- Parity has arbitrary size lower bounds against input-blind TC⁰ circuits. -/
theorem inputBlindTC0_parity_sizeLowerBound
    {n : Nat} (i : Fin n) (depthBound lower : Nat) :
    InputBlindTC0SizeLowerBoundAt n depthBound lower := by
  intro C hblind hcomp _
  exact False.elim
    (no_inputBlindThresholdCircuit_computes_parity i ⟨C, hblind, hcomp⟩)

/-! ## Toy NC¹: input-blind formulas -/

/-- Input-blind formulas: a deliberately weak toy subclass of NC¹/formulas. -/
def InputBlindFormula {n : Nat} (A : PropFormula n) : Prop :=
  forall σ τ : Fin n -> Bool, A.eval σ = A.eval τ

/-- Input-blind formulas cannot compute parity on nonempty inputs. -/
theorem no_inputBlindFormula_computes_parity
    {n : Nat} (i : Fin n) :
    Not (exists A : PropFormula n,
      InputBlindFormula A /\ A.Computes (parityFunction n)) := by
  exact no_inputBlind_computes_parity
    (fun (A : PropFormula n) σ => A.eval σ) i

/-- Input-blind NC¹/formula lower-bound interface. -/
def InputBlindNC1SizeLowerBoundAt (n depthBound lower : Nat) : Prop :=
  forall A : PropFormula n,
    InputBlindFormula A ->
    A.Computes (parityFunction n) ->
    A.depth <= depthBound ->
    lower <= A.size

/-- Parity has arbitrary size lower bounds against input-blind formulas. -/
theorem inputBlindNC1_parity_sizeLowerBound
    {n : Nat} (i : Fin n) (depthBound lower : Nat) :
    InputBlindNC1SizeLowerBoundAt n depthBound lower := by
  intro A hblind hcomp _
  exact False.elim
    (no_inputBlindFormula_computes_parity i ⟨A, hblind, hcomp⟩)

/-! ## Observer-invariant packaging for the toy models -/

/-- Budgeted input-blind threshold circuits. -/
abbrev BudgetedInputBlindThresholdCircuit
    (n depthBound sizeBudget : Nat) : Type :=
  { C : ThresholdCircuitSyntax n //
    InputBlindThresholdCircuit C /\ C.depth <= depthBound /\ C.size <= sizeBudget }

/-- The toy TC⁰ input-blind lower bound as an observer-invariant preservation
instance. -/
def inputBlindTC0_observerInvariantPreservation
    {n depthBound lower sizeBudget : Nat} (i : Fin n) :
    Rung5ObserverInvariantPreservation
      (BudgetedInputBlindThresholdCircuit n depthBound sizeBudget)
      (ThresholdCircuitSyntax n)
      (fun C => C.val.Computes (parityFunction n))
      (fun C => C.val.size)
      (tc0SizeObserverInvariant n lower)
      lower sizeBudget where
  witnessOf C _ := C.val
  visible C hC :=
    inputBlindTC0_parity_sizeLowerBound i depthBound lower
      C.val C.property.1 hC C.property.2.1
  demand_ge _ _ := by simp [tc0SizeObserverInvariant]
  capacity_le_budget _ _ := by simp [tc0SizeObserverInvariant]
  budget_le C := C.property.2.2

/-- No budgeted input-blind threshold circuit computes parity if its size budget
is below the demanded lower bound. -/
theorem no_budgeted_inputBlindTC0_parity_of_observerInvariant
    {n depthBound lower sizeBudget : Nat} (i : Fin n)
    (hgap : sizeBudget < lower) :
    Not (exists C : BudgetedInputBlindThresholdCircuit n depthBound sizeBudget,
      C.val.Computes (parityFunction n)) :=
  no_rung5_model_of_observerInvariant_preservation
    (inputBlindTC0_observerInvariantPreservation
      (n := n) (depthBound := depthBound) (lower := lower)
      (sizeBudget := sizeBudget) i)
    hgap

/-- Budgeted input-blind formulas. -/
abbrev BudgetedInputBlindFormula
    (n depthBound sizeBudget : Nat) : Type :=
  { A : PropFormula n //
    InputBlindFormula A /\ A.depth <= depthBound /\ A.size <= sizeBudget }

/-- The toy NC¹/formula input-blind lower bound as an observer-invariant
preservation instance. -/
def inputBlindNC1_observerInvariantPreservation
    {n depthBound lower sizeBudget : Nat} (i : Fin n) :
    Rung5ObserverInvariantPreservation
      (BudgetedInputBlindFormula n depthBound sizeBudget)
      (PropFormula n)
      (fun A => A.val.Computes (parityFunction n))
      (fun A => A.val.size)
      (nc1SizeObserverInvariant n lower)
      lower sizeBudget where
  witnessOf A _ := A.val
  visible A hA :=
    inputBlindNC1_parity_sizeLowerBound i depthBound lower
      A.val A.property.1 hA A.property.2.1
  demand_ge _ _ := by simp [nc1SizeObserverInvariant]
  capacity_le_budget _ _ := by simp [nc1SizeObserverInvariant]
  budget_le A := A.property.2.2

/-- No budgeted input-blind formula computes parity if its size budget is below
the demanded lower bound. -/
theorem no_budgeted_inputBlindNC1_parity_of_observerInvariant
    {n depthBound lower sizeBudget : Nat} (i : Fin n)
    (hgap : sizeBudget < lower) :
    Not (exists A : BudgetedInputBlindFormula n depthBound sizeBudget,
      A.val.Computes (parityFunction n)) :=
  no_rung5_model_of_observerInvariant_preservation
    (inputBlindNC1_observerInvariantPreservation
      (n := n) (depthBound := depthBound) (lower := lower)
      (sizeBudget := sizeBudget) i)
    hgap

/-- Toy rung-5 lower-bound package. -/
structure Rung5ToyLowerBounds : Prop where
  input_blind_tc0 :
    forall {n depthBound lower sizeBudget : Nat} (i : Fin n),
      sizeBudget < lower ->
      Not (exists C : BudgetedInputBlindThresholdCircuit n depthBound sizeBudget,
        C.val.Computes (parityFunction n))
  input_blind_nc1 :
    forall {n depthBound lower sizeBudget : Nat} (i : Fin n),
      sizeBudget < lower ->
      Not (exists A : BudgetedInputBlindFormula n depthBound sizeBudget,
        A.val.Computes (parityFunction n))
  width_one_bp :
    forall {n lower lengthBudget : Nat} (i : Fin n),
      lengthBudget < lower ->
      Not (exists P : BudgetedWidthOneBranchingProgram n lengthBudget,
        P.val.Computes (parityFunction n))
  one_config_space :
    forall {n configBudget : Nat} (i : Fin n),
      configBudget < 2 ->
      Not (exists M : BudgetedSpaceBoundedMachine n configBudget,
        M.2.val.Computes (parityFunction n))

/-- The toy rung-5 lower bounds proved in this file and in the existing tiny
kernels. -/
theorem rung5_toyLowerBounds : Rung5ToyLowerBounds where
  input_blind_tc0 := by
    intro n depthBound lower sizeBudget i hgap
    exact no_budgeted_inputBlindTC0_parity_of_observerInvariant i hgap
  input_blind_nc1 := by
    intro n depthBound lower sizeBudget i hgap
    exact no_budgeted_inputBlindNC1_parity_of_observerInvariant i hgap
  width_one_bp := by
    intro n lower lengthBudget i hgap
    exact no_budgeted_widthOneBP_parity_of_observerInvariant i hgap
  one_config_space := by
    intro n configBudget i hgap
    exact no_budgeted_space_parity_of_observerInvariant i hgap

/-! ## Kernel-only trace -/

#print axioms no_inputBlind_computes_parity
#print axioms no_inputBlindThresholdCircuit_computes_parity
#print axioms inputBlindTC0_parity_sizeLowerBound
#print axioms no_inputBlindFormula_computes_parity
#print axioms inputBlindNC1_parity_sizeLowerBound
#print axioms inputBlindTC0_observerInvariantPreservation
#print axioms no_budgeted_inputBlindTC0_parity_of_observerInvariant
#print axioms inputBlindNC1_observerInvariantPreservation
#print axioms no_budgeted_inputBlindNC1_parity_of_observerInvariant
#print axioms rung5_toyLowerBounds

end PallLean.Paper93.DeepMath.PathB
