import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRung5VariableAccessLowerBounds

/-!
# Rung 5 formula variable-access lower bounds

**STATUS: GENUINE LINEAR FORMULA LOWER BOUND, NOT AN NC¹ BREAKTHROUGH.**

This file pushes the observer/variable-access invariant from query branching
programs to unrestricted propositional formulas in the existing syntax.

The theorem is real but modest: any formula computing parity must mention every
input variable, hence its syntactic size is at least `n`.  This is not a
super-polynomial NC¹ lower bound; it is the variable-access floor that any such
lower bound must refine.
-/

namespace PallLean.Paper93.DeepMath.PathB

open Finset

namespace PropFormula

/-- Variables mentioned by a propositional formula. -/
def vars {n : Nat} : PropFormula n -> Finset (Fin n)
  | falsum => ∅
  | var i => {i}
  | neg A => A.vars
  | and A B => A.vars ∪ B.vars
  | or A B => A.vars ∪ B.vars
  | imp A B => A.vars ∪ B.vars

@[simp] theorem vars_falsum {n : Nat} : (falsum (n := n)).vars = ∅ := rfl
@[simp] theorem vars_var {n : Nat} (i : Fin n) : (var i).vars = {i} := rfl
@[simp] theorem vars_neg {n : Nat} (A : PropFormula n) : (neg A).vars = A.vars := rfl
@[simp] theorem vars_and {n : Nat} (A B : PropFormula n) :
    (and A B).vars = A.vars ∪ B.vars := rfl
@[simp] theorem vars_or {n : Nat} (A B : PropFormula n) :
    (or A B).vars = A.vars ∪ B.vars := rfl
@[simp] theorem vars_imp {n : Nat} (A B : PropFormula n) :
    (imp A B).vars = A.vars ∪ B.vars := rfl

/-- Formula evaluation depends only on variables mentioned by the formula. -/
theorem eval_eq_of_agree_on_vars
    {n : Nat} (A : PropFormula n) {σ τ : Fin n -> Bool}
    (hagree : forall i : Fin n, i ∈ A.vars -> σ i = τ i) :
    A.eval σ = A.eval τ := by
  induction A with
  | falsum => rfl
  | var i =>
      exact hagree i (by simp [vars])
  | neg A ih =>
      simp [eval, ih hagree]
  | and A B ihA ihB =>
      have hA : forall i : Fin n, i ∈ A.vars -> σ i = τ i := by
        intro i hi
        exact hagree i (by simp [vars, hi])
      have hB : forall i : Fin n, i ∈ B.vars -> σ i = τ i := by
        intro i hi
        exact hagree i (by simp [vars, hi])
      simp [eval, ihA hA, ihB hB]
  | or A B ihA ihB =>
      have hA : forall i : Fin n, i ∈ A.vars -> σ i = τ i := by
        intro i hi
        exact hagree i (by simp [vars, hi])
      have hB : forall i : Fin n, i ∈ B.vars -> σ i = τ i := by
        intro i hi
        exact hagree i (by simp [vars, hi])
      simp [eval, ihA hA, ihB hB]
  | imp A B ihA ihB =>
      have hA : forall i : Fin n, i ∈ A.vars -> σ i = τ i := by
        intro i hi
        exact hagree i (by simp [vars, hi])
      have hB : forall i : Fin n, i ∈ B.vars -> σ i = τ i := by
        intro i hi
        exact hagree i (by simp [vars, hi])
      simp [eval, ihA hA, ihB hB]

/-- If a formula omits variable `i`, the all-false and one-hot-`i` inputs are
indistinguishable to it. -/
theorem eval_falseInput_eq_eval_oneHotInput_of_not_mem_vars
    {n : Nat} (A : PropFormula n) {i : Fin n} (hi : i ∉ A.vars) :
    A.eval (falseInput n) = A.eval (oneHotInput i) := by
  apply A.eval_eq_of_agree_on_vars
  intro j hj
  have hji : j ≠ i := by
    intro h
    exact hi (by simpa [h] using hj)
  simp [falseInput, oneHotInput, hji]

/-- Any formula computing parity must mention every variable. -/
theorem mem_vars_of_computes_parity
    {n : Nat} (A : PropFormula n)
    (hcomp : A.Computes (parityFunction n)) (i : Fin n) :
    i ∈ A.vars := by
  by_contra hi
  have heval := A.eval_falseInput_eq_eval_oneHotInput_of_not_mem_vars hi
  have hF : parityFunction n (falseInput n) = parityFunction n (oneHotInput i) := by
    rw [← hcomp (falseInput n), ← hcomp (oneHotInput i)]
    exact heval
  exact parityFunction_falseInput_ne_oneHotInput i hF

/-- The variables of a parity-computing formula cover all inputs. -/
theorem vars_cover_of_computes_parity
    {n : Nat} (A : PropFormula n)
    (hcomp : A.Computes (parityFunction n)) :
    (Finset.univ : Finset (Fin n)) ⊆ A.vars := by
  intro i _
  exact A.mem_vars_of_computes_parity hcomp i

/-- The number of variables mentioned by a formula is bounded by its size. -/
theorem vars_card_le_size {n : Nat} (A : PropFormula n) :
    A.vars.card <= A.size := by
  induction A with
  | falsum => simp [vars, size]
  | var i => simp [vars, size]
  | neg A ih =>
      simp [vars, size]
      omega
  | and A B ihA ihB =>
      have hcup : (A.vars ∪ B.vars).card <= A.vars.card + B.vars.card :=
        Finset.card_union_le A.vars B.vars
      simp [vars, size]
      omega
  | or A B ihA ihB =>
      have hcup : (A.vars ∪ B.vars).card <= A.vars.card + B.vars.card :=
        Finset.card_union_le A.vars B.vars
      simp [vars, size]
      omega
  | imp A B ihA ihB =>
      have hcup : (A.vars ∪ B.vars).card <= A.vars.card + B.vars.card :=
        Finset.card_union_le A.vars B.vars
      simp [vars, size]
      omega

/-- Any formula computing parity has size at least `n`. -/
theorem size_ge_of_computes_parity
    {n : Nat} (A : PropFormula n)
    (hcomp : A.Computes (parityFunction n)) :
    n <= A.size := by
  have hcover := A.vars_cover_of_computes_parity hcomp
  have hcard : (Finset.univ : Finset (Fin n)).card <= A.vars.card :=
    Finset.card_le_card hcover
  have hvars := A.vars_card_le_size
  simpa [Fintype.card_fin] using Nat.le_trans hcard hvars

end PropFormula

/-! ## Lower-bound interface and observer packaging -/

/-- Parity formula-size lower bound at every depth: every formula computing
parity has size at least `n`. -/
theorem parity_formula_sizeLowerBound
    (n depthBound : Nat) : NC1FormulaSizeLowerBoundAt parityFunction n depthBound n := by
  intro A hcomp _
  exact A.size_ge_of_computes_parity hcomp

/-- Observer-invariant preservation for the formula variable-access lower bound. -/
def formulaParity_observerInvariantPreservation
    {n depthBound sizeBudget : Nat} :
    Rung5ObserverInvariantPreservation
      (BudgetedNC1Formula n depthBound sizeBudget)
      (PropFormula n)
      (fun A => A.val.Computes (parityFunction n))
      (fun A => A.val.size)
      (nc1SizeObserverInvariant n n)
      n sizeBudget where
  witnessOf A _ := A.val
  visible A hA := A.val.size_ge_of_computes_parity hA
  demand_ge _ _ := by simp [nc1SizeObserverInvariant]
  capacity_le_budget _ _ := by simp [nc1SizeObserverInvariant]
  budget_le A := A.property.2

/-- No formula of size below `n` computes parity, regardless of depth. -/
theorem no_small_formula_parity_of_observerInvariant
    {n depthBound sizeBudget : Nat} (hgap : sizeBudget < n) :
    Not (exists A : BudgetedNC1Formula n depthBound sizeBudget,
      A.val.Computes (parityFunction n)) :=
  no_rung5_model_of_observerInvariant_preservation
    (formulaParity_observerInvariantPreservation
      (n := n) (depthBound := depthBound) (sizeBudget := sizeBudget))
    hgap

/-- Formula variable-access lower-bound package. -/
structure Rung5FormulaVariableAccessLowerBounds : Prop where
  formula_size :
    forall n depthBound : Nat, NC1FormulaSizeLowerBoundAt parityFunction n depthBound n
  no_small_formula :
    forall {n depthBound sizeBudget : Nat},
      sizeBudget < n ->
      Not (exists A : BudgetedNC1Formula n depthBound sizeBudget,
        A.val.Computes (parityFunction n))

/-- The proved formula variable-access lower bounds. -/
theorem rung5_formulaVariableAccessLowerBounds :
    Rung5FormulaVariableAccessLowerBounds where
  formula_size := parity_formula_sizeLowerBound
  no_small_formula := by
    intro n depthBound sizeBudget hgap
    exact no_small_formula_parity_of_observerInvariant hgap

/-! ## Kernel-only trace -/

#print axioms PropFormula.eval_eq_of_agree_on_vars
#print axioms PropFormula.eval_falseInput_eq_eval_oneHotInput_of_not_mem_vars
#print axioms PropFormula.mem_vars_of_computes_parity
#print axioms PropFormula.vars_cover_of_computes_parity
#print axioms PropFormula.vars_card_le_size
#print axioms PropFormula.size_ge_of_computes_parity
#print axioms parity_formula_sizeLowerBound
#print axioms formulaParity_observerInvariantPreservation
#print axioms no_small_formula_parity_of_observerInvariant
#print axioms rung5_formulaVariableAccessLowerBounds

end PallLean.Paper93.DeepMath.PathB
