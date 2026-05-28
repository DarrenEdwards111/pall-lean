import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRung5ToyLowerBounds

/-!
# Rung 5 variable-access toy lower bounds

**STATUS: RESTRICTED VARIABLE-ACCESS LOWER BOUNDS, NOT TC⁰/NC¹ BREAKTHROUGHS.**

This file moves one notch beyond input-blind toy models.  It proves that parity
cannot be computed by a query branching program unless every variable is queried.
For schedules without repeated variables this gives a genuine length lower bound
`n <= length`.

The model is intentionally restricted: each branching-program layer queries one
input coordinate and updates state from that one bit.  This is not width-5 BP =
NC¹, but it is a real variable-access lower bound and a healthier rung-5 toy
than input-blindness.
-/

namespace PallLean.Paper93.DeepMath.PathB

open Finset

/-! ## Query branching programs -/

/-- One layer of a query branching program: query one variable and update the
state from that bit. -/
structure QueryBPLayer (n width : Nat) where
  var : Fin n
  next : Fin width -> Bool -> Fin width

/-- A deterministic query branching program with fixed width. -/
structure QueryBranchingProgram (n width : Nat) where
  layers : List (QueryBPLayer n width)
  start : Fin width
  accept : Finset (Fin width)

namespace QueryBranchingProgram

/-- Run a list of query-BP layers. -/
def runLayers {n width : Nat} (σ : Fin n -> Bool) :
    List (QueryBPLayer n width) -> Fin width -> Fin width
  | [], q => q
  | L :: Ls, q => runLayers σ Ls (L.next q (σ L.var))

/-- Final state. -/
def finalState {n width : Nat} (P : QueryBranchingProgram n width)
    (σ : Fin n -> Bool) : Fin width :=
  runLayers σ P.layers P.start

/-- Boolean evaluation. -/
def eval {n width : Nat} (P : QueryBranchingProgram n width)
    (σ : Fin n -> Bool) : Bool :=
  decide (P.finalState σ ∈ P.accept)

/-- Schedule of queried variables. -/
def vars {n width : Nat} (P : QueryBranchingProgram n width) : List (Fin n) :=
  P.layers.map (fun L => L.var)

/-- Length of a query branching program. -/
def length {n width : Nat} (P : QueryBranchingProgram n width) : Nat :=
  P.layers.length

/-- A query branching program computes a Boolean function. -/
def Computes {n width : Nat} (P : QueryBranchingProgram n width)
    (F : BoolFunction n) : Prop :=
  forall σ : Fin n -> Bool, P.eval σ = F σ

/-- If two inputs agree on every variable queried by a list of layers, then the
run from any state is identical. -/
theorem runLayers_eq_of_agree_on_vars
    {n width : Nat} (Ls : List (QueryBPLayer n width))
    {σ τ : Fin n -> Bool}
    (hagree : forall i : Fin n, i ∈ Ls.map (fun L => L.var) -> σ i = τ i)
    (q : Fin width) :
    runLayers σ Ls q = runLayers τ Ls q := by
  induction Ls generalizing q with
  | nil => rfl
  | cons L Ls ih =>
      have hvar : σ L.var = τ L.var := by
        exact hagree L.var (by simp)
      have htail : forall i : Fin n, i ∈ Ls.map (fun L => L.var) -> σ i = τ i := by
        intro i hi
        exact hagree i (by simp [hi])
      simp [runLayers, hvar, ih htail]

/-- If two inputs agree on all variables queried by a program, it evaluates them
identically. -/
theorem eval_eq_of_agree_on_vars
    {n width : Nat} (P : QueryBranchingProgram n width)
    {σ τ : Fin n -> Bool}
    (hagree : forall i : Fin n, i ∈ P.vars -> σ i = τ i) :
    P.eval σ = P.eval τ := by
  have hstate := runLayers_eq_of_agree_on_vars P.layers hagree P.start
  change decide (runLayers σ P.layers P.start ∈ P.accept) =
    decide (runLayers τ P.layers P.start ∈ P.accept)
  exact congrArg (fun q => decide (q ∈ P.accept)) hstate

/-- If a variable is never queried, the all-false input and the corresponding
one-hot input look identical to the query branching program. -/
theorem eval_falseInput_eq_eval_oneHotInput_of_not_mem_vars
    {n width : Nat} (P : QueryBranchingProgram n width) {i : Fin n}
    (hi : i ∉ P.vars) :
    P.eval (falseInput n) = P.eval (oneHotInput i) := by
  apply eval_eq_of_agree_on_vars P
  intro j hj
  have hji : j ≠ i := by
    intro h
    exact hi (by simpa [h] using hj)
  simp [falseInput, oneHotInput, hji]

/-- Every variable must be queried by a query branching program computing parity. -/
theorem mem_vars_of_computes_parity
    {n width : Nat} (P : QueryBranchingProgram n width)
    (hcomp : P.Computes (parityFunction n)) (i : Fin n) :
    i ∈ P.vars := by
  by_contra hi
  have heval := P.eval_falseInput_eq_eval_oneHotInput_of_not_mem_vars hi
  have hF : parityFunction n (falseInput n) = parityFunction n (oneHotInput i) := by
    rw [← hcomp (falseInput n), ← hcomp (oneHotInput i)]
    exact heval
  exact parityFunction_falseInput_ne_oneHotInput i hF

/-- The queried variables cover all input coordinates if the program computes
parity. -/
theorem vars_cover_of_computes_parity
    {n width : Nat} (P : QueryBranchingProgram n width)
    (hcomp : P.Computes (parityFunction n)) :
    (Finset.univ : Finset (Fin n)) ⊆ P.vars.toFinset := by
  intro i _
  exact List.mem_toFinset.mpr (P.mem_vars_of_computes_parity hcomp i)

/-- The support of a list has cardinality at most the list length. -/
theorem toFinset_card_le_length {α : Type} [DecidableEq α] (xs : List α) :
    xs.toFinset.card <= xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      calc
        (x :: xs).toFinset.card = (insert x xs.toFinset).card := by simp
        _ <= xs.toFinset.card + 1 := Finset.card_insert_le x xs.toFinset
        _ <= xs.length + 1 := by omega
        _ = (x :: xs).length := by simp

/-- Query branching programs computing parity have length at least `n`. -/
theorem length_ge_of_computes_parity
    {n width : Nat} (P : QueryBranchingProgram n width)
    (hcomp : P.Computes (parityFunction n)) :
    n <= P.length := by
  have hcover := P.vars_cover_of_computes_parity hcomp
  have hcard : (Finset.univ : Finset (Fin n)).card <= P.vars.toFinset.card :=
    Finset.card_le_card hcover
  have hsupp : P.vars.toFinset.card <= P.vars.length :=
    toFinset_card_le_length P.vars
  have hlen : P.vars.length = P.length := by
    simp [vars, length]
  simpa [Fintype.card_fin, hlen] using Nat.le_trans hcard hsupp

end QueryBranchingProgram

/-! ## Lower-bound interface and observer invariant packaging -/

/-- Pointwise length lower bound for query branching programs. -/
def QueryBPLengthLowerBoundAt
    (F : (n : Nat) -> BoolFunction n) (n width lower : Nat) : Prop :=
  forall P : QueryBranchingProgram n width,
    P.Computes (F n) -> lower <= P.length

/-- Parity needs query-BP length at least `n`, for every width. -/
theorem parity_queryBP_lengthLowerBound
    (n width : Nat) : QueryBPLengthLowerBoundAt parityFunction n width n := by
  intro P hcomp
  exact P.length_ge_of_computes_parity hcomp

/-- A query branching program packaged with a length budget. -/
abbrev BudgetedQueryBranchingProgram (n width lengthBudget : Nat) : Type :=
  { P : QueryBranchingProgram n width // P.length <= lengthBudget }

/-- Query-BP length invariant. -/
def queryBPLengthObserverInvariant (n width lower : Nat) :
    ObserverInvariant (QueryBranchingProgram n width) where
  demand _ := lower
  capacity P := P.length

/-- The parity query-BP lower bound as an observer-invariant preservation
instance. -/
def queryBP_parity_observerInvariantPreservation
    {n width lengthBudget : Nat} :
    Rung5ObserverInvariantPreservation
      (BudgetedQueryBranchingProgram n width lengthBudget)
      (QueryBranchingProgram n width)
      (fun P => P.val.Computes (parityFunction n))
      (fun P => P.val.length)
      (queryBPLengthObserverInvariant n width n)
      n lengthBudget where
  witnessOf P _ := P.val
  visible P hP := P.val.length_ge_of_computes_parity hP
  demand_ge _ _ := by simp [queryBPLengthObserverInvariant]
  capacity_le_budget _ _ := by simp [queryBPLengthObserverInvariant]
  budget_le P := P.property

/-- No query branching program of length below `n` computes parity. -/
theorem no_short_queryBP_parity_of_observerInvariant
    {n width lengthBudget : Nat} (hgap : lengthBudget < n) :
    Not (exists P : BudgetedQueryBranchingProgram n width lengthBudget,
      P.val.Computes (parityFunction n)) :=
  no_rung5_model_of_observerInvariant_preservation
    (queryBP_parity_observerInvariantPreservation
      (n := n) (width := width) (lengthBudget := lengthBudget))
    hgap

/-- Variable-access rung-5 toy lower-bound package. -/
structure Rung5VariableAccessLowerBounds : Prop where
  query_bp_length :
    forall n width : Nat, QueryBPLengthLowerBoundAt parityFunction n width n
  no_short_query_bp :
    forall {n width lengthBudget : Nat},
      lengthBudget < n ->
      Not (exists P : BudgetedQueryBranchingProgram n width lengthBudget,
        P.val.Computes (parityFunction n))

/-- The proved variable-access lower bounds. -/
theorem rung5_variableAccessLowerBounds : Rung5VariableAccessLowerBounds where
  query_bp_length := parity_queryBP_lengthLowerBound
  no_short_query_bp := by
    intro n width lengthBudget hgap
    exact no_short_queryBP_parity_of_observerInvariant hgap

/-! ## Kernel-only trace -/

#print axioms QueryBranchingProgram.runLayers_eq_of_agree_on_vars
#print axioms QueryBranchingProgram.eval_eq_of_agree_on_vars
#print axioms QueryBranchingProgram.eval_falseInput_eq_eval_oneHotInput_of_not_mem_vars
#print axioms QueryBranchingProgram.mem_vars_of_computes_parity
#print axioms QueryBranchingProgram.vars_cover_of_computes_parity
#print axioms QueryBranchingProgram.toFinset_card_le_length
#print axioms QueryBranchingProgram.length_ge_of_computes_parity
#print axioms parity_queryBP_lengthLowerBound
#print axioms queryBP_parity_observerInvariantPreservation
#print axioms no_short_queryBP_parity_of_observerInvariant
#print axioms rung5_variableAccessLowerBounds

end PallLean.Paper93.DeepMath.PathB
