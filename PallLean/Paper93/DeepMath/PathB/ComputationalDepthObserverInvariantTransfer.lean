import PallLean.Paper93.DeepMath.PathB.ComputationalDepthObserverProofComplexityAttachment
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRung5IntermediateModels

/-!
# Observer invariant transfer toward rung 5

**STATUS: INVARIANT SCHEMA / FRONTIER TARGET, NOT A RUNG-5 LOWER-BOUND ENGINE.**

This file extracts the common payload of the observer layer across rungs 1--4:
a natural-number invariant has a **demand** side and a **channel capacity** side.
A lower bound is a proof that every correct restricted object has demand bounded
by its available capacity; a model is ruled out only when the capacity budget is
strictly below the demanded invariant.

This captures the real pattern already present in the lower rungs:

* rung 1: expansion forces visible edge-boundary demand;
* rung 2: resolution width/medium clauses force local-channel demand;
* rung 3: degree/rank/depth interfaces force algebraic or semi-algebraic demand;
* rung 4: parity forces decision-tree depth, and DNF residual width feeds a
  decision-tree endpoint.

For rung 5, this does **not** prove TC⁰, NC¹, width-5 branching-program, or real
bounded-space lower bounds.  It records the exact missing ingredient: a
preservation theorem saying a rung-5 model computing the target must carry the
same observer invariant with insufficient capacity.  Such preservation theorems
are the frontier/literature-level hard part.
-/

namespace PallLean.Paper93.DeepMath.PathB

set_option linter.unusedVariables false

/-! ## Generic observer invariant -/

/-- A numerical observer invariant on a class of objects: `demand` is the amount
of boundary/counterfactual variation the object must carry, while `capacity` is
what the restricted channel exposes. -/
structure ObserverInvariant (Obj : Type) where
  demand : Obj -> Nat
  capacity : Obj -> Nat

namespace ObserverInvariant

/-- The invariant is visible on an object when demand fits into capacity. -/
def Visible {Obj : Type} (I : ObserverInvariant Obj) (x : Obj) : Prop :=
  I.demand x <= I.capacity x

/-- A budget gap for an object: the channel capacity is below the invariant
needed. -/
def Gap {Obj : Type} (I : ObserverInvariant Obj) (x : Obj) : Prop :=
  I.capacity x < I.demand x

/-- Visibility and gap are incompatible. -/
theorem not_visible_of_gap {Obj : Type} (I : ObserverInvariant Obj) (x : Obj)
    (hgap : I.Gap x) : Not (I.Visible x) := by
  intro hvis
  exact Nat.not_lt_of_ge hvis hgap

end ObserverInvariant

/-- A lower-bound interface says every object satisfying `Good` visibly carries
the invariant.  This is the common observer-layer shape of the rungs. -/
def ObserverInvariantLowerBound {Obj : Type}
    (I : ObserverInvariant Obj) (Good : Obj -> Prop) : Prop :=
  forall x : Obj, Good x -> I.Visible x

/-- If every good object must visibly carry an invariant, but all objects in a
candidate family have capacity below demand, then no object in the family is
good. -/
theorem no_good_object_of_invariant_gap
    {Obj : Type} (I : ObserverInvariant Obj) (Good Candidate : Obj -> Prop)
    (Hlb : ObserverInvariantLowerBound I Good)
    (Hgap : forall x : Obj, Candidate x -> I.Gap x) :
    Not (exists x : Obj, Candidate x /\ Good x) := by
  rintro ⟨x, hCand, hGood⟩
  exact I.not_visible_of_gap x (Hgap x hCand) (Hlb x hGood)

/-! ## Rung-4 instances: the invariant is real, not vocabulary -/

/-- Decision-tree parity invariant: the demand is `n`, capacity is tree depth. -/
def parityDecisionTreeInvariant (n : Nat) : ObserverInvariant (BoolDecisionTree n) where
  demand _ := n
  capacity T := T.depth

/-- The proved parity decision-tree theorem is exactly an observer-invariant
lower bound. -/
theorem parityDecisionTree_observerInvariantLowerBound (n : Nat) :
    ObserverInvariantLowerBound (parityDecisionTreeInvariant n)
      (fun T : BoolDecisionTree n => T.Computes (parityFunction n)) := by
  intro T hcomp
  exact BoolDecisionTree.depth_ge_of_computes_parity T hcomp

/-- No decision tree of depth below `n` computes parity.  This is just the real
rung-4 theorem expressed through the extracted invariant schema. -/
theorem no_shallow_decisionTree_of_parityInvariantGap
    {n depthBudget : Nat} (hgap : depthBudget < n) :
    Not (exists T : BoolDecisionTree n,
      T.Computes (parityFunction n) /\ T.depth <= depthBudget) := by
  rintro ⟨T, hcomp, hdepth⟩
  have hvisible := parityDecisionTree_observerInvariantLowerBound n T hcomp
  exact Nat.not_lt_of_ge (Nat.le_trans hvisible hdepth) hgap

/-- DNF parity invariant: demand is `n`, capacity is total literal width. -/
def parityDNFInvariant (n : Nat) : ObserverInvariant (Rung4DNF n) where
  demand _ := n
  capacity D := D.totalWidth

/-- The deterministic switching endpoint makes DNF total width an observer
capacity for parity. -/
theorem parityDNF_observerInvariantLowerBound (n : Nat) :
    ObserverInvariantLowerBound (parityDNFInvariant n)
      (fun D : Rung4DNF n => D.Computes (parityFunction n)) := by
  intro D hcomp
  exact Rung4DNF.totalWidth_ge_of_computes_parity D hcomp

/-- No DNF of total literal width below `n` computes parity. -/
theorem no_lowWidth_DNF_of_parityInvariantGap
    {n widthBudget : Nat} (hgap : widthBudget < n) :
    Not (exists D : Rung4DNF n,
      D.Computes (parityFunction n) /\ D.totalWidth <= widthBudget) := by
  rintro ⟨D, hcomp, hwidth⟩
  have hvisible := parityDNF_observerInvariantLowerBound n D hcomp
  exact Nat.not_lt_of_ge (Nat.le_trans hvisible hwidth) hgap

/-! ## Rung-5 frontier: preservation is the missing theorem -/

/-- A preservation target from a rung-5 model type into an observer invariant.

This is the honest frontier object.  To get a rung-5 lower bound from rungs 1--4,
one must prove that every correct rung-5 model induces an invariant witness whose
capacity is controlled by the model budget.  That preservation statement is where
TC⁰/NC¹/BP/bounded-space hardness lives. -/
structure Rung5ObserverInvariantPreservation
    (Model Witness : Type)
    (Computes : Model -> Prop)
    (Budget : Model -> Nat)
    (I : ObserverInvariant Witness)
    (demandLower budgetUpper : Nat) : Type where
  witnessOf : forall M : Model, Computes M -> Witness
  visible : forall M hM, I.Visible (witnessOf M hM)
  demand_ge : forall M hM, demandLower <= I.demand (witnessOf M hM)
  capacity_le_budget : forall M hM, I.capacity (witnessOf M hM) <= Budget M
  budget_le : forall M, Budget M <= budgetUpper

/-- The generic rung-5 transfer theorem.  If a preservation theorem exists and
the budget is below the invariant demand, no rung-5 model computes the target.

The theorem is elementary; the hard part is supplying `Pres`. -/
theorem no_rung5_model_of_observerInvariant_preservation
    {Model Witness : Type}
    {Computes : Model -> Prop}
    {Budget : Model -> Nat}
    {I : ObserverInvariant Witness}
    {demandLower budgetUpper : Nat}
    (Pres : Rung5ObserverInvariantPreservation
      Model Witness Computes Budget I demandLower budgetUpper)
    (hgap : budgetUpper < demandLower) :
    Not (exists M : Model, Computes M) := by
  rintro ⟨M, hM⟩
  have hvisible := Pres.visible M hM
  have hdem := Pres.demand_ge M hM
  have hcap := Pres.capacity_le_budget M hM
  have hbud := Pres.budget_le M
  have hle : demandLower <= budgetUpper :=
    Nat.le_trans hdem (Nat.le_trans hvisible (Nat.le_trans hcap hbud))
  exact Nat.not_lt_of_ge hle hgap

/-- TC⁰-specific preservation target.  This is not supplied by the file; it is
what a real rung-5 breakthrough would have to prove for a chosen target family. -/
def TC0ObserverInvariantPreservationTarget
    (F : (n : Nat) -> BoolFunction n) (n depthBound sizeBudget : Nat)
    (Witness : Type) (I : ObserverInvariant Witness) (demandLower : Nat) : Type :=
  Rung5ObserverInvariantPreservation
    (ThresholdCircuitSyntax n)
    Witness
    (fun C => C.Computes (F n) /\ C.depth <= depthBound)
    (fun C => C.size)
    I demandLower sizeBudget

/-- NC¹/formula preservation target. -/
def NC1ObserverInvariantPreservationTarget
    (F : (n : Nat) -> BoolFunction n) (n depthBound sizeBudget : Nat)
    (Witness : Type) (I : ObserverInvariant Witness) (demandLower : Nat) : Type :=
  Rung5ObserverInvariantPreservation
    (PropFormula n)
    Witness
    (fun A => A.Computes (F n) /\ A.depth <= depthBound)
    (fun A => A.size)
    I demandLower sizeBudget

/-- Branching-program preservation target.  For width 5 this is the Barrington
frontier; proving a strong preservation/lower bound here is not routine. -/
def BranchingProgramObserverInvariantPreservationTarget
    (F : (n : Nat) -> BoolFunction n) (n width lengthBudget : Nat)
    (Witness : Type) (I : ObserverInvariant Witness) (demandLower : Nat) : Type :=
  Rung5ObserverInvariantPreservation
    (BranchingProgram n width)
    Witness
    (fun P => P.Computes (F n))
    (fun P => P.length)
    I demandLower lengthBudget

/-- Bounded-space preservation target, formulated in terms of finite
configuration count. -/
def SpaceObserverInvariantPreservationTarget
    (F : (n : Nat) -> BoolFunction n) (n configBudget : Nat)
    (Witness : Type) (I : ObserverInvariant Witness) (demandLower : Nat) : Type :=
  forall configs : Nat,
    Rung5ObserverInvariantPreservation
      (SpaceBoundedMachine n configs)
      Witness
      (fun M => M.Computes (F n))
      (fun _ => configs)
      I demandLower configBudget

/-! ## Concrete tiny rung-5 boundary kernels via the invariant transfer -/

/-- Budgeted width-1 branching programs.  The budget is built into the type so
`Rung5ObserverInvariantPreservation.budget_le` is an honest field, not a hidden
assumption. -/
abbrev BudgetedWidthOneBranchingProgram (n lengthBudget : Nat) : Type :=
  { P : BranchingProgram n 1 // P.length <= lengthBudget }

/-- Width-1 branching-program parity invariant: demand is the requested lower
bound, capacity is program length. -/
def widthOneBPParityInvariant (n lower : Nat) :
    ObserverInvariant (BranchingProgram n 1) where
  demand _ := lower
  capacity P := P.length

/-- The tiny width-1 branching-program lower bound is a genuine preservation
instance of the observer invariant schema.  It is deliberately tiny: it says
nothing about width 5 or NC¹. -/
def widthOneBP_parity_observerInvariantPreservation
    {n lower lengthBudget : Nat} (i : Fin n) :
    Rung5ObserverInvariantPreservation
      (BudgetedWidthOneBranchingProgram n lengthBudget)
      (BranchingProgram n 1)
      (fun P => P.val.Computes (parityFunction n))
      (fun P => P.val.length)
      (widthOneBPParityInvariant n lower)
      lower lengthBudget where
  witnessOf P _ := P.val
  visible P hP :=
    width_one_branchingProgram_parity_length_lower_bound i lower P.val hP
  demand_ge _ _ := by
    simp [widthOneBPParityInvariant]
  capacity_le_budget _ _ := by
    simp [widthOneBPParityInvariant]
  budget_le P := P.property

/-- No budgeted width-1 branching program of length below the demanded invariant
computes parity.  This is the generic transfer theorem applied to a real tiny
rung-5 kernel. -/
theorem no_budgeted_widthOneBP_parity_of_observerInvariant
    {n lower lengthBudget : Nat} (i : Fin n)
    (hgap : lengthBudget < lower) :
    Not (exists P : BudgetedWidthOneBranchingProgram n lengthBudget,
      P.val.Computes (parityFunction n)) :=
  no_rung5_model_of_observerInvariant_preservation
    (widthOneBP_parity_observerInvariantPreservation
      (n := n) (lower := lower) (lengthBudget := lengthBudget) i)
    hgap

/-- A bounded-space machine packaged with a configuration budget. -/
abbrev BudgetedSpaceBoundedMachine (n configBudget : Nat) : Type :=
  Sigma (fun configs : Nat =>
    { M : SpaceBoundedMachine n configs // configs <= configBudget })

/-- Space-machine witnesses remember their configuration count. -/
abbrev SpaceBoundedWitness (n : Nat) : Type :=
  Sigma (fun configs : Nat => SpaceBoundedMachine n configs)

/-- Configuration-count invariant: demand is a lower bound on configurations;
capacity is the witness's actual number of configurations. -/
def spaceConfigObserverInvariant (n demandLower : Nat) :
    ObserverInvariant (SpaceBoundedWitness n) where
  demand _ := demandLower
  capacity W := W.1

/-- The two-configuration parity kernel is a preservation instance for the
bounded-space observer invariant.  Again, this is a tiny endpoint kernel, not a
space-hierarchy theorem. -/
def boundedSpace_parity_twoConfig_observerInvariantPreservation
    {n configBudget : Nat} (i : Fin n) :
    Rung5ObserverInvariantPreservation
      (BudgetedSpaceBoundedMachine n configBudget)
      (SpaceBoundedWitness n)
      (fun M => M.2.val.Computes (parityFunction n))
      (fun M => M.1)
      (spaceConfigObserverInvariant n 2)
      2 configBudget where
  witnessOf M _ := ⟨M.1, M.2.val⟩
  visible M hM :=
    parity_spaceBounded_config_lower_bound_two i M.1 M.2.val hM
  demand_ge _ _ := by
    simp [spaceConfigObserverInvariant]
  capacity_le_budget _ _ := by
    simp [spaceConfigObserverInvariant]
  budget_le M := M.2.property

/-- No bounded-space machine with fewer than two configurations computes parity
on a nonempty input set, obtained through the observer-invariant transfer. -/
theorem no_budgeted_space_parity_of_observerInvariant
    {n configBudget : Nat} (i : Fin n) (hgap : configBudget < 2) :
    Not (exists M : BudgetedSpaceBoundedMachine n configBudget,
      M.2.val.Computes (parityFunction n)) :=
  no_rung5_model_of_observerInvariant_preservation
    (boundedSpace_parity_twoConfig_observerInvariantPreservation
      (n := n) (configBudget := configBudget) i)
    hgap

/-- The concrete part of the rung-5 observer boundary completed here: tiny,
proved preservation kernels for width-1 branching programs and one-configuration
bounded-space machines.  The deep TC⁰/NC¹/width-5/real-space frontier remains
outside this structure. -/
structure Rung5ConcreteObserverBoundaryKernels : Prop where
  width_one_bp :
    forall {n lower lengthBudget : Nat} (i : Fin n),
      lengthBudget < lower ->
      Not (exists P : BudgetedWidthOneBranchingProgram n lengthBudget,
        P.val.Computes (parityFunction n))
  bounded_space_two_configs :
    forall {n configBudget : Nat} (i : Fin n),
      configBudget < 2 ->
      Not (exists M : BudgetedSpaceBoundedMachine n configBudget,
        M.2.val.Computes (parityFunction n))

/-- The proved tiny rung-5 observer-boundary kernels. -/
theorem rung5_concreteObserverBoundaryKernels :
    Rung5ConcreteObserverBoundaryKernels where
  width_one_bp := by
    intro n lower lengthBudget i hgap
    exact no_budgeted_widthOneBP_parity_of_observerInvariant i hgap
  bounded_space_two_configs := by
    intro n configBudget i hgap
    exact no_budgeted_space_parity_of_observerInvariant i hgap

/-- A completed rung-5 observer boundary would consist of preservation theorems
for the frontier models.  The fields are target types, not data supplied here;
this structure is a precise target list, not a proof. -/
structure Rung5ObserverBoundaryFrontier
    (F : (n : Nat) -> BoolFunction n) (n : Nat) : Type 1 where
  Witness : Type
  invariant : ObserverInvariant Witness
  demandLower : Nat
  tc0_target : Nat -> Nat -> Type
  nc1_target : Nat -> Nat -> Type
  bp_target : Nat -> Nat -> Type
  space_target : Nat -> Type
  tc0_target_eq : forall depthBound sizeBudget,
    tc0_target depthBound sizeBudget =
      TC0ObserverInvariantPreservationTarget
        F n depthBound sizeBudget Witness invariant demandLower
  nc1_target_eq : forall depthBound sizeBudget,
    nc1_target depthBound sizeBudget =
      NC1ObserverInvariantPreservationTarget
        F n depthBound sizeBudget Witness invariant demandLower
  bp_target_eq : forall width lengthBudget,
    bp_target width lengthBudget =
      BranchingProgramObserverInvariantPreservationTarget
        F n width lengthBudget Witness invariant demandLower
  space_target_eq : forall configBudget,
    space_target configBudget =
      SpaceObserverInvariantPreservationTarget
        F n configBudget Witness invariant demandLower

/-- The extracted invariant schema helps complete the *boundary specification* of
rung 5: it says exactly which preservation theorems must be proved.  It does not
supply those theorems. -/
def rung5ObserverBoundaryFrontier
    (F : (n : Nat) -> BoolFunction n) (n : Nat)
    (Witness : Type) (I : ObserverInvariant Witness) (demandLower : Nat) :
    Rung5ObserverBoundaryFrontier F n where
  Witness := Witness
  invariant := I
  demandLower := demandLower
  tc0_target depthBound sizeBudget :=
    TC0ObserverInvariantPreservationTarget
      F n depthBound sizeBudget Witness I demandLower
  nc1_target depthBound sizeBudget :=
    NC1ObserverInvariantPreservationTarget
      F n depthBound sizeBudget Witness I demandLower
  bp_target width lengthBudget :=
    BranchingProgramObserverInvariantPreservationTarget
      F n width lengthBudget Witness I demandLower
  space_target configBudget :=
    SpaceObserverInvariantPreservationTarget
      F n configBudget Witness I demandLower
  tc0_target_eq _ _ := rfl
  nc1_target_eq _ _ := rfl
  bp_target_eq _ _ := rfl
  space_target_eq _ := rfl

/-! ## Kernel-only trace -/

#print axioms ObserverInvariant.not_visible_of_gap
#print axioms no_good_object_of_invariant_gap
#print axioms parityDecisionTree_observerInvariantLowerBound
#print axioms no_shallow_decisionTree_of_parityInvariantGap
#print axioms parityDNF_observerInvariantLowerBound
#print axioms no_lowWidth_DNF_of_parityInvariantGap
#print axioms no_rung5_model_of_observerInvariant_preservation
#print axioms widthOneBP_parity_observerInvariantPreservation
#print axioms no_budgeted_widthOneBP_parity_of_observerInvariant
#print axioms boundedSpace_parity_twoConfig_observerInvariantPreservation
#print axioms no_budgeted_space_parity_of_observerInvariant
#print axioms rung5_concreteObserverBoundaryKernels
#print axioms rung5ObserverBoundaryFrontier

end PallLean.Paper93.DeepMath.PathB
