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

/-- A completed rung-5 observer boundary would consist of preservation theorems
for the frontier models.  The fields are propositions, not data supplied here;
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
#print axioms rung5ObserverBoundaryFrontier

end PallLean.Paper93.DeepMath.PathB
