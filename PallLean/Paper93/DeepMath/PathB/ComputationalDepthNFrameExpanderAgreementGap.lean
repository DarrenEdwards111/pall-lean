import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameExpanderListRecoveryEndpoint

/-!
# Expander local-to-global agreement gap

List recovery is the right higher-order target, but local candidate lists do not
automatically give a small global list.  This file separates those notions.

Each positive cell may attach a list of allowed Boolean values to every
continuation coordinate.  The true label can satisfy all those local lists while
the set of globally compatible labels remains exponential.  In particular, the
universal two-symbol list `{false, true}` has constant local size at every
coordinate but admits all `2^m` labels.

The missing Ramanujan input is therefore an agreement theorem: the expander
constraints must force the number of globally compatible continuation labels to
be polynomial.  Once that agreement bound exists, it constructs the polynomial
cell list decoder from the previous endpoint and yields the same contradiction.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameExpanderAgreementGap

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPObserverSwitchToy
open PallLean.Paper93.DeepMath.PathB.NFrameExpanderListRecoveryEndpoint

/-! ## Local coordinate lists and global compatibility -/

/-- Per-cell, per-coordinate candidate lists.  Every true continuation label is
locally covered, and every local alphabet list has size at most two. -/
structure CoordinateListProfile
    {m : Nat} {Cell : Type} [DecidableEq Cell]
    (cellOf : Assignment m -> Cell) where
  allowed : Cell -> Fin m -> Finset Bool
  covers : forall (a : Assignment m) (i : Fin m),
    a i ∈ allowed (cellOf a) i
  localSize : forall (c : Cell) (i : Fin m),
    (allowed c i).card <= 2

/-- A label is globally compatible with all coordinate lists of one cell. -/
def LocallyCompatible
    {m : Nat} {Cell : Type} [DecidableEq Cell]
    {cellOf : Assignment m -> Cell}
    (P : CoordinateListProfile cellOf)
    (c : Cell) (a : Assignment m) : Prop :=
  forall i : Fin m, a i ∈ P.allowed c i

/-- The complete finite set of labels compatible with a cell's local lists. -/
noncomputable def compatibleLabels
    {m : Nat} {Cell : Type} [DecidableEq Cell]
    {cellOf : Assignment m -> Cell}
    (P : CoordinateListProfile cellOf)
    (c : Cell) : Finset (Assignment m) := by
  classical
  exact (Finset.univ : Finset (Assignment m)).filter
    (fun a => LocallyCompatible P c a)

/-- The actual expander agreement property: every cell has at most `r` globally
compatible labels. -/
def AgreementListBound
    {m : Nat} {Cell : Type} [DecidableEq Cell]
    {cellOf : Assignment m -> Cell}
    (P : CoordinateListProfile cellOf) (r : Nat) : Prop :=
  forall c : Cell, (compatibleLabels P c).card <= r

/-- Local coverage ensures that the true label belongs to its cell's global
compatibility set. -/
theorem trueLabel_mem_compatibleLabels
    {m : Nat} {Cell : Type} [DecidableEq Cell]
    {cellOf : Assignment m -> Cell}
    (P : CoordinateListProfile cellOf) (a : Assignment m) :
    a ∈ compatibleLabels P (cellOf a) := by
  classical
  unfold compatibleLabels
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ a, fun i => P.covers a i⟩

/-- A genuine local-to-global agreement theorem constructs a cell list decoder. -/
noncomputable def listRecoveryOfAgreement
    {m r : Nat} {Cell : Type} [Fintype Cell] [DecidableEq Cell]
    {cellOf : Assignment m -> Cell}
    (P : CoordinateListProfile cellOf)
    (hagreement : AgreementListBound P r) :
    CellListRecovery cellOf r where
  candidates := compatibleLabels P
  covers := trueLabel_mem_compatibleLabels P
  listSize := hagreement

/-! ## Constant local lists have exponential global ambiguity -/

/-- The vacuous local profile allows both Boolean values at every coordinate. -/
def fullCoordinateLists
    {m : Nat} {Cell : Type} [DecidableEq Cell]
    (cellOf : Assignment m -> Cell) : CoordinateListProfile cellOf where
  allowed _ _ := {false, true}
  covers a i := by cases a i <;> simp
  localSize _ _ := by simp

/-- Every assignment is compatible with every cell under the full local profile. -/
theorem compatibleLabels_full_eq_univ
    {m : Nat} {Cell : Type} [DecidableEq Cell]
    (cellOf : Assignment m -> Cell) (c : Cell) :
    compatibleLabels (fullCoordinateLists cellOf) c = Finset.univ := by
  classical
  unfold compatibleLabels
  apply Finset.filter_eq_self.mpr
  intro a _
  unfold LocallyCompatible
  intro i
  cases a i <;> simp [fullCoordinateLists]

/-- Hence each global compatibility list has exact size `2^m`, despite every
coordinate list having size only two. -/
theorem compatibleLabels_full_card
    {m : Nat} {Cell : Type} [DecidableEq Cell]
    (cellOf : Assignment m -> Cell) (c : Cell) :
    (compatibleLabels (fullCoordinateLists cellOf) c).card = 2 ^ m := by
  rw [compatibleLabels_full_eq_univ]
  simp

/-- No agreement bound below the full cube size follows from these uniformly
constant local lists. -/
theorem fullCoordinateLists_not_agreement
    {m r : Nat} {Cell : Type} [Nonempty Cell] [DecidableEq Cell]
    (cellOf : Assignment m -> Cell) (hsmall : r < 2 ^ m) :
    ¬ AgreementListBound (fullCoordinateLists cellOf) r := by
  intro hagreement
  let c : Cell := Classical.choice (inferInstance : Nonempty Cell)
  have hc := hagreement c
  rw [compatibleLabels_full_card cellOf c] at hc
  omega

/-- Concrete local-to-global failure: at dimension four, local lists of size two
exist over a one-cell projection, but no global list bound of four is possible. -/
theorem constantCell_localLists_without_globalList :
    Nonempty (CoordinateListProfile
      (fun _ : Assignment 4 => PUnit.unit)) ∧
    ¬ AgreementListBound
      (fullCoordinateLists (fun _ : Assignment 4 => PUnit.unit)) 4 := by
  refine ⟨⟨fullCoordinateLists _⟩, ?_⟩
  exact fullCoordinateLists_not_agreement _ (by norm_num)

/-! ## Solver-indexed agreement bridge -/

/-- The precise Ramanujan bridge: correctness must turn bounded local lists into
a polynomial bound on globally compatible labels in every positive cell. -/
structure SolverExpanderAgreementFor
    (U : MachineModel) (D : DecisionMachine U) where
  m : Nat
  k : Nat
  d : Nat
  Cell : Type
  cellFintype : Fintype Cell
  cellDecidableEq : DecidableEq Cell
  cellOf : Assignment m -> Cell
  profile : @CoordinateListProfile m Cell cellDecidableEq cellOf
  polyCells : @Fintype.card Cell cellFintype <= m ^ k
  agreement_of_decides : DecidesSAT U D ->
    @AgreementListBound m Cell cellDecidableEq cellOf profile (m ^ d)
  expGap : m ^ (k + d) < 2 ^ m

namespace SolverExpanderAgreementFor

variable {U : MachineModel} {D : DecisionMachine U}

/-- A correctness-derived expander agreement theorem refutes its alleged solver. -/
theorem not_decidesSAT (B : SolverExpanderAgreementFor U D) :
    ¬ DecidesSAT U D := by
  intro hD
  letI : Fintype B.Cell := B.cellFintype
  letI : DecidableEq B.Cell := B.cellDecidableEq
  let L := listRecoveryOfAgreement B.profile (B.agreement_of_decides hD)
  exact no_polynomial_cells_and_listRecovery B.cellOf B.polyCells L B.expGap

end SolverExpanderAgreementFor

/-- Agreement bridges for all certified machines rule out polynomial SAT
decision. -/
theorem no_SATDecisionInP_of_expanderAgreement
    {U : MachineModel}
    (H : forall D : DecisionMachine U,
      Nonempty (SolverExpanderAgreementFor U D)) :
    ¬ SATDecisionInP U := by
  rintro ⟨D, hD⟩
  obtain ⟨B⟩ := H D
  exact B.not_decidesSAT hD

end PallLean.Paper93.DeepMath.PathB.NFrameExpanderAgreementGap

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameExpanderAgreementGap.trueLabel_mem_compatibleLabels
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameExpanderAgreementGap.compatibleLabels_full_card
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameExpanderAgreementGap.constantCell_localLists_without_globalList
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameExpanderAgreementGap.no_SATDecisionInP_of_expanderAgreement
